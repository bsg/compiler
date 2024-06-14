// TODO logical and/or should short circuit

mod builtin;
mod env;
mod error;
mod result;

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    ast::{BlockExpression, CallExpression, FnExpression, NodeKind, NodeRef, Op, RangeExpression},
    err,
    parser::Parser,
};

use self::{
    env::{Env, EnvRef},
    error::Error,
    result::{BuiltInFn, EvalResult, MapKey, Value},
};

pub struct Eval {
    env: EnvRef,
}

use EvalResult::Err;
use EvalResult::Return;
use EvalResult::Val;

use Value::Array;
use Value::Bool;
use Value::BuiltIn;
use Value::Fn;
use Value::Int;
use Value::Map;
use Value::Nil;
use Value::Pair;
use Value::Range;
use Value::Str;

impl Eval {
    pub fn new() -> Eval {
        let builtins = Env::new(); // TODO construct this somewhere else

        let fns: &[(&str, BuiltInFn)] = &[
            ("len", builtin::len),
            ("print", builtin::print),
            ("println", builtin::println),
            ("push", builtin::push),
            ("pop", builtin::pop),
            ("first", builtin::first),
            ("last", builtin::last),
            ("tail", builtin::tail),
            ("foreach", builtin::foreach),
            ("map", builtin::map),
        ];

        for (fn_name, fn_ref) in fns {
            builtins
                .borrow_mut()
                .bind_local(Rc::from(*fn_name), BuiltIn(*fn_ref));
        }

        Eval {
            env: Env::from(builtins),
        }
    }

    #[inline(always)]
    fn eval_infix(op: &Op, lhs: &EvalResult, rhs: &EvalResult) -> EvalResult {
        match (lhs, rhs) {
            (Val(lhs) | Return(lhs), Val(rhs) | Return(rhs)) => match (op, lhs, rhs) {
                (Op::Assign, ..) => unreachable!(),
                (Op::Eq, lhs, rhs) => Val(Bool(lhs == rhs)),
                (Op::NotEq, lhs, rhs) => Val(Bool(lhs != rhs)),
                (Op::Add, Int(a), Int(b)) => Val(Int(a + b)),
                (Op::Sub, Int(a), Int(b)) => Val(Int(a - b)),
                (Op::Mul, Int(a), Int(b)) => Val(Int(a * b)),
                (Op::Div, Int(a), Int(b)) => Val(Int(a / b)),
                (Op::Mod, Int(a), Int(b)) => Val(Int(a % b)),
                (Op::Lt, Int(a), Int(b)) => Val(Bool(a < b)),
                (Op::Gt, Int(a), Int(b)) => Val(Bool(a > b)),
                (Op::Le, Int(a), Int(b)) => Val(Bool(a <= b)),
                (Op::Ge, Int(a), Int(b)) => Val(Bool(a >= b)),
                (Op::And, Bool(a), Bool(b)) => Val(Bool(*a && *b)),
                (Op::Or, Bool(a), Bool(b)) => Val(Bool(*a || *b)),
                (Op::Add, Str(a), Str(b)) => {
                    let mut s = a.to_string();
                    s.push_str(b);
                    Val(Str(Rc::from(s.as_str())))
                }
                (_, lhs, rhs) => err!(
                    "unknown operator {} {} {}",
                    lhs.type_str(),
                    op,
                    rhs.type_str()
                ),
            },
            _ => unreachable!(),
        }
    }

    #[inline(always)]
    fn eval_prefix(op: &Op, rhs: &Value) -> EvalResult {
        match op {
            Op::Neg => match rhs {
                Int(i) => Val(Int(-i)),
                _ => err!("unknown operator {}{}", op, rhs.type_str()),
            },
            Op::Not => match rhs {
                Bool(b) => Val(Bool(!b)),
                _ => err!("unknown operator {}{}", op, rhs.type_str()),
            },
            _ => unreachable!(),
        }
    }

    #[inline(always)]
    fn eval_block(env: EnvRef, block: &BlockExpression) -> EvalResult {
        let mut rv = Val(Nil);

        match block.statements.first() {
            Some(node) => match &node.kind {
                NodeKind::Pair(_) => {
                    let mut map: HashMap<MapKey, Value> = HashMap::new();
                    for stmt in block.statements.iter().cloned() {
                        match Self::eval_ast(env.clone(), stmt) {
                            Val(Pair(key, value)) => {
                                map.insert(key, Rc::into_inner(value).unwrap());
                            }
                            err @ Err(_) => return err,
                            _ => todo!(),
                        }
                    }
                    return Val(Map(Rc::from(RefCell::new(map))));
                }
                _ => {
                    let new_env = Env::from(env);
                    for stmt in block.statements.iter().cloned() {
                        match Self::eval_ast(new_env.clone(), stmt) {
                            val @ Val(_) => {
                                rv = val;
                            }
                            val @ Return(_) => return val,
                            err @ Err(_) => return err,
                        }
                    }
                }
            },
            _ => todo!(),
        }

        rv
    }

    #[inline(always)]
    fn eval_assign(env: EnvRef, lvalue: NodeRef, rvalue: NodeRef, is_let: bool) -> EvalResult {
        match &lvalue.kind {
            NodeKind::Ident(name) => {
                match Self::eval_ast(env.clone(), rvalue) {
                    Val(val) => {
                        if is_let {
                            env.borrow_mut().bind_local(name.clone(), val);
                        } else {
                            env.borrow_mut().bind(name.clone(), val);
                        }
                        Val(Nil) // TODO return without value
                    }
                    err @ Err(_) => err,
                    _ => todo!(),
                }
            }
            NodeKind::Index(idx) => {
                if let Val(rval) = Self::eval_ast(env.clone(), rvalue) {
                    match env.borrow().get(&idx.ident) {
                        Some(Array(arr)) => {
                            let i = match Self::eval_ast(env.clone(), idx.index.clone()) {
                                Val(Int(i)) => i,
                                Err(_) => todo!(),
                                _ => todo!(),
                            };
                            arr.borrow_mut()[i as usize] = rval;
                            Val(Nil)
                        }
                        Some(Map(map)) => {
                            let key = match Self::eval_ast(env.clone(), idx.index.clone()) {
                                Val(Int(key)) | Return(Int(key)) => MapKey::Int(key),
                                Val(Bool(key)) | Return(Bool(key)) => MapKey::Bool(key),
                                Val(Str(key)) | Return(Str(key)) => MapKey::Str(key),
                                Err(_) => todo!(),
                                _ => todo!(),
                            };
                            map.borrow_mut().insert(key, rval);
                            Val(Nil)
                        }
                        None => todo!(),
                        _ => todo!(),
                    }
                } else {
                    todo!()
                }
            }
            _ => todo!(),
        }
    }

    #[inline(always)]
    fn eval_call(env: EnvRef, call: &CallExpression) -> EvalResult {
        match env.borrow().get(&call.ident) {
            Some(Fn(func, ast, fnenv)) => {
                let fnenv = Env::from(fnenv);
                if func.args.len() != call.args.len() {
                    return err!(
                        "function {} expects {} arguments",
                        call.ident,
                        func.args.len()
                    );
                }

                for (name, arg) in func.args.iter().zip(call.args.iter()) {
                    match Self::eval_ast(env.clone(), arg.clone()) {
                        Val(val) | Return(val) => {
                            fnenv.borrow_mut().bind_local(name.clone(), val);
                        }
                        err @ Err(_) => return err,
                    }
                }
                match Self::eval_ast(fnenv, ast) {
                    Val(rv) | Return(rv) => Val(rv),
                    err @ Err(_) => err,
                }
            }
            Some(BuiltIn(f)) => {
                let mut args: Vec<Value> = Vec::new();
                for arg in call.args.iter() {
                    match Self::eval_ast(env.clone(), arg.clone()) {
                        Val(val) | Return(val) => args.push(val),
                        err @ Err(_) => return err,
                    }
                }
                match f(&mut args) {
                    Val(rv) | Return(rv) => Val(rv),
                    Err(_) => todo!(),
                }
            }
            _ => todo!(),
        }
    }

    #[inline(always)]
    fn call(func: &FnExpression, env: EnvRef, ast: NodeRef, args: &[Value]) -> EvalResult {
        assert_eq!(func.args.len(), args.len());

        {
            let mut env = env.borrow_mut();
            for (name, arg) in func.args.iter().zip(args.iter()) {
                env.bind_local(name.clone(), arg.clone());
            }
        }

        match Self::eval_ast(env, ast) {
            Val(rv) | Return(rv) => Val(rv),
            Err(_) => todo!(),
        }
    }

    #[inline(always)]
    fn eval_range(env: EnvRef, range: &RangeExpression, is_inclusive: bool) -> EvalResult {
        if let Val(Int(lower)) = Self::eval_ast(env.clone(), range.lower.clone()) {
            if let Val(Int(upper)) = Self::eval_ast(env, range.upper.clone()) {
                Val(Range(lower, if is_inclusive { upper } else { upper - 1 }))
            } else {
                todo!()
            }
        } else {
            todo!()
        }
    }

    fn eval_ast(env: EnvRef, node: NodeRef) -> EvalResult {
        let lhs = node.left.as_ref().cloned();
        let rhs = node.right.as_ref().cloned();

        match node.kind.clone() {
            NodeKind::Ident(name) => match env.borrow().get(&name) {
                Some(val) => Val(val),
                None => err!("Unknown ident {}", name),
            },
            NodeKind::Int(i) => Val(Int(i)),
            NodeKind::Bool(b) => Val(Bool(b)),
            NodeKind::Str(b) => Val(Str(b)),
            NodeKind::PrefixOp(op) => match Self::eval_ast(env, rhs.unwrap()) {
                err @ Err(_) => err,
                Val(val) | Return(val) => Self::eval_prefix(&op, &val),
            },
            NodeKind::InfixOp(op) => match op {
                Op::Assign => Self::eval_assign(env, lhs.unwrap(), rhs.unwrap(), false),
                _ => {
                    match (
                        Self::eval_ast(env.clone(), lhs.unwrap()),
                        Self::eval_ast(env.clone(), rhs.unwrap()),
                    ) {
                        p @ (Err(_), _) => p.0,
                        p @ (_, Err(_)) => p.1,
                        (lhs, rhs) => Self::eval_infix(&op, &lhs, &rhs),
                    }
                }
            },
            NodeKind::Let => Self::eval_assign(env, lhs.unwrap(), rhs.unwrap(), true),

            NodeKind::Return => match Self::eval_ast(env, rhs.unwrap()) {
                Val(val) | Return(val) => Return(val),
                err @ Err(_) => err,
            },
            NodeKind::If(if_expr) => {
                match Self::eval_ast(env.clone(), if_expr.condition.to_owned()) {
                    Val(val) | Return(val) => match val {
                        Bool(cond) => {
                            if cond {
                                Self::eval_ast(env, lhs.unwrap())
                            } else if let Some(node) = rhs {
                                Self::eval_ast(env, node)
                            } else {
                                EvalResult::Val(Nil)
                            }
                        }
                        Nil => err!("expected condition after if"),
                        _ => Self::eval_ast(env, lhs.unwrap()),
                    },
                    err @ Err(_) => err,
                }
            }
            NodeKind::Block(block) => Self::eval_block(env, &block),
            NodeKind::Fn(func) => Val(Fn(func, rhs.unwrap(), Env::from(env))),
            NodeKind::Call(call) => Self::eval_call(env, &call),
            NodeKind::Array(nodes) => {
                let mut arr: Vec<Value> = Vec::new();
                nodes
                    .iter()
                    .for_each(|node| match Self::eval_ast(env.clone(), node.clone()) {
                        Val(value) | Return(value) => {
                            arr.push(value);
                        }
                        Err(_) => todo!(),
                    });
                Val(Array(Rc::from(RefCell::new(arr))))
            }
            NodeKind::Index(idx) => match env.borrow().get(&idx.ident) {
                Some(Array(arr)) => {
                    let i = match Self::eval_ast(env.clone(), idx.index) {
                        Val(Int(i)) | Return(Int(i)) => i,
                        Err(_) => todo!(),
                        _ => todo!(),
                    };
                    Val(arr.borrow()[i as usize].clone())
                }
                Some(Map(map)) => {
                    let key = match Self::eval_ast(env.clone(), idx.index) {
                        Val(Int(key)) | Return(Int(key)) => MapKey::Int(key),
                        Val(Bool(key)) | Return(Bool(key)) => MapKey::Bool(key),
                        Val(Str(key)) | Return(Str(key)) => MapKey::Str(key),
                        Err(_) => todo!(),
                        _ => todo!(),
                    };
                    if let Some(val) = map.borrow().get(&key) {
                        Val(val.clone())
                    } else {
                        Val(Nil)
                    }
                }
                None => todo!(),
                _ => todo!(),
            },
            NodeKind::Pair(pair) => {
                let key = match Self::eval_ast(env.clone(), pair.key) {
                    Val(Int(key)) | Return(Int(key)) => MapKey::Int(key),
                    Val(Bool(key)) | Return(Bool(key)) => MapKey::Bool(key),
                    Val(Str(key)) | Return(Str(key)) => MapKey::Str(key),
                    Err(_) => todo!(),
                    _ => todo!(),
                };
                let value = match Self::eval_ast(env.clone(), pair.value) {
                    Val(val) | Return(val) => val,
                    Err(_) => todo!(),
                };
                Val(Pair(key, Rc::from(value)))
            }
            NodeKind::Range(range) => Self::eval_range(env, &range, false),
            NodeKind::RangeInclusive(range) => Self::eval_range(env, &range, true),
        }
    }

    pub fn eval(&self, code: &str) -> EvalResult {
        let mut last_result = Val(Nil);
        let mut parser = Parser::new(code);

        loop {
            let node = parser.parse_statement();
            if let Some(node) = node {
                last_result = Self::eval_ast(self.env.clone(), node);
            } else {
                break;
            }
        }

        last_result
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::eval::result::MapKey;

    use super::*;

    macro_rules! assert_eval_stmt {
        ($input:expr, $expected:expr) => {
            let eval = Eval::new();
            assert_eq!(eval.eval($input.into()), $expected);
        };
    }

    #[test]
    fn nil() {
        assert_eval_stmt!("", Val(Nil));
    }

    #[test]
    fn int_literal() {
        assert_eval_stmt!("5", Val(Int(5)));
    }

    #[test]
    fn bool_literal() {
        assert_eval_stmt!("false", Val(Bool(false)));
    }

    #[test]
    fn numerical() {
        assert_eval_stmt!("5 + -10 * 2", Val(Int(-15)));
    }

    #[test]
    fn neg() {
        assert_eval_stmt!("-5", Val(Int(-5)));
    }

    #[test]
    fn not() {
        assert_eval_stmt!("!false", Val(Bool(true)));
    }

    #[test]
    fn int_comparison() {
        assert_eval_stmt!("1 > 5", Val(Bool(false)));
    }

    #[test]
    fn equal_int_int() {
        assert_eval_stmt!("1 == 1", Val(Bool(true)));
        assert_eval_stmt!("1 == 2", Val(Bool(false)));
    }

    #[test]
    fn not_equal_int_int() {
        assert_eval_stmt!("1 != 2", Val(Bool(true)));
        assert_eval_stmt!("2 != 2", Val(Bool(false)));
    }

    #[test]
    fn equal_bool_bool() {
        assert_eval_stmt!("true == true", Val(Bool(true)));
        assert_eval_stmt!("true == false", Val(Bool(false)));
    }

    #[test]
    fn not_equal_bool_bool() {
        assert_eval_stmt!("true != false", Val(Bool(true)));
        assert_eval_stmt!("true != true", Val(Bool(false)));
    }

    #[test]
    fn block_single_statement() {
        assert_eval_stmt!("{1}", Val(Int(1)));
    }

    #[test]
    fn block_multi_statement() {
        assert_eval_stmt!("{1;2;3}", Val(Int(3)));
    }

    #[test]
    fn block_with_early_return() {
        assert_eval_stmt!("{1;return 2;3}", Return(Int(2)));
    }

    #[test]
    fn if_statement() {
        assert_eval_stmt!("if (1 < 2) {1} {2}", Val(Int(1)));
    }

    #[test]
    fn eval_block_with_let() {
        assert_eval_stmt!("{let x = 1; x}", Val(Int(1)));
    }

    #[test]
    fn fn_call() {
        let ctx = Eval::new();

        let code = "
            let f = fn(x){x * x};
            f(2);
        ";
        assert_eq!(ctx.eval(code), Val(Int(4)));

        let code = "
            let g = fn(x, y){x * y}
            g(2, 10);
        ";
        assert_eq!(ctx.eval(code), Val(Int(20)));
        assert_eq!(ctx.eval("f(g(2, 10));"), Val(Int(400)));
    }

    #[test]
    fn nested_scopes() {
        let code = "
            {
                let x = 1;
                {
                    let y = 2;
                    {
                        x + y;
                    }
                }
            }
        ";
        let ctx = Eval::new();
        assert_eq!(ctx.eval(code), Val(Int(3)));
    }

    #[test]
    fn fn_scope() {
        let ctx = Eval::new();
        let code = "
            let x = 1;
            let f = fn(){x = 2};
        ";
        ctx.eval(code);
        assert_eq!(ctx.eval("x"), Val(Int(1)));
        ctx.eval("f()");
        assert_eq!(ctx.eval("x"), Val(Int(2)));
    }

    #[test]
    fn closure() {
        let code = "
            let newAdder = fn(x) {
                fn(y) { x + y };
            };
            let addTwo = newAdder(2);
            addTwo(2);
        ";
        assert_eq!(Eval::new().eval(code), Val(Int(4)));
    }

    #[test]
    fn functions_as_arguments() {
        let code = "
            let add = fn(a, b) { a + b };
            let sub = fn(a, b) { a - b };
            let applyFunc = fn(a, b, func) { func(a, b) };
        ";
        let ctx = Eval::new();
        ctx.eval(code);
        assert_eq!(ctx.eval("applyFunc(2, 2, add);"), Val(Int(4)));
        assert_eq!(ctx.eval("applyFunc(4, 2, sub);"), Val(Int(2)));
    }

    #[test]
    fn function_literals() {
        let code = "
            let applyFunc = fn(a, b, func) { func(a, b) };
        ";
        let ctx = Eval::new();
        ctx.eval(code);
        assert_eq!(
            ctx.eval("applyFunc(2, 2, fn(a, b) { a + b });"),
            Val(Int(4))
        );
    }

    #[test]
    fn fibonacci() {
        let code = "
            let fibonacci = fn(n) {
                println(n);
                if(n == 0) { return 0 }
                if(n == 1) { return 1 }
                if(n > 1) { fibonacci(n - 1) + fibonacci(n - 2) }
            }
        ";
        let ctx = Eval::new();
        ctx.eval(code);
        assert_eq!(ctx.eval("fibonacci(0)"), Val(Int(0)));
        assert_eq!(ctx.eval("fibonacci(1)"), Val(Int(1)));
        assert_eq!(ctx.eval("fibonacci(2)"), Val(Int(1)));
        assert_eq!(ctx.eval("fibonacci(3)"), Val(Int(2)));
        assert_eq!(ctx.eval("fibonacci(4)"), Val(Int(3)));
    }

    #[test]
    fn fizzbuzz1() {
        let code = r#"
            let fizzbuzz = fn(n) {
                if(n % 3 == 0 && n % 5 == 0) {
                    return "fizzbuzz";
                } else {
                    if(n % 3 == 0) {
                        return "fizz";
                    } else {
                        if(n % 5 == 0) {
                            return "buzz";
                        }   
                    }
                }
                
            }
        "#;
        let ctx = Eval::new();
        ctx.eval(code);
        assert_eq!(ctx.eval("fizzbuzz(15)"), Val(Str("fizzbuzz".into())));
        assert_eq!(ctx.eval("fizzbuzz(3)"), Val(Str("fizz".into())));
        assert_eq!(ctx.eval("fizzbuzz(5)"), Val(Str("buzz".into())));
    }

    #[test]
    fn fizzbuzz2() {
        let code = r#"
            let fizzbuzz = fn(n) {
                if(n % 3 == 0 && n % 5 == 0) {
                    return "fizzbuzz";
                }
                if(n % 3 == 0) {
                    return "fizz";
                }
                if(n % 5 == 0) {
                    return "buzz";
                } 
            }
        "#;
        let ctx = Eval::new();
        ctx.eval(code);
        assert_eq!(ctx.eval("fizzbuzz(15)"), Val(Str("fizzbuzz".into())));
        assert_eq!(ctx.eval("fizzbuzz(3)"), Val(Str("fizz".into())));
        assert_eq!(ctx.eval("fizzbuzz(5)"), Val(Str("buzz".into())));
    }

    #[test]
    fn fizzbuzz3() {
        let code = r#"
            let fizzbuzz = fn(n) {
                let s = "";
                if(n % 3 == 0) {
                    s = s + "fizz";
                }
                if(n % 5 == 0) {
                    s = s + "buzz";
                }
                return s;
            }
        "#;
        let ctx = Eval::new();
        ctx.eval(code);
        assert_eq!(ctx.eval("fizzbuzz(15)"), Val(Str("fizzbuzz".into())));
        assert_eq!(ctx.eval("fizzbuzz(3)"), Val(Str("fizz".into())));
        assert_eq!(ctx.eval("fizzbuzz(5)"), Val(Str("buzz".into())));
    }

    #[test]
    fn fizzbuzz4() {
        let code = r#"
            let fizzbuzz = fn(n) {
                if(n % 3 == 0){"fizz"}{""} + if(n % 5 == 0){"buzz"}{""}
            }
        "#;
        let ctx = Eval::new();
        ctx.eval(code);
        assert_eq!(ctx.eval("fizzbuzz(15)"), Val(Str("fizzbuzz".into())));
        assert_eq!(ctx.eval("fizzbuzz(3)"), Val(Str("fizz".into())));
        assert_eq!(ctx.eval("fizzbuzz(5)"), Val(Str("buzz".into())));
    }

    #[test]
    fn string_len() {
        assert_eq!(Eval::new().eval(r#"len("asdfg")"#), Val(Int(5)));
    }

    #[test]
    fn eval_array() {
        let code = r#"
            [1, 2, false]
        "#;
        assert_eq!(
            Eval::new().eval(code),
            Val(Array(Rc::from(RefCell::new(vec!(
                Int(1),
                Int(2),
                Bool(false)
            )))))
        );
    }

    #[test]
    fn eval_array_index() {
        let code = r#"
            let a = [1, if(false){2}{5}, 3];
            a[0] + a[1]
        "#;
        assert_eq!(Eval::new().eval(code), Val(Int(6)));

        let code = r#"
            let a = [1, if(false){2}{5}, 3];
            a[1] = 4;
            a
        "#;
        assert_eq!(
            Eval::new().eval(code),
            Val(Array(Rc::from(RefCell::new(vec![Int(1), Int(4), Int(3)]))))
        );
    }

    #[test]
    fn array_len() {
        let code = r#"
            let a = [1, 2, 3 ,4];
            len(a)
        "#;
        assert_eq!(Eval::new().eval(code), Val(Int(4)));
    }

    #[test]
    fn array_push_pop() {
        let code = r#"
            let a = [1, 2, 3, 4];
        "#;
        let ctx = Eval::new();
        ctx.eval(code);
        assert_eq!(ctx.eval("len(a)"), Val(Int(4)));
        ctx.eval("push(a, 5)");
        assert_eq!(ctx.eval("len(a)"), Val(Int(5)));
        assert_eq!(ctx.eval("pop(a)"), Val(Int(5)));
        assert_eq!(ctx.eval("len(a)"), Val(Int(4)));
    }

    #[test]
    fn array_first_last_tail() {
        let code = r#"
            let a = [1, 2, 3, 4];
        "#;
        let ctx = Eval::new();
        ctx.eval(code);
        assert_eq!(ctx.eval("first(a)"), Val(Int(1)));
        assert_eq!(ctx.eval("last(a)"), Val(Int(4)));
        assert_eq!(
            ctx.eval("tail(a)"),
            Val(Array(Rc::from(RefCell::new(vec![Int(2), Int(3), Int(4)]))))
        );
    }

    #[test]
    fn eval_map_literal() {
        let mut map: HashMap<MapKey, Value> = HashMap::new();
        map.insert(MapKey::Str(Rc::from("a")), Int(1));
        map.insert(MapKey::Str(Rc::from("b")), Int(2));
        assert_eq!(
            Eval::new().eval(r#"{"a": 1, "b": 2}"#),
            Val(Map(Rc::from(RefCell::new(map))))
        );
    }

    #[test]
    fn eval_map_index() {
        let code = r#"
            let map = {"a": 1};
        "#;
        let ctx = Eval::new();
        ctx.eval(code);
        assert_eq!(ctx.eval(r#"map["a"]"#), Val(Int(1)));
        ctx.eval(r#"map["a"]=2"#);
        assert_eq!(ctx.eval(r#"map["a"]"#), Val(Int(2)));
    }

    #[test]
    fn eval_range() {
        assert_eq!(Eval::new().eval(r#"{0..10}"#), Val(Range(0, 9)));

        assert_eq!(Eval::new().eval(r#"{0..=10}"#), Val(Range(0, 10)));
    }

    #[test]
    fn eval_foreach_range() {
        let code = r#"
            let i = 0;
            foreach(1..4, fn(n){i = i + n})
            i
        "#;
        assert_eq!(Eval::new().eval(code), Val(Int(6)));

        let code = r#"
            let i = 0;
            foreach(1..=4, fn(n){i = i + n})
            i
        "#;
        assert_eq!(Eval::new().eval(code), Val(Int(10)));
    }

    #[test]
    fn eval_foreach_array() {
        let code = r#"
            let i = 0;
            foreach([1, 2, 3, 4], fn(n){i = i + n})
            i
        "#;
        assert_eq!(Eval::new().eval(code), Val(Int(10)));
    }

    #[test]
    fn eval_foreach_map() {
        let code = r#"
            let i = 0;
            foreach({1: 2, 3: 4}, fn(k, v){i = i + k + v})
            i
        "#;
        assert_eq!(Eval::new().eval(code), Val(Int(10)));
    }

    #[test]
    fn eval_map_array() {
        let code = r#"
            let arr = [1, 2, 3, 4];
            map(arr, fn(n){n * n})
        "#;
        assert_eq!(
            Eval::new().eval(code),
            Val(Array(Rc::from(RefCell::new(vec![
                Int(1),
                Int(4),
                Int(9),
                Int(16)
            ]))))
        );
    }

    #[test]
    fn eval_map_range() {
        let code = r#"
            map(1..=4, fn(n){n * n})
        "#;
        assert_eq!(
            Eval::new().eval(code),
            Val(Array(Rc::from(RefCell::new(vec![
                Int(1),
                Int(4),
                Int(9),
                Int(16)
            ]))))
        );
    }
}
