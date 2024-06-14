use std::{cell::RefCell, rc::Rc};

use crate::{err, eval::Error};

use super::{
    result::{EvalResult, Value},
    Eval,
};

use EvalResult::Return;
use EvalResult::Val;

use Value::Array;
use Value::Fn;
use Value::Int;
use Value::Nil;
use Value::Range;
use Value::Str;

pub fn len(args: &mut [Value]) -> EvalResult {
    if args.len() == 1 {
        if let Str(s) = &args[0] {
            Return(Int(s.len().try_into().unwrap()))
        } else if let Array(a) = &args[0] {
            Return(Int(a.borrow().len().try_into().unwrap()))
        } else {
            err!("len() expected a string argument")
        }
    } else {
        err!("len() expected one argument")
    }
}

pub fn print(args: &mut [Value]) -> EvalResult {
    if args.len() == 1 {
        print!("{}", args[0]);
    }
    Return(Nil)
}

pub fn println(args: &mut [Value]) -> EvalResult {
    if args.len() == 1 {
        println!("{}", args[0]);
    }
    Return(Nil)
}

pub fn push(args: &mut [Value]) -> EvalResult {
    if args.len() == 2 {
        let v = args[1].clone();
        if let Array(ref mut a) = args[0] {
            a.borrow_mut().push(v);
            Val(Nil)
        } else {
            err!("push() expected an array argument")
        }
    } else {
        err!("push() expected one argument")
    }
}
pub fn pop(args: &mut [Value]) -> EvalResult {
    if args.len() == 1 {
        if let Array(ref mut a) = args[0].clone() {
            match a.borrow_mut().pop() {
                Some(v) => Val(v),
                None => Val(Nil),
            }
        } else {
            err!("pop() expected an array argument")
        }
    } else {
        err!("pop() expected one argument")
    }
}

pub fn first(args: &mut [Value]) -> EvalResult {
    if args.len() == 1 {
        if let Array(ref mut a) = args[0].clone() {
            match a.borrow_mut().first() {
                Some(v) => Val(v.clone()),
                None => Val(Nil),
            }
        } else {
            err!("first() expected an array argument")
        }
    } else {
        err!("first() expected one argument")
    }
}

pub fn last(args: &mut [Value]) -> EvalResult {
    if args.len() == 1 {
        if let Array(ref mut a) = args[0].clone() {
            match a.borrow_mut().last() {
                Some(v) => Val(v.clone()),
                None => Val(Nil),
            }
        } else {
            err!("last() expected an array argument")
        }
    } else {
        err!("last() expected one argument")
    }
}

pub fn tail(args: &mut [Value]) -> EvalResult {
    if args.len() == 1 {
        if let Array(ref mut a) = args[0].clone() {
            match a.borrow_mut().split_first() {
                Some((_, tail)) => Val(Array(Rc::from(RefCell::new(tail.to_vec())))),
                None => Val(Nil),
            }
        } else {
            err!("tail() expected an array argument")
        }
    } else {
        err!("tail() expected one argument")
    }
}

pub fn foreach(args: &mut [Value]) -> EvalResult {
    if args.len() == 2 {
        if let Fn(f, ast, fnenv) = &args[1] {
            match &args[0] {
                Range(lower, upper) => {
                    for i in *lower..=*upper {
                        Eval::call(f, fnenv.clone(), ast.clone(), &[Int(i)]);
                    }
                    Val(Nil)
                }
                Value::Array(arr) => {
                    for i in arr.borrow().iter() {
                        Eval::call(f, fnenv.clone(), ast.clone(), &[i.clone()]);
                    }
                    Val(Nil)
                }
                Value::Map(map) => {
                    map.borrow().iter().for_each(|(k, v)| {
                        Eval::call(f, fnenv.clone(), ast.clone(), &[k.into(), v.clone()]);
                    });
                    Val(Nil)
                }
                _ => todo!(),
            }
        } else {
            todo!()
        }
    } else {
        err!("foreach() expected two arguments")
    }
}
pub fn map(args: &mut [Value]) -> EvalResult {
    if args.len() == 2 {
        if let Fn(f, ast, fnenv) = &args[1] {
            let v: Vec<Value> = match &args[0] {
                Range(lower, upper) => (*lower..=*upper)
                    .map(
                        |i| match Eval::call(f, fnenv.clone(), ast.clone(), &[Int(i)]) {
                            Val(val) | Return(val) => val,
                            EvalResult::Err(_) => todo!(),
                        },
                    )
                    .collect(),
                Value::Array(arr) => arr
                    .borrow()
                    .iter()
                    .map(
                        |item| match Eval::call(f, fnenv.clone(), ast.clone(), &[item.clone()]) {
                            Val(val) | Return(val) => val,
                            EvalResult::Err(_) => todo!(),
                        },
                    )
                    .collect(),
                Value::Map(_) => {
                    todo!()
                }
                _ => todo!(),
            };
            Val(Array(Rc::from(RefCell::new(v))))
        } else {
            todo!()
        }
    } else {
        err!("foreach() expected two arguments")
    }
}
