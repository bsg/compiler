// TODO we need a ParseResult -- do we? why not just panic?

use std::iter::Peekable;
use std::rc::Rc;

use crate::ast::*;
use crate::lexer::{Lexer, Token, Tokens};

pub struct Parser {
    tokens: Peekable<Tokens>,
    curr_token: Token,
    peek_token: Token,
}

macro_rules! node {
    ($kind:expr, $left:expr, $right:expr) => {
        Rc::new(Node {
            kind: $kind,
            left: $left,
            right: $right,
        })
    };
}

impl Parser {
    pub fn new(input: &str) -> Parser {
        Parser {
            tokens: Lexer::new(input).tokens().peekable(),
            curr_token: Token::None,
            peek_token: Token::None,
        }
    }

    // FIXME FUCKING FIX THE NEXT/PEEK SITUATION
    fn next_token(&mut self) {
        self.curr_token = self.tokens.next().unwrap_or(Token::None);
        self.peek_token = self.tokens.peek().cloned().unwrap_or(Token::None);
    }

    fn parse_block(&mut self) -> Option<NodeRef> {
        assert_eq!(self.curr_token, Token::LBrace);

        let mut statements: Vec<NodeRef> = Vec::new();

        match self.curr_token {
            Token::LBrace => {
                while let Some(stmt) = self.parse_statement().as_ref() {
                    statements.push(stmt.clone());
                }

                Some(node!(
                    NodeInner::Block(BlockStmt {
                        statements: Rc::from(statements.as_slice())
                    }),
                    None,
                    None
                ))
            }
            _ => todo!(),
        }
    }

    /// caller must ensure current token is If
    fn parse_if(&mut self) -> Option<NodeRef> {
        assert_eq!(self.curr_token, Token::If);
        assert_eq!(self.peek_token, Token::LParen);
        self.next_token();

        match self.parse_expression(0) {
            Some(cond) => {
                assert_eq!(self.peek_token, Token::RParen);
                self.next_token();

                assert_eq!(self.peek_token, Token::LBrace);
                self.next_token();
                let lhs = self.parse_block();

                // eat 'else' if there is one
                if self.peek_token == Token::Else {
                    self.next_token();
                    assert_eq!(self.peek_token, Token::LBrace);
                }

                let rhs = if self.peek_token == Token::LBrace {
                    self.next_token();
                    self.parse_block()
                } else {
                    None
                };

                match lhs {
                    Some(_) => Some(node!(NodeInner::If(IfStmt { condition: cond }), lhs, rhs)),
                    None => todo!(),
                }
            }
            None => todo!(),
        }
    }

    // caller must ensure current token is Fn
    fn parse_fn(&mut self) -> Option<NodeRef> {
        let mut args: Vec<(Rc<str>, Rc<str>)> = Vec::new();

        assert_eq!(self.curr_token, Token::Fn);
        self.next_token();

        if let Token::Ident(ident) = &self.curr_token.clone() {
            self.next_token();
            assert_eq!(self.curr_token, Token::LParen);
            self.next_token();

            loop {
                match &self.curr_token.clone() {
                    Token::Ident(arg_ident) => {
                        self.next_token();
                        assert_eq!(self.curr_token, Token::Colon);
                        self.next_token();

                        if let Token::Ident(ty_ident) = &self.curr_token {
                            args.push((arg_ident.clone(), ty_ident.clone()))
                        } else {
                            todo!()
                        }
                    }
                    Token::Comma => (),
                    _ => break,
                }
                self.next_token();
            }

            self.next_token();
            assert_eq!(self.curr_token, Token::Arrow);
            self.next_token();

            let return_type = match self.curr_token.clone() {
                Token::Ident(ret_ident) => ret_ident,
                _ => todo!(),
            };
            self.next_token();

            assert_eq!(self.curr_token, Token::LBrace);

            let body = self.parse_block()?;

            Some(node!(
                NodeInner::Fn(FnStmt {
                    ident: ident.clone(),
                    args: Rc::from(args.as_slice()),
                    ret_ty: return_type.clone()
                }),
                None,
                Some(body)
            ))
        } else {
            todo!()
        }
    }

    fn parse_call(&mut self, lhs: NodeRef) -> Option<NodeRef> {
        let mut args: Vec<NodeRef> = Vec::new();

        let ident = match &lhs.kind {
            NodeInner::Ident(id) => id.clone(),
            _ => todo!(),
        };

        self.next_token();
        if self.peek_token != Token::RParen {
            while let Some(node) = self.parse_expression(0) {
                args.push(node);
                match self.peek_token {
                    Token::Comma => {
                        self.next_token();
                    }
                    _ => break,
                }
            }
        }

        assert_eq!(self.peek_token, Token::RParen);
        self.next_token();

        Some(node!(
            NodeInner::Call(CallStmt {
                ident,
                args: Rc::from(args.as_slice())
            }),
            None,
            None
        ))
    }

    fn parse_array(&mut self) -> Option<NodeRef> {
        assert_eq!(self.curr_token, Token::LBracket);

        let mut arr: Vec<Rc<Node>> = Vec::new();

        if self.peek_token != Token::RBracket {
            while let Some(node) = self.parse_expression(0) {
                arr.push(node.clone());
                match self.peek_token {
                    Token::Comma => self.next_token(),
                    _ => break,
                }
            }
        }
        assert_eq!(self.peek_token, Token::RBracket);
        self.next_token();

        Some(node!(NodeInner::Array(arr), None, None))
    }

    fn parse_index(&mut self, lhs: NodeRef) -> Option<NodeRef> {
        assert_eq!(self.peek_token, Token::LBracket);

        let ident = match &lhs.kind {
            NodeInner::Ident(id) => id.clone(),
            _ => todo!(),
        };
        self.next_token();

        let index = self.parse_expression(0)?;
        assert_eq!(self.peek_token, Token::RBracket);
        self.next_token();

        Some(node!(
            NodeInner::Index(IndexStmt { ident, index }),
            None,
            None
        ))
    }

    fn parse_pair(&mut self, key: NodeRef) -> Option<NodeRef> {
        assert_eq!(self.peek_token, Token::Colon);
        self.next_token();
        let value = self.parse_expression(0)?;

        if self.peek_token == Token::Comma {
            self.next_token();
        }

        Some(node!(NodeInner::Pair(PairStmt { key, value }), None, None))
    }

    pub fn parse_statement(&mut self) -> Option<NodeRef> {
        let node = match self.tokens.peek() {
            Some(Token::Let) => {
                self.next_token();
                self.next_token(); // eat 'let'

                let lhs = self.parse_ident();
                self.next_token();
                assert_eq!(self.curr_token, Token::Colon);
                self.next_token();
                if let Token::Ident(ty) = self.curr_token.clone() {
                    self.next_token();
                    match self.curr_token {
                        Token::Assign => Some(node!(
                            NodeInner::Let(LetStmt { ty }),
                            lhs,
                            self.parse_expression(0)
                        )),
                        _ => todo!(),
                    }
                } else {
                    panic!()
                }
            }
            Some(Token::Return) => {
                self.next_token();
                Some(node!(NodeInner::Return, None, self.parse_expression(0)))
            }
            Some(_) => self.parse_expression(0),
            None => return None,
        };

        if self.peek_token == Token::Semicolon {
            self.next_token();
        }

        node
    }

    fn parse_ident(&self) -> Option<NodeRef> {
        match &self.curr_token {
            Token::Ident(name) => Some(node!(NodeInner::Ident(name.clone()), None, None)),
            _ => todo!(),
        }
    }

    pub fn parse_expression(&mut self, precedence: i32) -> Option<NodeRef> {
        self.next_token();
        let mut lhs = match &self.curr_token {
            Token::Int(s) => {
                let i = match s.parse() {
                    Ok(i) => i,
                    Err(_) => todo!(),
                };

                node!(NodeInner::Int(i), None, None)
            }
            Token::Str(s) => node!(NodeInner::Str(s.clone()), None, None),
            Token::Ident(_) => self.parse_ident()?,
            Token::True => node!(NodeInner::Bool(true), None, None),
            Token::False => node!(NodeInner::Bool(false), None, None),
            Token::Minus => {
                node!(NodeInner::PrefixOp(Op::Neg), None, self.parse_expression(0))
            }
            Token::Bang => node!(NodeInner::PrefixOp(Op::Not), None, self.parse_expression(0)),
            Token::Let => self.parse_statement()?,
            Token::LParen => {
                let node = self.parse_expression(0)?;
                assert_eq!(self.peek_token, Token::RParen);
                self.next_token();
                node
            }
            Token::LBracket => self.parse_array()?,
            Token::LBrace => self.parse_block()?,
            Token::Fn => self.parse_fn()?,
            Token::If => self.parse_if()?,

            _ => return None,
        };

        loop {
            let op = match self.peek_token {
                Token::Assign => Op::Assign,
                Token::Plus => Op::Add,
                Token::Minus => Op::Sub,
                Token::Asterisk => Op::Mul,
                Token::Slash => Op::Div,
                Token::Percent => Op::Mod,
                Token::Eq => Op::Eq,
                Token::NotEq => Op::NotEq,
                Token::Lt => Op::Lt,
                Token::Gt => Op::Gt,
                Token::Le => Op::Le,
                Token::Ge => Op::Ge,
                Token::And => Op::And,
                Token::Or => Op::Or,
                Token::LParen => Op::Call,
                Token::LBracket => Op::Index,
                Token::Colon => Op::Colon,
                _ => break,
            };

            match op {
                Op::Call => lhs = self.parse_call(lhs)?,
                Op::Index => lhs = self.parse_index(lhs)?,
                Op::Colon => lhs = self.parse_pair(lhs)?,
                op => {
                    if op.precedence() < precedence {
                        break;
                    }
                    self.next_token();
                    let rhs = self.parse_expression(op.precedence())?;
                    lhs = node!(NodeInner::InfixOp(op), Some(lhs), Some(rhs));
                }
            }
        }
        Some(lhs)
    }

    pub fn parse(&mut self) -> Vec<NodeRef> {
        let mut ast = Vec::new();
        while let Some(node) = self.parse_expression(0) {
            ast.push(node)
        }
        ast
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // TODO maybe use "pretty_assertions" crate here
    macro_rules! assert_parse {
        ($input:expr, $expected:expr) => {
            let mut parser = Parser::new($input);
            match parser.parse_statement() {
                Some(ast) => assert_eq!(format!("{}", ast), $expected,),
                None => panic!(),
            }
        };
    }

    #[test]
    fn int_literal() {
        assert_parse!(
            "453;", "\
453
"
        );
    }

    #[test]
    fn ident() {
        assert_parse!(
            "__var_12;",
            "\
ident __var_12
"
        );
    }

    #[test]
    fn bool() {
        assert_parse!(
            "true", "\
true
"
        );
    }

    // TODO neg shouldn't be an op
    #[test]
    fn op_neg() {
        assert_parse!(
            "-12;",
            "\
neg
    12
"
        );
    }

    #[test]
    fn op_not() {
        assert_parse!(
            "!false;",
            "\
not
    false
"
        );
    }

    #[test]
    fn op_assign() {
        assert_parse!(
            "x = 2",
            "\
assign
    ident x
    2
"
        );
    }

    #[test]
    fn op_add() {
        assert_parse!(
            "6 + 2",
            "\
add
    6
    2
"
        );
    }

    #[test]
    fn op_sub() {
        assert_parse!(
            "6 - 2",
            "\
sub
    6
    2
"
        );
    }

    #[test]
    fn op_mul() {
        assert_parse!(
            "6 * 2",
            "\
mul
    6
    2
"
        );
    }

    #[test]
    fn op_div() {
        assert_parse!(
            "6 / 2",
            "\
div
    6
    2
"
        );
    }

    #[test]
    fn op_eq() {
        assert_parse!(
            "5 == 5",
            "\
eq
    5
    5
"
        );
    }

    #[test]
    fn op_not_eq() {
        assert_parse!(
            "5 != 5",
            "\
neq
    5
    5
"
        );
    }
    #[test]
    fn op_lt() {
        assert_parse!(
            "5 < 5",
            "\
lt
    5
    5
"
        );
    }

    #[test]
    fn op_gt() {
        assert_parse!(
            "5 > 5",
            "\
gt
    5
    5
"
        );
    }

    #[test]
    fn if_expression() {
        assert_parse!(
            "if (x < 0) {return 0}",
            "\
if
    lt
        ident x
        0
then
    block
        return
            0
"
        );
    }

    #[test]
    fn if_with_alternate() {
        assert_parse!(
            "if (a < b) {return a} {return b}",
            "\
if
    lt
        ident a
        ident b
then
    block
        return
            ident a
else
    block
        return
            ident b
"
        );
    }

    #[test]
    fn if_else() {
        assert_parse!(
            "if (a < b) {return a} else {return b}",
            "\
if
    lt
        ident a
        ident b
then
    block
        return
            ident a
else
    block
        return
            ident b
"
        );
    }

    #[test]
    fn op_precedence() {
        assert_parse!(
            "1 + 2 * (3 - 4) / 5",
            "\
add
    1
    mul
        2
        div
            sub
                3
                4
            5
"
        );
    }

    #[test]
    fn let_statement() {
        assert_parse!(
            "let x: i32 = 1 + 2",
            "\
let i32
    ident x
    add
        1
        2
"
        );
    }

    #[test]
    fn return_statement() {
        assert_parse!(
            "return 1 + 2",
            "\
return
    add
        1
        2
"
        );
    }

    #[test]
    fn block_with_semicolons() {
        assert_parse!(
            "{let x: u32 = 1;let y: u32 = 2;return x + y}",
            "\
block
    let u32
        ident x
        1
    let u32
        ident y
        2
    return
        add
            ident x
            ident y
"
        );
    }

    #[test]
    fn block_without_semicolons() {
        assert_parse!(
            "{1 + 2 3 + 4}",
            "\
block
    add
        1
        2
    add
        3
        4
"
        );
    }

    #[test]
    fn nested_blocks() {
        assert_parse!(
            "{{1+2}}",
            "\
block
    block
        add
            1
            2
"
        );
    }

    #[test]
    fn sequential_blocks() {
        // NOTE second block should not be parsed since we're parsing a single statement
        assert_parse!(
            r#"{"1"}{"2"}"#,
            "\
block
    \"1\"
"
        );
    }

    #[test]
    fn nested_sequential_blocks() {
        assert_parse!(
            "{{1}{2}}",
            "\
block
    block
        1
    block
        2
"
        );
    }

    #[test]
    fn fn_expression() {
        assert_parse!(
            "fn test(a: u32, b: u32, c: u32) -> u32 {return a * b - c;}",
            "\
fn test(a: u32, b: u32, c: u32) -> u32
    block
        return
            sub
                mul
                    ident a
                    ident b
                ident c
"
        );
    }

    #[test]
    fn fn_call_noarg() {
        assert_parse!(
            "f()",
            "\
call f
"
        );
    }

    #[test]
    fn fn_call_with_args() {
        assert_parse!(
            "f(2, a+1)",
            "\
call f
    2
    add
        ident a
        1
"
        );
    }

    #[test]
    fn fn_call_with_block_arg() {
        assert_parse!(
            "f(2, {a+1})",
            "\
call f
    2
    block
        add
            ident a
            1
"
        );
    }

    #[test]
    fn fn_call_with_if_expr_arg() {
        assert_parse!(
            "f(2, if(x){1}else{2})",
            "\
call f
    2
    if
        ident x
    then
        block
            1
    else
        block
            2
"
        );
    }

    #[test]
    fn sequential_ifs() {
        assert_parse!(
            "{if(x){1}if(y){2}}",
            "\
block
    if
        ident x
    then
        block
            1
    if
        ident y
    then
        block
            2
"
        );
    }

    #[test]
    fn call_precedence() {
        assert_parse!(
            "f(1) + f(2)",
            "\
add
    call f
        1
    call f
        2
"
        );
    }

    #[test]
    fn if_precedence() {
        assert_parse!(
            "if(a){1}{2} + if(b){3}{4}",
            "\
add
    if
        ident a
    then
        block
            1
    else
        block
            2
    if
        ident b
    then
        block
            3
    else
        block
            4
"
        );
    }

    #[test]
    fn parse_array() {
        assert_parse!(
            "[]",
            "\
array[]
"
        );
        assert_parse!(
            "[1, 2, x]",
            "\
array[1, 2, ident x]
"
        );
    }

    #[test]
    #[should_panic]
    fn parse_invalid_array() {
        assert_parse!("[1, 2, x", "");
    }

    #[test]
    fn parse_index() {
        assert_parse!(
            "arr[2]",
            "\
arr[2]
"
        );
        assert_parse!(
            "arr[x]",
            "\
arr[ident x]
"
        );
        assert_parse!(
            "arr[x + 2]",
            "\
arr[add\n   ident x\n   2]
"
        );
        assert_parse!(
            "arr[1] + arr[2]",
            "\
add
    arr[1]
    arr[2]
"
        );
    }

    #[test]
    #[should_panic]
    fn parse_invalid_index() {
        assert_parse!("arr[2", "");
    }
}
