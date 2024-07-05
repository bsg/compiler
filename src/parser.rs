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

    // TODO this is fucked
    fn parse_type(&mut self) -> Option<Rc<str>> {
        fn get_ident_str(ident: &Token) -> Option<&str> {
            if let Token::Ident(name) = ident {
                Some(name)
            } else {
                None
            }
        }

        let ty = match self.curr_token.clone() {
            Token::Ident(ident) => Some(ident),
            Token::Star => {
                self.next_token();
                if let Some(ty) = get_ident_str(&self.curr_token) {
                    Some(("*".to_owned() + ty).into())
                } else {
                    Some(("*".to_owned() + &self.parse_type().unwrap()).into())
                }
            }
            Token::Amp => {
                self.next_token();
                if let Some(ty) = get_ident_str(&self.curr_token) {
                    Some(("&".to_owned() + ty).into())
                } else {
                    Some(("&".to_owned() + &self.parse_type().unwrap()).into())
                }
            }
            Token::LBracket => {
                self.next_token();
                let ty = match self.curr_token.clone() {
                    Token::Ident(ty) => Some(ty),
                    Token::LBracket => self.parse_type(),
                    _ => todo!(),
                };

                if let Some(ty) = ty {
                    if self.peek_token == Token::Semicolon {
                        self.next_token();
                        self.next_token();
                        if let Token::Int(len) = &self.curr_token.clone() {
                            self.next_token();
                            assert_eq!(Token::RBracket, self.curr_token);
                            Some(format!("[{}; {}]", ty, len).as_str().into())
                        } else {
                            todo!()
                        }
                    } else if self.peek_token == Token::RBracket {
                        Some(format!("[{}]", ty).as_str().into())
                    } else {
                        todo!()
                    }
                } else {
                    todo!()
                }
            }
            _ => todo!(),
        };

        ty
    }

    fn parse_block(&mut self) -> Option<NodeRef> {
        assert_eq!(self.curr_token, Token::LBrace);

        let mut statements: Vec<NodeRef> = Vec::new();

        match self.curr_token {
            Token::LBrace => {
                while let Some(stmt) = self.parse_statement().as_ref() {
                    statements.push(stmt.clone());
                }

                Some(
                    Node::Block {
                        statements: Rc::from(statements.as_slice()),
                    }
                    .into(),
                )
            }
            _ => todo!(),
        }
    }

    /// caller must ensure current token is If
    fn parse_if(&mut self) -> Option<NodeRef> {
        assert_eq!(self.curr_token, Token::If);

        match self.parse_expression(0) {
            Some(cond) => {
                assert_eq!(self.peek_token, Token::LBrace);
                self.next_token();
                let then_block = self.parse_block();

                // eat 'else' if there is one
                if self.peek_token == Token::Else {
                    self.next_token();
                    assert_eq!(self.peek_token, Token::LBrace);
                }

                // TODO do not allow without preceding 'else' keyword
                let else_block = if self.peek_token == Token::LBrace {
                    self.next_token();
                    self.parse_block()
                } else {
                    None
                };

                match then_block {
                    Some(then_blk) => Some(
                        Node::If {
                            condition: cond,
                            then_block: then_blk,
                            else_block,
                        }
                        .into(),
                    ),
                    None => todo!(),
                }
            }
            None => todo!(),
        }
    }

    /// caller must ensure current token is While
    fn parse_while(&mut self) -> Option<NodeRef> {
        assert_eq!(self.curr_token, Token::While);

        match self.parse_expression(0) {
            Some(cond) => {
                assert_eq!(self.peek_token, Token::LBrace);
                self.next_token();
                let body = self.parse_block();

                match body {
                    Some(while_body) => Some(
                        Node::While {
                            condition: cond,
                            body: while_body,
                        }
                        .into(),
                    ),
                    None => todo!(),
                }
            }
            None => todo!(),
        }
    }

    // TODO linkage should be an enum
    /// caller must ensure current token is Fn
    fn parse_fn(&mut self, is_extern: bool, linkage: Option<Rc<str>>) -> Option<NodeRef> {
        let mut args: Vec<Arg> = Vec::new();

        assert_eq!(Token::Fn, self.curr_token);
        self.next_token();

        if let Token::Ident(ident) = &self.curr_token.clone() {
            self.next_token();
            assert_eq!(self.curr_token, Token::LParen);
            self.next_token();

            loop {
                match &self.curr_token.clone() {
                    Token::Ident(arg_ident) => {
                        self.next_token();
                        assert_eq!(Token::Colon, self.curr_token);
                        self.next_token();

                        if let Some(ty) = self.parse_type() {
                            args.push(Arg {
                                ident: arg_ident.clone(),
                                ty,
                            });
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
                Token::Star => {
                    self.next_token();
                    match self.curr_token.clone() {
                        Token::Ident(ret_ident) => ret_ident,
                        _ => todo!(),
                    }
                }
                _ => todo!(),
            };
            self.next_token();

            let body = if self.curr_token == Token::LBrace {
                self.parse_block()
            } else {
                None
            };


            Some(
                Node::Fn {
                    ident: ident.clone(),
                    args: Rc::from(args.as_slice()),
                    ret_ty: return_type.clone(),
                    is_extern,
                    linkage,
                    body,
                }
                .into(),
            )
        } else {
            todo!()
        }
    }

    fn parse_call(&mut self, lhs: NodeRef) -> Option<NodeRef> {
        let mut args: Vec<NodeRef> = Vec::new();

        let ident = match &*lhs {
            Node::Ident { name } => name.clone(),
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

        Some(
            Node::Call {
                ident,
                args: Rc::from(args.as_slice()),
            }
            .into(),
        )
    }

    fn parse_index(&mut self, lhs: NodeRef) -> Option<NodeRef> {
        assert_eq!(self.peek_token, Token::LBracket);

        self.next_token();

        let rhs = self.parse_expression(0)?;
        assert_eq!(self.peek_token, Token::RBracket);
        self.next_token();

        Some(
            Node::BinOp {
                op: Op::Index,
                lhs,
                rhs,
            }
            .into(),
        )
    }

    fn parse_pair(&mut self, key: NodeRef) -> Option<NodeRef> {
        assert_eq!(self.peek_token, Token::Colon);
        self.next_token();
        let value = self.parse_expression(0)?;

        if self.peek_token == Token::Comma {
            self.next_token();
        }

        Some(Node::Pair { key, value }.into())
    }

    fn parse_struct(&mut self) -> Option<NodeRef> {
        let mut fields: Vec<StructField> = Vec::new();

        assert_eq!(Token::Struct, self.curr_token);
        self.next_token();

        if let Token::Ident(ident) = &self.curr_token.clone() {
            self.next_token();
            assert_eq!(self.curr_token, Token::LBrace);
            self.next_token();

            loop {
                match &self.curr_token.clone() {
                    Token::Ident(arg_ident) => {
                        self.next_token();
                        assert_eq!(Token::Colon, self.curr_token);
                        self.next_token();

                        if let Some(ty) = self.parse_type() {
                            fields.push(StructField {
                                ident: arg_ident.clone(),
                                ty,
                            });
                        } else {
                            todo!()
                        }

                        self.next_token();
                        assert_eq!(Token::Semicolon, self.curr_token);
                        self.next_token();
                    }
                    Token::RBrace => break,
                    _ => todo!(),
                }
            }

            assert_eq!(self.curr_token, Token::RBrace);

            Some(
                Node::Struct {
                    ident: ident.clone(),
                    fields: Rc::from(fields.as_slice()),
                }
                .into(),
            )
        } else {
            todo!()
        }
    }

    fn parse_array(&mut self) -> Option<NodeRef> {
        let mut elems: Vec<NodeRef> = Vec::new();

        assert_eq!(Token::LBracket, self.curr_token);

        loop {
            if let Some(elem) = self.parse_expression(0) {
                elems.push(elem);
                self.next_token();
            } else {
                todo!()
            }

            match self.curr_token {
                Token::Comma => (),
                Token::RBracket => break,
                _ => todo!(),
            }
        }

        Some(Rc::new(Node::Array {
            elems: elems.as_slice().into(),
        }))
    }

    fn parse_statement(&mut self) -> Option<NodeRef> {
        let node = match self.tokens.peek() {
            Some(Token::Let) => {
                self.next_token();
                self.next_token(); // eat 'let'

                let lhs = if let Some(ident) = self.parse_ident() {
                    ident
                } else {
                    todo!()
                };

                self.next_token();
                assert_eq!(Token::Colon, self.curr_token);
                self.next_token();

                let ty = if let Some(ty) = self.parse_type() {
                    self.next_token();
                    ty
                } else {
                    todo!()
                };

                let rhs = match self.curr_token {
                    Token::Assign => {
                        let rhs = Some(self.parse_expression(0)?);
                        self.next_token();
                        rhs
                    }
                    Token::Semicolon => None,
                    _ => todo!(),
                };

                assert_eq!(Token::Semicolon, self.curr_token);

                Some(Rc::new(Node::Let { ty, lhs, rhs }))
            }
            Some(Token::Return) => {
                self.next_token();
                Some(Rc::new(Node::Return {
                    stmt: self.parse_expression(0),
                }))
            }
            Some(_) => self.parse_expression(0),
            None => return None,
        };

        if self.peek_token == Token::Semicolon {
            self.next_token();
        }

        node
    }

    fn parse_impl(&mut self) -> Option<NodeRef> {
        let mut methods: Vec<NodeRef> = Vec::new();

        assert_eq!(Token::Impl, self.curr_token);
        self.next_token();

        if let Token::Ident(ident) = &self.curr_token.clone() {
            self.next_token();
            assert_eq!(self.curr_token, Token::LBrace);
            self.next_token();

            while let Token::Fn = self.curr_token {
                if let Some(fn_node) = self.parse_fn(false, None) {
                    methods.push(fn_node);
                } else {
                    todo!()
                }

                assert_eq!(self.curr_token, Token::RBrace);
                self.next_token();
            }

            assert_eq!(self.curr_token, Token::RBrace);

            Some(
                Node::Impl {
                    ident: ident.clone(),
                    methods: Rc::from(methods.as_slice()),
                }
                .into(),
            )
        } else {
            todo!()
        }
    }

    fn parse_ident(&self) -> Option<NodeRef> {
        match &self.curr_token {
            Token::Ident(name) => Some(Node::Ident { name: name.clone() }.into()),
            _ => todo!(),
        }
    }

    /// This skips over the current token. On return, current token is the last token of the expr.
    fn parse_expression(&mut self, precedence: i32) -> Option<NodeRef> {
        self.next_token();
        let mut lhs = match &self.curr_token {
            Token::Int(s) => {
                let value = match s.parse() {
                    Ok(i) => i,
                    Err(_) => todo!(),
                };

                Rc::new(Node::Int { value })
            }
            Token::Str(s) => Rc::new(Node::Str { value: s.clone() }),
            Token::Char(c) => Rc::new(Node::Char { value: c.clone() }),
            Token::Ident(_) => self.parse_ident()?,
            Token::True => Rc::new(Node::Bool { value: true }),
            Token::False => Rc::new(Node::Bool { value: false }),
            Token::Minus => Rc::new(Node::UnOp {
                op: Op::Neg,
                rhs: self.parse_expression(Op::precedence(&Op::Neg))?,
            }),
            Token::Bang => Rc::new(Node::UnOp {
                op: Op::Not,
                rhs: self.parse_expression(Op::precedence(&Op::Not))?,
            }),
            Token::Let => self.parse_statement()?,
            Token::LParen => {
                let node = self.parse_expression(0)?;
                assert_eq!(self.peek_token, Token::RParen);
                self.next_token();
                node
            }
            Token::LBrace => self.parse_block()?,
            Token::Fn => self.parse_fn(false, None)?,
            Token::If => self.parse_if()?,
            Token::While => self.parse_while()?,
            Token::Amp => Rc::new(Node::UnOp {
                op: Op::Ref,
                rhs: self.parse_expression(Op::precedence(&Op::Ref))?,
            }),
            Token::Star => Rc::new(Node::UnOp {
                op: Op::Deref,
                rhs: self.parse_expression(Op::precedence(&Op::Deref))?,
            }),
            Token::Struct => self.parse_struct()?,
            Token::Impl => self.parse_impl()?,
            Token::LBracket => self.parse_array()?,
            Token::Extern => {
                self.next_token();
                if let Token::Str(linkage) = &self.curr_token.clone() {
                    self.next_token();
                    self.parse_fn(true, Some(linkage.clone()))?
                } else {
                    todo!()
                }
            }
            _ => return None,
        };

        loop {
            let op = match self.peek_token {
                Token::Assign => Op::Assign,
                Token::Plus => Op::Add,
                Token::Minus => Op::Sub,
                Token::Star => Op::Mul,
                Token::Slash => Op::Div,
                Token::Percent => Op::Mod,
                Token::Eq => Op::Eq,
                Token::NotEq => Op::NotEq,
                Token::Lt => Op::Lt,
                Token::Gt => Op::Gt,
                Token::Le => Op::Le,
                Token::Ge => Op::Ge,
                Token::Amp => Op::And,
                Token::Bar => Op::Or,
                Token::LParen => Op::Call,
                Token::LBracket => Op::Index,
                Token::Colon => Op::Colon,
                Token::Dot => Op::Dot,
                Token::ColonColon => Op::ScopeRes,
                Token::As => Op::Cast,
                _ => break,
            };

            let mut op_precedence = op.precedence();
            if op_precedence < precedence {
                break;
            }

            lhs = match op {
                Op::Call => self.parse_call(lhs)?,
                Op::Index => self.parse_index(lhs)?,
                Op::Colon => self.parse_pair(lhs)?,
                Op::Cast => {
                    self.next_token();
                    self.next_token();
                    let type_ident = self.parse_type()?;
                    Rc::new(Node::BinOp {
                        op: Op::Cast,
                        lhs,
                        rhs: Node::Ident { name: type_ident }.into(),
                    })
                }
                op => {
                    // TODO feels hacky, test the shit out of this
                    if op == Op::Dot {
                        op_precedence += 1;
                    }

                    self.next_token();
                    let rhs = self.parse_expression(op_precedence)?;
                    Rc::new(Node::BinOp { op, lhs, rhs })
                }
            };
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
                Some(ast) => assert_eq!(format!("{:?}", ast), $expected),
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
    fn bool_literal() {
        assert_parse!(
            "true", "\
true
"
        );
    }

    #[test]
    fn str_literal() {
        assert_parse!(
            "\"test\"",
            "\
\"test\"
"
        );
    }

    #[test]
    fn char_literal() {
        assert_parse!(
            "'c'",
            "\
'c'
"
        );
    }

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
    fn op_neq() {
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
            "if x < 0 {return 0}",
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
            "if a < b {return a} else {return b}",
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
            "!1 + 2 * !(3 - 4) / 5",
            "\
add
    not
        1
    mul
        2
        div
            not
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
            "let x: i32 = 1 + 2;",
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

    // TODO make sure this does not parse
    //     #[test]
    //     fn block_without_semicolons() {
    //         assert_parse!(
    //             "{1 + 2 3 + 4}",
    //             "\
    // block
    //     add
    //         1
    //         2
    //     add
    //         3
    //         4
    // "
    //         );
    //     }

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
    fn parse_array_type() {
        assert_parse!(
            "let arr: [u8; 5];",
            "\
let [u8; 5]
    ident arr
"
        );
        assert_parse!(
            "let arr: [[u8; 5]; 2];",
            "\
let [[u8; 5]; 2]
    ident arr
"
        );
    }

    #[test]
    fn parse_index() {
        assert_parse!(
            "arr[2]",
            "\
index
    ident arr
    2
"
        );
        assert_parse!(
            "arr[x]",
            "\
index
    ident arr
    ident x
"
        );
        assert_parse!(
            "arr[x + 2]",
            "\
index
    ident arr
    add
        ident x
        2
"
        );
        assert_parse!(
            "arr[1] + arr[2]",
            "\
add
    index
        ident arr
        1
    index
        ident arr
        2
"
        );
    }

    #[test]
    #[should_panic]
    fn parse_invalid_index() {
        assert_parse!("arr[2", "");
    }

    #[test]
    fn get_ref() {
        assert_parse!(
            "&foo",
            "\
ref
    ident foo
"
        );
    }

    #[test]
    fn deref() {
        assert_parse!(
            "*p",
            "\
deref
    ident p
"
        );
    }

    #[test]
    fn ptr_type_in_fn_head() {
        assert_parse!(
            "fn f(x: *u32) -> *u32 {return x;}",
            "\
fn f(x: *u32) -> u32
    block
        return
            ident x
"
        );
    }

    #[test]
    fn while_loop() {
        assert_parse!(
            "while x < 5 {x = x + 1}",
            "\
while
    lt
        ident x
        5
    block
        assign
            ident x
            add
                ident x
                1
"
        );
    }

    #[test]
    fn struct_defn() {
        assert_parse!(
            "struct T {a: u32; b: u8; c: A;}",
            "\
struct T
    a u32
    b u8
    c A
"
        );
    }

    #[test]
    fn dot_operator() {
        assert_parse!(
            "*foo.bar.baz * a.b",
            "\
mul
    deref
        dot
            dot
                ident foo
                ident bar
            ident baz
    dot
        ident a
        ident b
"
        );
    }

    #[test]
    fn impl_defn() {
        assert_parse!(
            "impl T {\
fn a() -> u32 {return 0;}
fn b(self: &Self, other: *T) -> u8 {return 0;}
}",
            "\
impl T
    fn a() -> u32
        block
            return
                0
    fn b(self: &Self, other: *T) -> u8
        block
            return
                0
"
        );
    }

    #[test]
    fn array_literal() {
        assert_parse!(
            "[1, 2, 3, x]",
            "\
array
    1
    2
    3
    ident x
"
        );

        assert_parse!(
            "[[1, 2], [3, x]]",
            "\
array
    array
        1
        2
    array
        3
        ident x
"
        );
    }

    #[test]
    fn scope_resolution() {
        assert_parse!(
            "1 * A::foo()",
            "\
mul
    1
    scoperes
        ident A
        call foo
"
        );
    }

    #[test]
    fn cast_operator() {
        assert_parse!(
            "1 * A::foo() as *u32 * 5",
            "\
mul
    1
    mul
        cast
            scoperes
                ident A
                call foo
            ident *u32
        5
"
        );
    }

    #[test]
    fn extern_fn() {
        assert_parse!(
            "extern \"C\" fn exit(status: u32) -> void;",
            "\
extern \"C\" fn exit(status: u32) -> void
"
        );
    }
}
