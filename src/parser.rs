// TODO we need a ParseResult -- do we? why not just panic?

use std::rc::Rc;

use peekmore::{PeekMore, PeekMoreIterator};

use crate::ast::*;
use crate::lexer::{Lexer, Token, Tokens};

pub struct Parser {
    tokens: PeekMoreIterator<Tokens>,
    curr_token: Token,
    peek_token: Token,
    // FIXME disgusting
    peek_token2: Token,
    peek_token3: Token,
}

impl Parser {
    pub fn new(input: &str) -> Parser {
        Parser {
            tokens: Lexer::new(input).tokens().peekmore(),
            curr_token: Token::None,
            peek_token: Token::None,
            peek_token2: Token::None,
            peek_token3: Token::None,
        }
    }

    // FIXME FUCKING FIX THE NEXT/PEEK SITUATION
    fn next_token(&mut self) {
        self.curr_token = self.tokens.next().unwrap_or(Token::None);
        self.peek_token = self.tokens.peek().cloned().unwrap_or(Token::None);
        self.tokens.advance_cursor();
        self.peek_token2 = self.tokens.peek().cloned().unwrap_or(Token::None);
        self.tokens.advance_cursor();
        self.peek_token3 = self.tokens.peek().cloned().unwrap_or(Token::None);
        self.tokens.reset_cursor();
    }

    // TODO this is fucked
    fn parse_type(&mut self) -> Option<Rc<str>> {
        let ty = match self.curr_token.clone() {
            Token::Ident(ident) => {
                if self.peek_token == Token::Lt {
                    self.next_token();
                    self.next_token();

                    let mut generics: Vec<Rc<str>> = Vec::new();
                    while self.curr_token != Token::Gt {
                        if let Some(ty_ident) = &self.parse_type() {
                            generics.push(ty_ident.clone());
                        } else {
                            todo!()
                        }
                        self.next_token();
                    }

                    Some(format!("{}<{}>", ident, generics.join(",")).into())
                } else {
                    Some(ident)
                }
            }
            Token::Star => {
                self.next_token();
                Some(("*".to_owned() + &self.parse_type().unwrap()).into())
            }
            Token::Amp => {
                self.next_token();
                Some(("&".to_owned() + &self.parse_type().unwrap()).into())
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

    /// curr_token after return is RBrace
    fn parse_block(&mut self) -> Option<NodeRef> {
        let mut statements: Vec<NodeRef> = Vec::new();

        match self.curr_token {
            Token::LBrace => {
                self.next_token();
                while self.curr_token != Token::RBrace {
                    if let Some(stmt) = self.parse_statement(true) {
                        statements.push(stmt.clone());
                    }
                }
                assert_eq!(Token::RBrace, self.curr_token);
                self.next_token();

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
        assert_eq!(Token::If, self.curr_token);
        self.next_token();

        match self.parse_expression(0) {
            Some(cond) => {
                self.next_token();
                assert_eq!(Token::LBrace, self.curr_token);
                let then_block = self.parse_block();

                let else_block = if self.curr_token == Token::Else {
                    self.next_token();
                    assert_eq!(Token::LBrace, self.curr_token);
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
        assert_eq!(Token::While, self.curr_token);

        self.next_token();
        match self.parse_expression(0) {
            Some(cond) => {
                self.next_token();
                assert_eq!(Token::LBrace, self.curr_token);
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
                        if &**arg_ident == "self" {
                            args.push(Arg::SelfVal);

                            self.next_token();
                        } else {
                            self.next_token();
                            assert_eq!(Token::Colon, self.curr_token);
                            self.next_token();

                            if let Some(ty) = self.parse_type() {
                                args.push(Arg::Pair {
                                    ident: arg_ident.clone(),
                                    ty,
                                });
                            } else {
                                todo!()
                            }
                        }
                    }
                    Token::Amp => {
                        if let Token::Ident(ident) = &self.peek_token {
                            if &**ident == "self" {
                                args.push(Arg::SelfRef);
                            } else {
                                todo!()
                            }

                            self.next_token();
                        }
                    }
                    Token::Comma => (),
                    _ => break,
                }
                self.next_token();
            }

            assert_eq!(Token::RParen, self.curr_token);
            self.next_token();

            let return_type = match self.curr_token {
                Token::Arrow => {
                    self.next_token();
                    let t = self.parse_type().unwrap();
                    self.next_token();
                    t
                }
                Token::LBrace | Token::Semicolon => "void".into(),
                _ => todo!(),
            };

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
        assert_eq!(Token::LParen, self.curr_token);
        self.next_token();

        let mut args: Vec<NodeRef> = Vec::new();

        let ident = match &*lhs {
            Node::Ident { name } => name.clone(),
            _ => todo!(),
        };

        if self.curr_token != Token::RParen {
            while let Some(node) = self.parse_expression(0) {
                self.next_token();
                args.push(node);
                match self.curr_token {
                    Token::Comma => {
                        self.next_token();
                    }
                    _ => break,
                }
            }
        }

        assert_eq!(Token::RParen, self.curr_token);

        Some(
            Node::Call {
                ident,
                args: Rc::from(args.as_slice()),
            }
            .into(),
        )
    }

    fn parse_index(&mut self, lhs: NodeRef) -> Option<NodeRef> {
        assert_eq!(self.curr_token, Token::LBracket);
        self.next_token();
        let rhs = self.parse_expression(0)?;
        self.next_token();
        assert_eq!(self.curr_token, Token::RBracket);

        Some(
            Node::BinOp {
                op: Op::Index,
                lhs,
                rhs,
            }
            .into(),
        )
    }

    fn parse_struct(&mut self) -> Option<NodeRef> {
        let mut fields: Vec<StructField> = Vec::new();
        let mut generics: Vec<Rc<str>> = Vec::new();

        assert_eq!(Token::Struct, self.curr_token);
        self.next_token();

        if let Token::Ident(ident) = &self.curr_token.clone() {
            self.next_token();
            match self.curr_token {
                Token::LBrace => self.next_token(),
                Token::Lt => {
                    self.next_token();
                    while self.curr_token != Token::Gt {
                        if let Some(Node::Ident { name }) = self.parse_ident().as_deref() {
                            generics.push(name.clone());
                            self.next_token();
                            if let Token::Comma = self.curr_token {
                                self.next_token();
                            }
                        } else {
                            todo!()
                        }
                    }
                    self.next_token(); // eat Gt
                    self.next_token(); // eat LBrace
                }
                _ => todo!(),
            }

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
            self.next_token();

            Some(
                Node::Struct {
                    ident: ident.clone(),
                    fields: Rc::from(fields.as_slice()),
                    generics: Rc::from(generics.as_slice()),
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
            self.next_token();
            if let Some(elem) = self.parse_expression(0) {
                self.next_token();
                elems.push(elem);
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

    fn parse_let_or_const(&mut self, is_const: bool) -> Option<NodeRef> {
        self.next_token(); // eat 'let' / 'const'

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
                self.next_token();
                let rhs = Some(self.parse_expression(0)?);
                self.next_token();
                rhs
            }
            _ => None,
        };

        assert_eq!(Token::Semicolon, self.curr_token);

        if is_const {
            Some(Rc::new(Node::Const { ty, lhs, rhs }))
        } else {
            Some(Rc::new(Node::Let { ty, lhs, rhs }))
        }
    }

    fn parse_impl(&mut self) -> Option<NodeRef> {
        let mut impl_generics: Vec<Rc<str>> = Vec::new();
        let mut type_generics: Vec<Rc<str>> = Vec::new();
        let mut methods: Vec<NodeRef> = Vec::new();

        assert_eq!(Token::Impl, self.curr_token);
        self.next_token();

        if let Token::Lt = self.curr_token {
            self.next_token();
            while self.curr_token != Token::Gt {
                if let Some(Node::Ident { name }) = self.parse_ident().as_deref() {
                    impl_generics.push(name.clone());
                    self.next_token();
                    if let Token::Comma = self.curr_token {
                        self.next_token();
                    }
                } else {
                    todo!()
                }
            }
            self.next_token(); // eat Gt
        };

        if let Token::Ident(ident) = &self.curr_token.clone() {
            self.next_token();

            match self.curr_token {
                Token::LBrace => self.next_token(),
                Token::Lt => {
                    self.next_token();
                    while self.curr_token != Token::Gt {
                        if let Some(Node::Ident { name }) = self.parse_ident().as_deref() {
                            type_generics.push(name.clone());
                            self.next_token();
                            if let Token::Comma = self.curr_token {
                                self.next_token();
                            }
                        } else {
                            todo!()
                        }
                    }
                    self.next_token(); // eat Gt
                    self.next_token(); // eat LBrace
                }
                _ => todo!(),
            }

            while let Token::Fn = self.curr_token {
                if let Some(fn_node) = self.parse_fn(false, None) {
                    methods.push(fn_node);
                } else {
                    todo!()
                }
            }

            assert_eq!(self.curr_token, Token::RBrace);
            self.next_token();

            Some(
                Node::Impl {
                    ident: ident.clone(),
                    methods: Rc::from(methods.as_slice()),
                    impl_generics: impl_generics.into(),
                    type_generics: type_generics.into(),
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

    /// On return, current token is the last token of the expr.
    fn parse_expression(&mut self, precedence: i32) -> Option<NodeRef> {
        let mut lhs = match &self.curr_token {
            Token::NullPtr => Rc::new(Node::NullPtr),
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
            Token::Minus => {
                self.next_token();
                Rc::new(Node::UnOp {
                    op: Op::Neg,
                    rhs: self.parse_expression(Op::precedence(&Op::Neg))?,
                })
            }
            Token::Bang => {
                self.next_token();
                Rc::new(Node::UnOp {
                    op: Op::Not,
                    rhs: self.parse_expression(Op::precedence(&Op::Not))?,
                })
            }
            Token::LParen => {
                self.next_token();
                let node = self.parse_expression(0)?;
                assert_eq!(Token::RParen, self.peek_token);
                self.next_token();
                node
            }
            Token::LBrace => self.parse_block()?,
            Token::If => todo!(), // TODO if expr,
            Token::Amp => {
                self.next_token();
                Rc::new(Node::UnOp {
                    op: Op::Ref,
                    rhs: self.parse_expression(Op::precedence(&Op::Ref))?,
                })
            }
            Token::Star => {
                self.next_token();
                Rc::new(Node::UnOp {
                    op: Op::Deref,
                    rhs: self.parse_expression(Op::precedence(&Op::Deref))?,
                })
            }
            Token::LBracket => self.parse_array()?,
            Token::Dot => {
                self.next_token();
                let ty = self.parse_type()?;
                Rc::new(Node::Ident { name: ty })
            },
            Token::None => return None,
            _ => panic!("unexpected token {}", self.curr_token),
        };

        loop {
            let op = match self.peek_token {
                Token::Assign => Op::Assign(None),
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
                Token::AmpAmp => Op::And,
                Token::BarBar => Op::Or,
                Token::Amp => Op::BitwiseAnd,
                Token::Bar => Op::BitwiseOr,
                Token::LParen => Op::Call,
                Token::LBracket => Op::Index,
                Token::Dot => Op::Dot,
                Token::ColonColon => Op::ScopeRes,
                Token::As => Op::Cast,
                Token::PlusAssign => Op::Assign(Some(Op::Add.into())),
                Token::MinusAssign => Op::Assign(Some(Op::Sub.into())),
                Token::StarAssign => Op::Assign(Some(Op::Mul.into())),
                Token::SlashAssign => Op::Assign(Some(Op::Div.into())),
                Token::LBrace => match (self.peek_token2.clone(), self.peek_token3.clone()) {
                    (Token::Ident(..), Token::Colon) => Op::StructLiteral,
                    _ => return Some(lhs),
                },
                _ => break,
            };

            let mut op_precedence = op.precedence();
            if op_precedence < precedence {
                break;
            }

            lhs = match op {
                Op::Call => {
                    self.next_token();
                    self.parse_call(lhs)?
                }
                Op::Index => {
                    self.next_token();
                    self.parse_index(lhs)?
                }
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
                Op::StructLiteral => {
                    if let Node::Ident { name } = &*lhs {
                        self.next_token();
                        assert_eq!(Token::LBrace, self.curr_token);
                        self.next_token();

                        let mut fields: Vec<StructLiteralField> = Vec::new();

                        while self.curr_token != Token::RBrace {
                            if let Token::Comma = self.curr_token {
                                self.next_token();
                            }

                            let field_name =
                                if let Token::Ident(field_name) = self.curr_token.clone() {
                                    field_name
                                } else {
                                    println!("{:?}", lhs);
                                    todo!();
                                };

                            self.next_token();
                            assert_eq!(Token::Colon, self.curr_token);
                            self.next_token();

                            let val = if let Some(expr) = self.parse_expression(0) {
                                expr
                            } else {
                                todo!();
                            };

                            fields.push(StructLiteralField {
                                ident: field_name.clone(),
                                val,
                            });

                            self.next_token();
                        }

                        return Some(
                            Node::StructLiteral {
                                ident: name.clone(),
                                fields: fields.as_slice().into(),
                            }
                            .into(),
                        );
                    } else {
                        break;
                    }
                }
                op => {
                    if op == Op::Dot {
                        op_precedence += 1;
                    }

                    self.next_token(); // curr_token is now the op
                    self.next_token(); // curr_token is now rhs
                    let rhs = self.parse_expression(op_precedence)?;
                    Rc::new(Node::BinOp { op, lhs, rhs })
                }
            };
        }
        Some(lhs)
    }

    fn parse_statement(&mut self, mut expect_semicolon: bool) -> Option<NodeRef> {
        let node = match self.curr_token {
            Token::Let => {
                expect_semicolon = true;
                self.parse_let_or_const(false)
            }
            Token::Return => {
                expect_semicolon = true;
                self.next_token();
                let r = Some(Rc::new(Node::Return {
                    expr: self.parse_expression(0),
                }));
                self.next_token();
                r
            }
            Token::If => {
                expect_semicolon = false;
                self.parse_if()
            }
            Token::While => {
                expect_semicolon = false;
                self.parse_while()
            }
            Token::Struct => {
                expect_semicolon = false;
                self.parse_struct()
            }
            Token::Const => {
                expect_semicolon = true;
                self.parse_let_or_const(true)
            }
            Token::Impl => self.parse_impl(),
            Token::Fn => self.parse_fn(false, None),
            Token::Extern => {
                expect_semicolon = true;
                self.next_token();
                if let Token::Str(linkage) = &self.curr_token.clone() {
                    self.next_token();
                    self.parse_fn(true, Some(linkage.clone()))
                } else {
                    todo!()
                }
            }
            _ => {
                let expr = self.parse_expression(0);
                self.next_token();
                expr
            }
        };

        if expect_semicolon {
            assert_eq!(Token::Semicolon, self.curr_token);
            self.next_token()
        }

        node
    }

    pub fn parse(&mut self) -> Vec<NodeRef> {
        let mut ast = Vec::new();
        self.next_token(); // load first token
        while let Some(node) = self.parse_statement(false) {
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
            parser.next_token();
            match parser.parse_statement(false) {
                Some(ast) => assert_eq!($expected, format!("{:?}", ast)),
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
            "'c'", "\
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
    fn if_stmt() {
        assert_parse!(
            "if x < 0 {return 0;}",
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
    fn if_else_stmt() {
        assert_parse!(
            "if a < b {return a;} else {return b;}",
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

        assert_parse!(
            "if (a < b) {return a;} else {return b;}",
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
            "return 1 + 2;",
            "\
return
    add
        1
        2
"
        );
    }

    #[test]
    fn block_with_semicolon_delimited_stmts() {
        assert_parse!(
            "{let x: u32 = 1;let y: u32 = 2;return x + y;}",
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
    fn fn_stmt() {
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

    // TODO block expr
    //     #[test]
    //     fn fn_call_with_block_arg() {
    //         assert_parse!(
    //             "f(2, {a+1})",
    //             "\
    // call f
    //     2
    //     block
    //         add
    //             ident a
    //             1
    // "
    //         );
    //     }

    // TODO if expr
    //     #[test]
    //     fn fn_call_with_if_expr_arg() {
    //         assert_parse!(
    //             "f(2, if(x){1}else{2})",
    //             "\
    // call f
    //     2
    //     if
    //         ident x
    //     then
    //         block
    //             1
    //     else
    //         block
    //             2
    // "
    //         );
    //     }

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

    // TODO if expr
    //     #[test]
    //     fn if_precedence() {
    //         assert_parse!(
    //             "if(a){1}{2} + if(b){3}{4}",
    //             "\
    // add
    //     if
    //         ident a
    //     then
    //         block
    //             1
    //     else
    //         block
    //             2
    //     if
    //         ident b
    //     then
    //         block
    //             3
    //     else
    //         block
    //             4
    // "
    //         );
    //     }

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
fn f(x: *u32) -> *u32
    block
        return
            ident x
"
        );
    }

    #[test]
    fn while_loop() {
        assert_parse!(
            "while x < 5 && c {a = x + 1;}",
            "\
while
    and
        lt
            ident x
            5
        ident c
    block
        assign
            ident a
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
                fn b(&self, other: *T) -> u8 {return 0;}
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

    #[test]
    fn generic_type_instance() {
        assert_parse!(
            "let a: T<&u32>;",
            "\
let T<&u32>
    ident a
"
        );
    }

    #[test]
    fn struct_defn_with_generics() {
        assert_parse!(
            "struct T<A, B> {a: u32; b: u8; c: A;}",
            "\
struct T<A,B>
    a u32
    b u8
    c A
"
        );
    }

    #[test]
    fn impl_for_generic_struct() {
        assert_parse!(
            "impl T<A, B> {}",
            "\
impl T<A,B>
"
        );
        assert_parse!(
            "impl<A, B> T<A, B> {}",
            "\
impl<A,B> T<A,B>
"
        );
    }

    #[test]
    fn struct_literal() {
        assert_parse!(
            "foo.bar(1, Rect {x: 0, y: 0, w: 10, h: 10});",
            "\
dot
    ident foo
    call bar
        1
        struct_literal Rect
            x
                0
            y
                0
            w
                10
            h
                10
"
        );

        assert_parse!(
            "let _: Foo = Foo {a: 1 + 2, b: Bar {x: 5}};",
            "\
let Foo
    ident _
    struct_literal Foo
        a
            add
                1
                2
        b
            struct_literal Bar
                x
                    5
"
        );

        assert_parse!(
            "let _: A = &A {x: 1};",
            "\
let A
    ident _
    ref
        struct_literal A
            x
                1
"
        );
        
    }

    #[test]
    fn generic_struct_literal() {
        assert_parse!(
            "let _: &A<T> = &.A<T> {x: 1};",
            "\
let &A<T>
    ident _
    ref
        struct_literal A<T>
            x
                1
"
        );
    }
}
