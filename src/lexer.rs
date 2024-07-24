use std::{rc::Rc, str};

use crate::ast::Span;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TokenKind {
    None,
    Illegal,
    Ident(Rc<str>),
    Int(Rc<str>),
    Str(Rc<str>),
    Char(Rc<u8>),

    // Operators
    Assign,
    Plus,
    Minus,
    Bang,
    Star,
    Slash,
    Percent,
    Amp,
    Bar,
    AmpAmp,
    BarBar,
    Lt,
    Gt,
    Le,
    Ge,
    Eq,
    NotEq,
    Arrow,
    FatArrow,
    Dot,
    DotDot,
    ColonColon,
    As,
    PlusAssign,
    MinusAssign,
    StarAssign,
    SlashAssign,

    // Delimiters
    Comma,
    Colon,
    Semicolon,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,

    // Keywords
    Fn,
    Let,
    True,
    False,
    If,
    Else,
    While,
    Return,
    Struct,
    Impl,
    NullPtr,
    Extern,
    Const,
    Match,

    Hash,
}

#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn none() -> Token {
        Token {
            kind: TokenKind::None,
            span: Span {
                start_line: 0,
                start_col: 0,
                end_line: 0,
                end_col: 0,
            },
        }
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            TokenKind::Ident(s) => f.write_fmt(format_args!("ident:{}", s)),
            TokenKind::Int(s) => f.write_fmt(format_args!("int:{}", s)),
            _ => f.write_fmt(format_args!("{:?}", self)),
        }
    }
}

pub struct Tokens {
    input: Rc<str>,
    position: usize,
    read_position: usize,
    ch: Option<u8>,
    current_line: usize,
    current_col: usize,
}

impl Tokens {
    fn read_char(&mut self) {
        if self.read_position >= self.input.len() {
            self.ch = None;
        } else {
            self.ch = Some(self.input.as_bytes()[self.read_position]);
        }
        self.position = self.read_position;
        self.read_position += 1;
        self.current_col += 1;
    }

    fn peek_char(&self) -> Option<u8> {
        if self.read_position >= self.input.len() {
            None
        } else {
            Some(self.input.as_bytes()[self.read_position])
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.ch {
            match ch {
                b'\n' => {
                    self.current_col = 0;
                    self.current_line += 1;
                    self.read_char();
                }
                _ => {
                    if ch.is_ascii_whitespace() {
                        self.read_char();
                    } else {
                        break;
                    }
                }
            }
        }
    }

    fn read_identifier(&mut self) -> Rc<str> {
        let pos_start = self.position;
        while let Some(c) = self.ch {
            match c {
                (b'0'..=b'9') | (b'a'..=b'z') | (b'A'..=b'Z') | b'_' => {
                    self.read_char();
                }
                _ => break,
            }
        }
        Rc::from(self.input[pos_start..self.position].to_string())
    }

    fn read_number(&mut self) -> Rc<str> {
        let pos_start = self.position;

        while let Some(b'0'..=b'9' | b'x' | b'a'..=b'f' | b'A'..=b'F') = self.ch {
            self.read_char();
        }

        Rc::from(self.input[pos_start..self.position].to_string())
    }

    fn read_string(&mut self) -> Rc<str> {
        let pos_start = self.position;

        self.read_char();
        // TODO handle missing end quote
        while self.ch != Some(b'"') {
            self.read_char();
        }

        Rc::from(self.input[pos_start + 1..self.position].to_string())
    }

    pub fn next_token(&mut self) -> Token {
        let mut skip_tail_read_char = false;
        let start_col = self.current_col;

        self.skip_whitespace();
        let token_kind = match self.ch {
            Some(b'=') => match self.peek_char() {
                Some(b'=') => {
                    self.read_char();
                    TokenKind::Eq
                }
                Some(b'>') => {
                    self.read_char();
                    TokenKind::FatArrow
                }
                _ => TokenKind::Assign,
            },
            Some(b'+') => match self.peek_char() {
                Some(b'=') => {
                    self.read_char();
                    TokenKind::PlusAssign
                }
                _ => TokenKind::Plus,
            },
            Some(b'-') => match self.peek_char() {
                Some(b'>') => {
                    self.read_char();
                    TokenKind::Arrow
                }
                Some(b'=') => {
                    self.read_char();
                    TokenKind::MinusAssign
                }
                _ => TokenKind::Minus,
            },
            Some(b'!') => match self.peek_char() {
                Some(b'=') => {
                    self.read_char();
                    TokenKind::NotEq
                }
                _ => TokenKind::Bang,
            },
            Some(b'*') => match self.peek_char() {
                Some(b'=') => {
                    self.read_char();
                    TokenKind::StarAssign
                }
                _ => TokenKind::Star,
            },
            Some(b'<') => match self.peek_char() {
                Some(b'=') => {
                    self.read_char();
                    TokenKind::Le
                }
                _ => TokenKind::Lt,
            },
            Some(b'>') => match self.peek_char() {
                Some(b'=') => {
                    self.read_char();
                    TokenKind::Ge
                }
                _ => TokenKind::Gt,
            },
            Some(b'/') => match self.peek_char() {
                Some(b'/') => loop {
                    self.read_char();
                    if let Some(c) = self.ch {
                        if c == b'\n' {
                            return self.next_token();
                        }
                    } else {
                        return Token::none();
                    }
                },
                Some(b'=') => {
                    self.read_char();
                    TokenKind::SlashAssign
                }
                _ => TokenKind::Slash,
            },
            Some(b'%') => TokenKind::Percent,
            Some(b'&') => match self.peek_char() {
                Some(b'&') => {
                    self.read_char();
                    TokenKind::AmpAmp
                }
                _ => TokenKind::Amp,
            },
            Some(b'|') => match self.peek_char() {
                Some(b'|') => {
                    self.read_char();
                    TokenKind::BarBar
                }
                _ => TokenKind::Bar,
            },
            Some(b'(') => TokenKind::LParen,
            Some(b')') => TokenKind::RParen,
            Some(b'{') => TokenKind::LBrace,
            Some(b'}') => TokenKind::RBrace,
            Some(b'[') => TokenKind::LBracket,
            Some(b']') => TokenKind::RBracket,
            Some(b',') => TokenKind::Comma,
            Some(b':') => match self.peek_char() {
                Some(b':') => {
                    self.read_char();
                    TokenKind::ColonColon
                }
                _ => TokenKind::Colon,
            },
            Some(b';') => TokenKind::Semicolon,
            Some(b'"') => TokenKind::Str(self.read_string()),
            Some(b'\'') => {
                self.read_char();
                if let (Some(ch), Some(peek)) = (self.ch, self.peek_char()) {
                    let ch = if ch == b'\\' && peek == b'n' {
                        self.read_char();
                        self.read_char();
                        10
                    } else {
                        self.read_char();
                        ch
                    };

                    match self.ch {
                        Some(b'\'') => TokenKind::Char(ch.into()),
                        _ => todo!(),
                    }
                } else {
                    todo!()
                }
            }
            Some(b'.') => match self.peek_char() {
                Some(b'.') => {
                    self.read_char();
                    TokenKind::DotDot
                }
                _ => TokenKind::Dot,
            },
            Some(b'#') => TokenKind::Hash,
            Some(c) => {
                skip_tail_read_char = true;
                match c {
                    (b'a'..=b'z') | (b'A'..=b'Z') | b'_' => {
                        let ident = self.read_identifier();
                        match ident.as_ref() {
                            "fn" => TokenKind::Fn,
                            "let" => TokenKind::Let,
                            "true" => TokenKind::True,
                            "false" => TokenKind::False,
                            "if" => TokenKind::If,
                            "else" => TokenKind::Else,
                            "return" => TokenKind::Return,
                            "while" => TokenKind::While,
                            "struct" => TokenKind::Struct,
                            "impl" => TokenKind::Impl,
                            "nullptr" => TokenKind::NullPtr,
                            "as" => TokenKind::As,
                            "extern" => TokenKind::Extern,
                            "const" => TokenKind::Const,
                            "match" => TokenKind::Match,
                            _ => TokenKind::Ident(ident),
                        }
                    }
                    (b'0'..=b'9') => TokenKind::Int(self.read_number()),

                    _ => TokenKind::Illegal,
                }
            }
            None => TokenKind::None,
        };
        if !skip_tail_read_char {
            self.read_char();
        }
        Token {
            kind: token_kind,
            span: Span {
                start_line: self.current_line,
                start_col,
                end_line: self.current_line,
                end_col: self.current_col,
            },
        }
    }
}

impl Iterator for Tokens {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.next_token();
        match &token.kind {
            TokenKind::None => None,
            _ => Some(token),
        }
    }
}

pub struct Lexer {
    input: Rc<str>,
}

impl Lexer {
    pub fn new(input: &str) -> Lexer {
        Lexer {
            input: input.into(),
        }
    }

    pub fn tokens(&self) -> Tokens {
        let mut tokens = Tokens {
            input: self.input.clone(),
            position: 0,
            read_position: 0,
            ch: None,
            current_line: 1,
            current_col: 0,
        };
        tokens.read_char();
        tokens
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use TokenKind::*;

    #[test]
    fn symbols() {
        let source = "=+-!*/(){}[],;:->&||..&&.::as%+=";
        let expected = [
            Assign, Plus, Minus, Bang, Star, Slash, LParen, RParen, LBrace, RBrace, LBracket,
            RBracket, Comma, Semicolon, Colon, Arrow, Amp, BarBar, DotDot, AmpAmp, Dot, ColonColon,
            As, Percent, PlusAssign,
        ];
        let mut tokens = Lexer::new(source).tokens();
        expected
            .iter()
            .for_each(|t| assert_eq!(*t, tokens.next_token().kind));
    }

    #[test]
    fn read_identifier() {
        let mut tokens = Lexer::new("let ").tokens();
        assert_eq!("let", &*tokens.read_identifier());
    }

    #[test]
    fn string() {
        let expected = [LBrace, Str("some string".into()), RBrace];
        let mut tokens = Lexer::new(r#"{"some string"}"#).tokens();
        expected
            .iter()
            .for_each(|t| assert_eq!(*t, tokens.next_token().kind));
    }

    #[test]
    fn char() {
        let expected = [LBrace, Char(b'c'.into()), RBrace];
        let mut tokens = Lexer::new(r#"{'c'}"#).tokens();
        expected
            .iter()
            .for_each(|t| assert_eq!(*t, tokens.next_token().kind));
    }

    #[test]
    fn comment() {
        let source = "=+-!*/(){}[]// comment\n,;:->&||..&&.";
        let expected = [
            Assign, Plus, Minus, Bang, Star, Slash, LParen, RParen, LBrace, RBrace, LBracket,
            RBracket, Comma, Semicolon, Colon, Arrow, Amp, BarBar, DotDot, AmpAmp, Dot,
        ];
        let mut tokens = Lexer::new(source).tokens();
        expected
            .iter()
            .for_each(|t| assert_eq!(*t, tokens.next_token().kind));
    }
}
