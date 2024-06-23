use std::{rc::Rc, str};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    None,
    Illegal,
    Ident(Rc<str>),
    Int(Rc<str>),
    Str(Rc<str>),

    // Operators
    Assign,
    Plus,
    Minus,
    Bang,
    Asterisk,
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
    Return,
}

impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ident(s) => f.write_fmt(format_args!("ident:{}", s)),
            Self::Int(s) => f.write_fmt(format_args!("int:{}", s)),
            _ => f.write_fmt(format_args!("{:?}", self)),
        }
    }
}

pub struct Tokens {
    input: Rc<str>,
    position: usize,
    read_position: usize,
    ch: Option<u8>,
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
    }

    fn peek_char(&self) -> Option<u8> {
        if self.read_position >= self.input.len() {
            None
        } else {
            Some(self.input.as_bytes()[self.read_position])
        }
    }

    fn skip_whitespace(&mut self) {
        while self.ch.unwrap_or(b'!').is_ascii_whitespace() {
            self.read_char();
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

        while let Some(b'0'..=b'9') = self.ch {
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
        self.skip_whitespace();
        let token = match self.ch {
            Some(b'=') => match self.peek_char() {
                Some(b'=') => {
                    self.read_char();
                    Token::Eq
                }
                _ => Token::Assign,
            },
            Some(b'+') => Token::Plus,
            Some(b'-') => match self.peek_char() {
                Some(b'>') => {
                    self.read_char();
                    Token::Arrow
                }
                _ => Token::Minus,
            },
            Some(b'!') => match self.peek_char() {
                Some(b'=') => {
                    self.read_char();
                    Token::NotEq
                }
                _ => Token::Bang,
            },
            Some(b'*') => Token::Asterisk,
            Some(b'<') => match self.peek_char() {
                Some(b'=') => {
                    self.read_char();
                    Token::Le
                }
                _ => Token::Lt,
            },
            Some(b'>') => match self.peek_char() {
                Some(b'=') => {
                    self.read_char();
                    Token::Ge
                }
                _ => Token::Gt,
            },
            Some(b'/') => Token::Slash,
            Some(b'%') => Token::Percent,
            Some(b'&') => match self.peek_char() {
                Some(b'&') => {
                    self.read_char();
                    Token::AmpAmp
                }
                _ => Token::Amp,
            },
            Some(b'|') => match self.peek_char() {
                Some(b'|') => {
                    self.read_char();
                    Token::BarBar
                }
                _ => Token::Bar,
            },
            Some(b'(') => Token::LParen,
            Some(b')') => Token::RParen,
            Some(b'{') => Token::LBrace,
            Some(b'}') => Token::RBrace,
            Some(b'[') => Token::LBracket,
            Some(b']') => Token::RBracket,
            Some(b',') => Token::Comma,
            Some(b':') => Token::Colon,
            Some(b';') => Token::Semicolon,
            Some(b'"') => Token::Str(self.read_string()),
            Some(c) => match c {
                (b'a'..=b'z') | (b'A'..=b'Z') | b'_' => {
                    let ident = self.read_identifier();
                    return match ident.as_ref() {
                        "fn" => Token::Fn,
                        "let" => Token::Let,
                        "true" => Token::True,
                        "false" => Token::False,
                        "if" => Token::If,
                        "else" => Token::Else,
                        "return" => Token::Return,
                        _ => Token::Ident(ident),
                    };
                }
                (b'0'..=b'9') => return Token::Int(self.read_number()),
                _ => Token::Illegal,
            },
            None => Token::None,
        };
        self.read_char();
        token
    }
}

impl Iterator for Tokens {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let tok = self.next_token();
        match tok {
            Token::None => None,
            _ => Some(tok),
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
        };
        tokens.read_char();
        tokens
    }
}

#[cfg(test)]
mod tests {
    // TODO write better tests
    use super::*;
    use Token::*;

    #[test]
    fn symbols() {
        let source = "=+-!*/(){}[],;:->&||&&";
        let expected = [
            Assign, Plus, Minus, Bang, Asterisk, Slash, LParen, RParen, LBrace, RBrace, LBracket,
            RBracket, Comma, Semicolon, Colon, Arrow, Amp, BarBar, AmpAmp,
        ];
        let mut tokens = Lexer::new(source).tokens();
        expected
            .iter()
            .for_each(|t| assert_eq!(tokens.next_token(), *t));
    }

    #[test]
    fn read_identifier() {
        let mut tokens = Lexer::new("let ").tokens();
        assert_eq!(tokens.read_identifier(), "let".into());
    }

    #[test]
    fn multichar_token() {
        Lexer::new("==").tokens().for_each(|t| assert_eq!(t, Eq));
        Lexer::new("!=").tokens().for_each(|t| assert_eq!(t, NotEq));
    }

    #[test]
    fn string() {
        let expected = [LBrace, Str("some string".into()), RBrace];
        let mut tokens = Lexer::new(r#"{"some string"}"#).tokens();
        expected
            .iter()
            .for_each(|t| assert_eq!(tokens.next_token(), *t));
    }

    #[test]
    fn code() {
        let source = r#"
                        let five = 5;
                        let ten = 10;
                        let add = fn(x, y) {
                            x + y;
                        };
                        let result = add(five, ten);
                    "#;

        #[rustfmt::skip]
        let expected = vec!{
            Let, Ident("five".into()), Assign, Int("5".into()), Semicolon,
            Let, Ident("ten".into()), Assign, Int("10".into()), Semicolon,
            Let, Ident("add".into()), Assign, Fn, LParen, Ident("x".into()), Comma, Ident("y".into()), RParen, LBrace,
            Ident("x".into()), Plus, Ident("y".into()), Semicolon,
            RBrace, Semicolon,
            Let, Ident("result".into()), Assign, Ident("add".into()), LParen, Ident("five".into()), Comma, Ident("ten".into()), RParen, Semicolon
        };

        let lexer = Lexer::new(source);
        assert_eq!(lexer.tokens().collect::<Vec<Token>>(), expected);
    }
}
