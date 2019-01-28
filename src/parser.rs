#[derive(Debug)]
pub enum Token<'src> {
    LeftParenthesis,
    RightParenthesis,
    Integer(u64),
    LowercaseIdentifier(&'src str),
    UppercaseIdentifier(&'src str),
    Indent,
    Dedent,
}

#[derive(Debug)]
pub enum Expression<'src> {
    Integer(u64),
    Variable(&'src str),
    Call(FunctionIdentifier<'src>, Vec<Expression<'src>>),
}

/// An identifier that represents a function; e.g., `Foo _ _ Bar _`.
///
/// Upper-cased identifiers which form parts of the name are represented by `Some(name)`; 'gaps'
/// for arguments are represented by `None`.
pub type FunctionIdentifier<'src> = Vec<Option<&'src str>>;

#[derive(Debug)]
pub enum Error<'src> {
    UnexpectedCharacter(char),
    UnexpectedEof,
    UnexpectedToken(Token<'src>),
    InvalidIndent,
}

#[derive(Debug, Clone)]
pub struct Parser<'src> {
    src: &'src str,
    indent: u32,
    indents_to_output: i32,
    is_start_of_file: bool,
    ignore_dents: bool,
}

pub type Result<'src, T> = std::result::Result<T, Error<'src>>;

impl<'src> Parser<'src> {
    pub fn from_src(src: &'src str) -> Self {
        Self {
            src,
            indent: 0,
            indents_to_output: 0,
            is_start_of_file: true,
            ignore_dents: false,
        }
    }

    fn advance(&mut self) -> Option<char> {
        self.is_start_of_file = false;
        self.src.chars().next().map(|c| {
            self.src = &self.src[c.len_utf8()..];
            c
        })
    }

    fn peek(&self) -> Option<char> {
        self.src.chars().next()
    }

    fn skip_whitespace(&mut self) -> i32 {
        let mut new_indent = 0;
        let mut measure_indents = self.is_start_of_file;
        let mut check_indent = measure_indents;

        while let Some(c) = self.peek().filter(|&x| x.is_whitespace()) {
            if !self.ignore_dents {
                if c == '\n' {
                    new_indent = 0;
                    measure_indents = true;
                    check_indent = true;
                } else if measure_indents {
                    if c == '\t' {
                        new_indent += 1;
                    } else {
                        measure_indents = false;
                    }
                }
            }

            self.advance();
        }

        let ret;
        if check_indent {
            ret = new_indent as i32 - self.indent as i32;
            self.indent = new_indent;
        } else {
            ret = 0;
        };

        while self.peek().filter(|&x| x != '\n' && x.is_whitespace()).is_some() {
            self.advance();
        }

        ret
    }

    pub fn parse_token(&mut self) -> Result<'src, Token<'src>> {
        if self.ignore_dents {
            self.skip_whitespace();
        } else if self.indents_to_output == 0 {
            self.indents_to_output = self.skip_whitespace();
        }

        if self.indents_to_output > 0 {
            self.indents_to_output -= 1;
            return Ok(Token::Indent)
        } else if self.indents_to_output < 0 {
            self.indents_to_output += 1;
            return Ok(Token::Dedent)
        }

        let old_src = self.src;
        match self.advance() {
            Some('(') => Ok(Token::LeftParenthesis),
            Some(')') => Ok(Token::RightParenthesis),
            Some(c @ '0'...'9') => {
                let mut i = c as u64 - '0' as u64;
                while let Some(c @ '0'...'9') = self.peek() {
                    self.advance();
                    i *= 10;
                    i += c as u64 - '0' as u64;
                }
                Ok(Token::Integer(i))
            },
            Some(c @ 'A'...'Z') => {
                let mut byte_len = c.len_utf8();
                while let Some(c) = self.peek() {
                    if c.is_alphanumeric() {
                        byte_len += c.len_utf8();
                        self.advance();
                    } else {
                        break;
                    }
                }
                Ok(Token::UppercaseIdentifier(&old_src[0..byte_len]))
            },
            Some(c @ 'a'...'z') => {
                let mut byte_len = c.len_utf8();
                while let Some(c) = self.peek() {
                    if c.is_alphanumeric() {
                        byte_len += c.len_utf8();
                        self.advance();
                    } else {
                        break;
                    }
                }
                Ok(Token::LowercaseIdentifier(&old_src[0..byte_len]))
            },
            Some(c) => Err(Error::UnexpectedCharacter(c)),
            None => Err(Error::UnexpectedEof),
        }
    }

    // In theory, we shouldn't need self to be &mut here, but it's easier
    // if it is and isn't a problem in practice.
    fn peek_token(&self) -> Result<'src, Token<'src>> {
        let mut other = self.clone();
        other.parse_token()
    }

    pub fn parse_expression(&mut self) -> Result<'src, Expression<'src>> {
        match self.parse_token()? {
            Token::Integer(i) => Ok(Expression::Integer(i)),
            Token::LowercaseIdentifier(s) => Ok(Expression::Variable(s)),
            Token::LeftParenthesis => {
                self.ignore_dents = true;
                let mut function_ident = vec![];
                let mut args = vec![];
                loop {
                    let token = self.peek_token()?;
                    match token {
                        Token::RightParenthesis => {
                            let _ = self.parse_token();
                            self.ignore_dents = false;
                            break Ok(Expression::Call(function_ident, args))
                        },
                        Token::UppercaseIdentifier(s) => {
                            let _ = self.parse_token();
                            function_ident.push(Some(s));
                        },
                        _ => {
                            args.push(self.parse_expression()?);
                            function_ident.push(None);
                        },
                    }
                }
            },
            t => Err(Error::UnexpectedToken(t)),
        }
    }
}
