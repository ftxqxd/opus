use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Token<'source> {
    LeftParenthesis,
    RightParenthesis,
    Colon,
    Equals,
    Integer(u64),
    LowercaseIdentifier(&'source str),
    UppercaseIdentifier(&'source str),
    Indent,
    Dedent,
    Var,
}

#[derive(Debug)]
pub enum Expression<'source> {
    Integer(u64),
    Variable(&'source str),
    Call(Box<FunctionName<'source>>, Vec<Expression<'source>>),
    Assignment(&'source str, Box<Expression<'source>>),
}

pub type Block<'source> = [Expression<'source>];

#[derive(Debug)]
pub enum Definition<'source> {
    Function(FunctionSignature<'source>, Box<Block<'source>>),
}

/// The name of a function; e.g., `Foo _ _ Bar _`.
///
/// Uppercase identifiers which form parts of the name are represented by `Some(name)`; 'gaps' for
/// arguments are represented by `None`.
pub type FunctionName<'source> = [Option<&'source str>];

/// The full signature of a function (including argument names & types).
#[derive(Debug)]
pub struct FunctionSignature<'source> {
    /// The name of the function, i.e., its signature without its argument names & types.
    pub name: Box<FunctionName<'source>>,
    /// A list of `(name, type)` representing the names & types of the function's arguments.
    pub arguments: Vec<(&'source str, Expression<'source>)>,

    pub return_type: Expression<'source>,
}

impl<'source> fmt::Display for FunctionSignature<'source> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "(")?;

        let mut i = 0;

        let mut written_anything = false;

        for part in self.name.iter() {
            if written_anything {
                write!(formatter, " ")?;
            }

            match *part {
                Some(x) => write!(formatter, "{}", x)?,
                None => {
                    // FIXME: implement Display for Expression
                    write!(formatter, "{}: {:?}", self.arguments[i].0, self.arguments[i].1)?;
                    i += 1;
                },
            }

            written_anything = true;
        }

        write!(formatter, ")")
    }
}

#[derive(Debug)]
pub enum Error<'source> {
    UnexpectedCharacter(char),
    UnexpectedEof,
    UnexpectedToken(Token<'source>),
    ExpectedFoundToken { expected: Token<'source>, found: Token<'source> },
    ExpectedLowercaseIdentifier(Token<'source>),
}

#[derive(Debug, Clone)]
pub struct Parser<'source> {
    source: &'source str,
    indent: u32,
    indents_to_output: i32,
    is_start_of_file: bool,

    /// This is set once we have reached the end of the source and have emitted all necessary
    /// `Token::Dedent`s.
    is_end_of_file: bool,

    /// If this is zero, indents/dedents will *not* be ignored; otherwise, they will be.
    ignore_dents: u32,
}

pub type Result<'source, T> = std::result::Result<T, Error<'source>>;

impl<'source> Parser<'source> {
    pub fn from_source(source: &'source str) -> Self {
        Self {
            source,
            indent: 0,
            indents_to_output: 0,
            is_start_of_file: true,
            is_end_of_file: false,
            ignore_dents: 0,
        }
    }

    fn advance(&mut self) -> Option<char> {
        self.is_start_of_file = false;
        self.source.chars().next().map(|c| {
            self.source = &self.source[c.len_utf8()..];
            c
        })
    }

    fn peek(&self) -> Option<char> {
        self.source.chars().next()
    }

    fn skip_whitespace(&mut self) -> i32 {
        let mut new_indent = 0;
        let mut measure_indents = self.is_start_of_file;
        let mut check_indent = measure_indents;

        while let Some(c) = self.peek().filter(|&x| x.is_whitespace()) {
            if self.ignore_dents == 0 {
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

        if self.source.len() == 0 && !self.is_end_of_file {
            self.is_end_of_file = true;
            return -(self.indent as i32)
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

    pub fn parse_token(&mut self) -> Result<'source, Token<'source>> {
        if self.ignore_dents > 0 {
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

        let old_source = self.source;
        match self.advance() {
            Some('(') => Ok(Token::LeftParenthesis),
            Some(')') => Ok(Token::RightParenthesis),
            Some(':') => Ok(Token::Colon),
            Some('=') => Ok(Token::Equals),
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
                Ok(Token::UppercaseIdentifier(&old_source[0..byte_len]))
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
                let identifier = &old_source[0..byte_len];
                match identifier {
                    "var" => Ok(Token::Var),
                    _ => Ok(Token::LowercaseIdentifier(identifier)),
                }
            },
            Some(c) => Err(Error::UnexpectedCharacter(c)),
            None => Err(Error::UnexpectedEof),
        }
    }

    // In theory, we shouldn't need self to be &mut here, but it's easier
    // if it is and isn't a problem in practice.
    fn peek_token(&self) -> Result<'source, Token<'source>> {
        let mut other = self.clone();
        other.parse_token()
    }

    fn expect(&mut self, expected: &Token<'source>) -> Result<'source, ()> {
        let found = self.parse_token()?;
        if *expected != found {
            return Err(Error::ExpectedFoundToken { expected: expected.clone(), found })
        }

        Ok(())
    }

    fn parse_lowercase_identifier(&mut self) -> Result<'source, &'source str> {
        match self.parse_token()? {
            Token::LowercaseIdentifier(s) => Ok(s),
            t => Err(Error::ExpectedLowercaseIdentifier(t))
        }
    }

    pub fn parse_expression(&mut self) -> Result<'source, Expression<'source>> {
        match self.parse_token()? {
            Token::Integer(i) => Ok(Expression::Integer(i)),
            Token::LowercaseIdentifier(s) => Ok(Expression::Variable(s)),
            Token::LeftParenthesis => {
                self.ignore_dents += 1;
                let mut function_ident = vec![];
                let mut args = vec![];
                loop {
                    let token = self.peek_token()?;
                    match token {
                        Token::RightParenthesis => {
                            let _ = self.parse_token();
                            self.ignore_dents -= 1;
                            break Ok(Expression::Call(function_ident.into(), args))
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
            Token::Var => {
                let variable_name = self.parse_lowercase_identifier()?;
                self.expect(&Token::Equals)?;
                let value = self.parse_expression()?;
                Ok(Expression::Assignment(variable_name, Box::new(value)))
            },
            t => Err(Error::UnexpectedToken(t)),
        }
    }

    /// Parse a block, including its opening `Indent` and closing `Dedent` tokens.
    fn parse_block(&mut self) -> Result<'source, Box<Block<'source>>> {
        let mut expressions = vec![];

        self.expect(&Token::Indent)?;
        loop {
            match self.peek_token()? {
                Token::Dedent => break,
                _ => expressions.push(self.parse_expression()?),
            }
        }
        let _ = self.parse_token(); // Skip past the Token::Dedent

        Ok(expressions.into())
    }

    pub fn parse_definition(&mut self) -> Result<'source, Definition<'source>> {
        let signature = self.parse_function_signature()?;
        let body = self.parse_block()?;
        Ok(Definition::Function(signature, body))
    }

    fn parse_function_signature(&mut self) -> Result<'source, FunctionSignature<'source>> {
        self.expect(&Token::LeftParenthesis)?;

        let mut name = vec![];
        let mut arguments = vec![];

        self.ignore_dents += 1;
        loop {
            match self.parse_token()? {
                Token::UppercaseIdentifier(part) => {
                    name.push(Some(part));
                },
                Token::LowercaseIdentifier(identifier) => {
                    self.expect(&Token::Colon)?;
                    let typ = self.parse_expression()?;
                    name.push(None);
                    arguments.push((identifier, typ));
                },
                Token::RightParenthesis => break,
                t => return Err(Error::UnexpectedToken(t)),
            }
        }
        self.ignore_dents -= 1;

        self.expect(&Token::Colon)?;
        let return_type = self.parse_expression()?;

        Ok(FunctionSignature {
            name: name.into(),
            arguments,
            return_type,
        })
    }
}
