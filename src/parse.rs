use crate::compile::Compiler;
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
    Return,
    If,
    Else,
    While,
    Break,
    Continue,
}

#[derive(Debug)]
pub enum Expression<'source> {
    Integer(u64),
    Variable(&'source str),
    Call(Box<FunctionName<'source>>, Vec<Box<Expression<'source>>>),
    Assignment(&'source str, Box<Expression<'source>>),
}

#[derive(Debug)]
pub enum Statement<'source> {
    Expression(Box<Expression<'source>>),
    Return(Box<Expression<'source>>),
    If(Box<Expression<'source>>, Box<Block<'source>>, Box<Block<'source>>),
    While(Box<Expression<'source>>, Box<Block<'source>>, Box<Block<'source>>),
    Break,
    Continue,
}

pub type Block<'source> = [Box<Statement<'source>>];

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
    pub arguments: Vec<(&'source str, Box<Expression<'source>>)>,

    pub return_type: Box<Expression<'source>>,
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

#[derive(Debug)]
pub struct Parser<'compiler, 'source> {
    compiler: &'compiler mut Compiler<'source>,
    source: &'source str,
    indent: u32,
    indents_to_output: i32,
    position: usize,

    /// This is set once we have reached the end of the source and have emitted all necessary
    /// `Token::Dedent`s.
    is_end_of_file: bool,

    /// If this is zero, indents/dedents will *not* be ignored; otherwise, they will be.
    ignore_dents: u32,

    /// The result of the last call to `peek_token`.  If this is not `None`, `parse_token` will
    /// return this value and reset it to `None`.
    peeked_token: Option<Token<'source>>,

    /// The position of the beginning of the last token parsed, not including whitespace.  Used for
    /// spans.
    ///
    /// Note: this is set by `peek_token` as well as `parse_token`.
    token_low: usize,
}

pub type Result<'source, T> = std::result::Result<T, Error<'source>>;

impl<'source, 'compiler> Parser<'compiler, 'source> {
    pub fn from_source(compiler: &'compiler mut Compiler<'source>, source: &'source str) -> Self {
        Self {
            compiler,
            source,
            indent: 0,
            indents_to_output: 0,
            position: 0,
            is_end_of_file: false,
            ignore_dents: 0,
            peeked_token: None,
            token_low: 0,
        }
    }

    fn advance(&mut self) -> Option<char> {
        self.source[self.position..].chars().next().map(|c| {
            self.position += c.len_utf8();
            c
        })
    }

    fn peek(&self) -> Option<char> {
        self.source[self.position..].chars().next()
    }

    fn skip_whitespace(&mut self) -> i32 {
        let mut new_indent = 0;
        let mut measure_indents = self.position == 0;
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

        if self.source[self.position..].len() == 0 && !self.is_end_of_file {
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
        if let Some(token) = self.peeked_token.take() {
            return Ok(token)
        }

        if self.ignore_dents > 0 {
            self.skip_whitespace();
        } else if self.indents_to_output == 0 {
            self.indents_to_output = self.skip_whitespace();
        }

        self.token_low = self.position;

        if self.indents_to_output > 0 {
            self.indents_to_output -= 1;
            return Ok(Token::Indent)
        } else if self.indents_to_output < 0 {
            self.indents_to_output += 1;
            return Ok(Token::Dedent)
        }

        let old_position = self.position;
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
                Ok(Token::UppercaseIdentifier(&self.source[old_position..old_position + byte_len]))
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
                let identifier = &self.source[old_position..old_position + byte_len];
                match identifier {
                    "var" => Ok(Token::Var),
                    "return" => Ok(Token::Return),
                    "if" => Ok(Token::If),
                    "else" => Ok(Token::Else),
                    "while" => Ok(Token::While),
                    "break" => Ok(Token::Break),
                    "continue" => Ok(Token::Continue),
                    _ => Ok(Token::LowercaseIdentifier(identifier)),
                }
            },
            Some(c) => Err(Error::UnexpectedCharacter(c)),
            None => Err(Error::UnexpectedEof),
        }
    }

    fn peek_token(&mut self) -> Result<'source, Token<'source>> {
        let token = self.parse_token()?;
        self.peeked_token = Some(token.clone());
        Ok(token)
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

    fn parse_expression(&mut self) -> Result<'source, Box<Expression<'source>>> {
        let token = self.parse_token()?;
        let low = self.token_low;

        let expression = match token {
            Token::Integer(i) => Expression::Integer(i),
            Token::LowercaseIdentifier(s) => Expression::Variable(s),
            Token::LeftParenthesis => {
                self.ignore_dents += 1;
                let mut function_ident = vec![];
                let mut args = vec![];
                loop {
                    let token2 = self.peek_token()?;
                    match token2 {
                        Token::RightParenthesis => {
                            let _ = self.parse_token();
                            self.ignore_dents -= 1;
                            break Expression::Call(function_ident.into(), args)
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
                Expression::Assignment(variable_name, value)
            },
            t => return Err(Error::UnexpectedToken(t)),
        };

        let expression_box = Box::new(expression);
        self.compiler.expression_spans.insert(&*expression_box, &self.source[low..self.position]);

        Ok(expression_box)
    }

    fn parse_statement(&mut self) -> Result<'source, Box<Statement<'source>>> {
        let token = self.peek_token()?;
        let low = self.token_low;

        let statement = match token {
            Token::Return => {
                let _ = self.parse_token();
                Statement::Return(self.parse_expression()?)
            },
            Token::If | Token::While => {
                let _ = self.parse_token();
                let condition = self.parse_expression()?;
                let then = self.parse_block()?;

                let els: Box<Block>;
                if let Ok(Token::Else) = self.peek_token() {
                    let _ = self.parse_token();
                    els = self.parse_block()?;
                } else {
                    els = Box::new([]);
                }

                (match token {
                    Token::If => Statement::If,
                    Token::While => Statement::While,
                    _ => unreachable!(),
                })(condition, then, els)
            },
            Token::Break => {
                let _ = self.parse_token();
                Statement::Break
            },
            Token::Continue => {
                let _ = self.parse_token();
                Statement::Continue
            },
            _ => Statement::Expression(self.parse_expression()?),
        };

        let boxed_statement = Box::new(statement);
        self.compiler.statement_spans.insert(&*boxed_statement, &self.source[low..self.position]);

        Ok(boxed_statement)
    }

    /// Parse a block, including its opening `Indent` and closing `Dedent` tokens.
    fn parse_block(&mut self) -> Result<'source, Box<Block<'source>>> {
        let mut statements = vec![];

        match self.peek_token()? {
            Token::Indent => {
                let _ = self.parse_token();
            },
            _ => {
                // Allow single-statement blocks
                return Ok(Box::new([self.parse_statement()?]))
            }
        }

        loop {
            match self.peek_token()? {
                Token::Dedent => break,
                _ => statements.push(self.parse_statement()?),
            }
        }
        let _ = self.parse_token(); // Skip past the Token::Dedent

        Ok(statements.into())
    }

    pub fn parse_definition(&mut self) -> Result<'source, Box<Definition<'source>>> {
        let _ = self.peek_token()?; // set token_low
        let low = self.token_low;

        let signature = self.parse_function_signature()?;
        let span = &self.source[low..self.position];
        let body = self.parse_block()?;

        let definition_boxed = Box::new(Definition::Function(signature, body));

        self.compiler.definition_spans.insert(&*definition_boxed, span);

        Ok(definition_boxed)
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
