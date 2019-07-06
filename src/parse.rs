use std::fmt;
use std::mem;
use crate::compile::Compiler;

#[derive(Debug, Clone, PartialEq)]
pub enum Token<'source> {
    LeftParenthesis,
    RightParenthesis,
    Colon,
    Equals,
    Plus,
    Minus,
    Asterisk,
    Slash,
    At,
    Tilde,
    Integer(u64, bool, u8),
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
    Extern,
    Ref,
    Mut,
    Null,
    EndOfFile,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BinaryOperator {
    Plus,
    Minus,
    Times,
    Divide,
}

impl BinaryOperator {
    fn from_token<'source>(token: &Token<'source>) -> Option<BinaryOperator> {
        match *token {
            Token::Plus => Some(BinaryOperator::Plus),
            Token::Minus => Some(BinaryOperator::Minus),
            Token::Asterisk => Some(BinaryOperator::Times),
            Token::Slash => Some(BinaryOperator::Divide),
            _ => None,
        }
    }

    fn precedence(&self) -> Precedence {
        match *self {
            BinaryOperator::Plus => 10,
            BinaryOperator::Minus => 10,
            BinaryOperator::Times => 11,
            BinaryOperator::Divide => 11,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Expression<'source> {
    Integer(u64, bool, u8),
    Null,
    Variable(&'source str),
    VariableDefinition(&'source str, Box<Expression<'source>>),
    Call(Box<FunctionName<'source>>, Vec<Box<Expression<'source>>>),
    BinaryOperator(BinaryOperator, Box<Expression<'source>>, Box<Expression<'source>>),
    Reference(Box<Expression<'source>>),
    MutableReference(Box<Expression<'source>>),
    Dereference(Box<Expression<'source>>),
    Negate(Box<Expression<'source>>),
    Parentheses(Box<Expression<'source>>),
}

#[derive(Debug)]
pub enum Statement<'source> {
    Expression(Box<Expression<'source>>),
    VariableDefinition(&'source str, Box<Expression<'source>>),
    Assignment(Box<Expression<'source>>, Box<Expression<'source>>),
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
    Extern(FunctionSignature<'source>),
}

/// The name of a function; e.g., `Foo _ _ Bar _`.
///
/// Uppercase identifiers which form parts of the name are represented by `Some(name)`; 'gaps' for
/// arguments are represented by `None`.
pub type FunctionName<'source> = [Option<&'source str>];

/// The full signature of a function (including argument names & types).
#[derive(Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
pub enum Error<'source> {
    UnexpectedCharacter(char),
    UnexpectedToken(Token<'source>),
    ExpectedFoundToken { expected: Token<'source>, found: Token<'source> },
    ExpectedLowercaseIdentifier(Token<'source>),
    InvalidExternFunctionName(FunctionSignature<'source>),
    InvalidNumericSize(u32),
}

type Precedence = i8;

#[derive(Debug)]
pub struct Parser<'compiler, 'source> {
    compiler: &'compiler mut Compiler<'source>,
    source: &'source str,
    indent: u32,
    indents_to_output: i32,
    real_position: usize,

    /// This is set once we have reached the end of the source and have emitted all necessary
    /// `Token::Dedent`s.
    is_end_of_file: bool,

    /// If this is zero, indents/dedents will *not* be ignored; otherwise, they will be.
    ignore_dents: u32,

    /// The result of the last call to `peek_token`.  If this is not `None`, `parse_token` will
    /// return this value and reset it to `None`.
    peeked_token: Option<Token<'source>>,

    /// Like `real_position`, but this value is not updated by calls to `peek_token`, instead
    /// retaining the old value until `parse_token` is called.
    position: usize,

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
            real_position: 0,
            is_end_of_file: false,
            ignore_dents: 0,
            peeked_token: None,
            position: 0,
            token_low: 0,
        }
    }

    pub fn is_at_end_of_file(&mut self) -> bool {
        self.peek_token() == Ok(Token::EndOfFile)
    }

    fn advance(&mut self) -> Option<char> {
        self.source[self.real_position..].chars().next().map(|c| {
            self.real_position += c.len_utf8();
            self.position = self.real_position;
            c
        })
    }

    fn peek(&self) -> Option<char> {
        self.source[self.real_position..].chars().next()
    }

    fn skip_whitespace(&mut self) -> i32 {
        let mut new_indent = 0;
        let mut measure_indents = self.real_position == 0;
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

        if self.source[self.real_position..].len() == 0 && !self.is_end_of_file {
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
            self.position = self.real_position;
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
            Some('+') => Ok(Token::Plus),
            Some('-') => Ok(Token::Minus),
            Some('*') => Ok(Token::Asterisk),
            Some('/') => Ok(Token::Slash),
            Some('@') => Ok(Token::At),
            Some('~') => Ok(Token::Tilde),
            Some(c @ '0'..='9') => {
                let mut i = c as u64 - '0' as u64;
                while let Some(c @ '0'..='9') = self.peek() {
                    self.advance();
                    i *= 10;
                    i += c as u64 - '0' as u64;
                }
                // look for type suffix
                let mut signed = true;
                let size = match self.peek() {
                    Some(c @ 'i') | Some(c @ 'n') => {
                        signed = c == 'i';

                        self.advance();
                        let old_position = self.real_position;
                        match (self.advance(), self.peek()) {
                            (Some('8'), _) => 8,
                            (Some('1'), Some('6')) => {
                                self.advance();
                                16
                            },
                            (Some('3'), Some('2')) => {
                                self.advance();
                                32
                            },
                            (Some('6'), Some('4')) => {
                                self.advance();
                                64
                            },
                            (Some(a @ '0'..='9'), Some(b @ '0'..='9')) => {
                                let size = (a as u32 - '0' as u32) * 10 + b as u32 - '0' as u32;
                                return Err(Error::InvalidNumericSize(size))
                            },
                            (Some(a @ '0'..='9'), _) => {
                                let size = a as u32 - '0' as u32;
                                return Err(Error::InvalidNumericSize(size))
                            },
                            _ => { self.real_position = old_position; self.position = old_position; 32 },
                        }
                    },
                    _ => 32,
                };
                Ok(Token::Integer(i, signed, size))
            },
            Some(c @ 'A'..='Z') | Some(c @ '\'') => {
                let mut byte_len = c.len_utf8();
                while let Some(c) = self.peek() {
                    if c.is_alphanumeric() || c == '\'' || c == '_' {
                        byte_len += c.len_utf8();
                        self.advance();
                    } else {
                        break;
                    }
                }
                Ok(Token::UppercaseIdentifier(&self.source[old_position..old_position + byte_len]))
            },
            Some(c @ 'a'..='z') | Some(c @ '_') => {
                let mut byte_len = c.len_utf8();
                while let Some(c) = self.peek() {
                    if c.is_alphanumeric() || c == '\'' || c == '_' {
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
                    "extern" => Ok(Token::Extern),
                    "ref" => Ok(Token::Ref),
                    "mut" => Ok(Token::Mut),
                    "null" => Ok(Token::Null),
                    _ => Ok(Token::LowercaseIdentifier(identifier)),
                }
            },
            Some(c) => Err(Error::UnexpectedCharacter(c)),
            None => Ok(Token::EndOfFile),
        }
    }

    fn peek_token(&mut self) -> Result<'source, Token<'source>> {
        let old_position = self.position;
        let token = self.parse_token()?;
        self.peeked_token = Some(token.clone());
        self.position = old_position;
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

    /// Return the position of the beginning of the given span string in this `Parser`'s source string.
    fn string_low(&self, span: &'source str) -> usize {
        let position = span as *const str as *const u8 as usize - self.source as *const str as *const u8 as usize;
        debug_assert!(position <= self.source.len());
        position
    }

    /// Return the position of the end of the given span string in this `Parser`'s source string.
    fn string_high(&self, span: &'source str) -> usize {
        span.len() + self.string_low(span)
    }

    fn parse_expression(&mut self) -> Result<'source, Box<Expression<'source>>> {
        let left = self.parse_atom()?;
        let operator_token = self.peek_token()?;
        if let Some(operator) = BinaryOperator::from_token(&operator_token) {
            let _ = self.parse_token()?;
            let right = self.parse_expression()?;

            let left_span = self.compiler.expression_span(&left);
            let low = self.string_low(left_span);

            let mut boxed_expression = Box::new(Expression::BinaryOperator(operator, left, right));
            self.correct_precedence(&mut *boxed_expression);

            self.compiler.expression_spans.insert(&*boxed_expression, &self.source[low..self.position]);

            Ok(boxed_expression)
        } else {
            Ok(left)
        }
    }

    fn correct_precedence(&mut self, expression: &mut Expression<'source>) {
        if let Expression::BinaryOperator(ref mut operator, ref mut left, ref mut right) = *expression {
            if let Expression::BinaryOperator(ref mut operator2, ref mut right_left, ref mut right_right) = **right {
                if operator.precedence() >= operator2.precedence() {
                    // These operators are out of order; swap them around!
                    //
                    // The process looks something like this:
                    //
                    //     *               +
                    //    / \             / \
                    //   a   +     =>    *   c
                    //      / \         / \
                    //     b   c       a   b

                    // First, gather some info about spans
                    let left_span = self.compiler.expression_span(&**left);
                    let low = self.string_low(left_span);
                    let right_left_span = self.compiler.expression_span(&**right_left);
                    let high = self.string_high(right_left_span);

                    // Do the swap!
                    mem::swap(operator, operator2);
                    mem::swap::<Box<_>>(left, right_left);
                    mem::swap::<Box<_>>(left, right_right);
                    mem::swap::<Box<_>>(left, right);
                    self.correct_precedence(left);

                    // Now correct the now-left sub-expression's span
                    self.compiler.expression_spans.insert(&**left, &self.source[low..high]);
                }
            }
        }
    }

    fn parse_atom(&mut self) -> Result<'source, Box<Expression<'source>>> {
        let token = self.parse_token()?;
        let low = self.token_low;

        let expression = match token {
            Token::Integer(i, signed, size) => {
                Expression::Integer(i, signed, size)
            },
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
                            break 
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
                if function_ident.len() == 1 && function_ident[0].is_none() {
                    Expression::Parentheses(args.pop().unwrap())
                } else {
                    Expression::Call(function_ident.into(), args)
                }
            },
            Token::Tilde => {
                let subexpression = self.parse_atom()?;
                Expression::Negate(subexpression)
            },
            Token::Ref => {
                let subexpression = self.parse_atom()?;
                Expression::Reference(subexpression)
            },
            Token::Mut => {
                let subexpression = self.parse_atom()?;
                Expression::MutableReference(subexpression)
            },
            Token::Var => {
                let variable_name = self.parse_lowercase_identifier()?;
                self.expect(&Token::Colon)?;
                let type_expression = self.parse_expression()?;
                Expression::VariableDefinition(variable_name, type_expression)
            },
            Token::Null => {
                Expression::Null
            },
            t => return Err(Error::UnexpectedToken(t)),
        };

        let mut expression_box = Box::new(expression);
        self.compiler.expression_spans.insert(&*expression_box, &self.source[low..self.position]);

        loop {
            match self.peek_token()? {
                Token::At => {
                    let _ = self.parse_token();
                    expression_box = Box::new(Expression::Dereference(expression_box));
                    self.compiler.expression_spans.insert(&*expression_box, &self.source[low..self.position]);
                },
                _ => break,
            }
        }

        Ok(expression_box)
    }

    fn parse_statement(&mut self) -> Result<'source, Box<Statement<'source>>> {
        let token = self.peek_token()?;
        let low = self.token_low;

        let statement = match token {
            Token::Var => {
                let _ = self.parse_token();
                let variable_name = self.parse_lowercase_identifier()?;
                self.expect(&Token::Equals)?;
                let value = self.parse_expression()?;
                Statement::VariableDefinition(variable_name, value)
            },
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
            _ => {
                let expression = self.parse_expression()?;

                match self.peek_token()? {
                    Token::Equals => {
                        // Assignment expression `a = b`
                        let _ = self.parse_token();
                        let right = self.parse_expression()?;
                        Statement::Assignment(expression, right)
                    },
                    _ => Statement::Expression(expression),
                }
            }
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
        let token = self.peek_token()?;
        let low = self.token_low;
        let span;

        let definition = match token {
            Token::Extern => {
                let _ = self.parse_token();
                let signature = self.parse_function_signature()?;
                span = &self.source[low..self.position];

                if signature.name.len() == 0
                || !signature.name[1..].iter().all(|x| x.is_none())
                || signature.name[0].is_none()
                || signature.name[0].as_ref().unwrap().chars().next() != Some('\'') {
                    return Err(Error::InvalidExternFunctionName(signature))
                }

                Definition::Extern(signature)
            },
            _ => {
                let signature = self.parse_function_signature()?;
                span = &self.source[low..self.position];
                let body = self.parse_block()?;

                Definition::Function(signature, body)
            },
        };

        let definition_boxed = Box::new(definition);

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
