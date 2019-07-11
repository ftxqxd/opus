use std::fmt;
use std::mem;
use crate::compile::Compiler;

#[derive(Debug, Clone, PartialEq)]
pub enum Token<'source> {
    LeftParenthesis,
    RightParenthesis,
    LeftSquareBracket,
    RightSquareBracket,
    LeftBrace,
    RightBrace,
    Colon,
    ColonEquals,
    #[allow(non_camel_case_types)]
    T_PAAMAYIM_NEKUDOTAYIM,
    Equals,
    LessThan,
    GreaterThan,
    LessThanEquals,
    GreaterThanEquals,
    Plus,
    Minus,
    Asterisk,
    Slash,
    Percent,
    At,
    Tilde,
    Dot,
    Integer(u64, Option<(bool, u8)>),
    String(Box<[u8]>),
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
    Refs,
    Muts,
    Null,
    False,
    True,
    Type,
    Record,
    Is,
    And,
    Or,
    Not,
    Import,
    EndOfFile,
}

impl<'source> fmt::Display for Token<'source> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        use Token::*;
        let buffer;
        formatter.write_str(match *self {
            LeftParenthesis => "(",
            RightParenthesis => ")",
            LeftSquareBracket => "[",
            RightSquareBracket => "]",
            LeftBrace => "{",
            RightBrace => "}",
            Colon => ":",
            ColonEquals => "←",
            T_PAAMAYIM_NEKUDOTAYIM => "::",
            Equals => "=",
            LessThan => "<",
            GreaterThan => ">",
            LessThanEquals => "<=",
            GreaterThanEquals => ">=",
            Plus => "+",
            Minus => "-",
            Asterisk => "*",
            Slash => "/",
            Percent => "%",
            At => "@",
            Tilde => "¯",
            Dot => ".",
            Integer(value, None) => {
                buffer = format!("{}", value);
                &buffer
            },
            Integer(value, Some((is_signed, size))) => {
                buffer = format!("{}{}{}", value, if is_signed { "i" } else { "n" }, size);
                &buffer
            },
            String(ref bytes) => {
                buffer = format!("{}", std::string::String::from_utf8_lossy(bytes));
                &buffer
            },
            LowercaseIdentifier(s) => s,
            UppercaseIdentifier(s) => s,
            Indent => "<indent>",
            Dedent => "<dedent>",
            Var => "var",
            Return => "return",
            If => "if",
            Else => "else",
            While => "while",
            Break => "break",
            Continue => "continue",
            Extern => "extern",
            Ref => "ref",
            Mut => "mut",
            Refs => "refs",
            Muts => "muts",
            Null => "null",
            False => "false",
            True => "true",
            Type => "type",
            Is => "is",
            And => "and",
            Or => "or",
            Not => "not",
            Record => "record",
            Import => "import",
            EndOfFile => "<end of file>",
        })?;
        Ok(())
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Operator {
    Plus,
    Minus,
    Times,
    Divide,
    Modulo,
    Equals,
    LessThan,
    GreaterThan,
    LessThanEquals,
    GreaterThanEquals,
    Is,
    And,
    Or,
    Not,
}

impl Operator {
    fn binary_from_token<'source>(token: &Token<'source>) -> Option<Operator> {
        match *token {
            Token::Plus => Some(Operator::Plus),
            Token::Minus => Some(Operator::Minus),
            Token::Asterisk => Some(Operator::Times),
            Token::Slash => Some(Operator::Divide),
            Token::Percent => Some(Operator::Modulo),
            Token::Equals => Some(Operator::Equals),
            Token::LessThan => Some(Operator::LessThan),
            Token::GreaterThan => Some(Operator::GreaterThan),
            Token::LessThanEquals => Some(Operator::LessThanEquals),
            Token::GreaterThanEquals => Some(Operator::GreaterThanEquals),
            Token::Is => Some(Operator::Is),
            Token::And => Some(Operator::And),
            Token::Or => Some(Operator::Or),
            _ => None,
        }
    }

    fn unary_from_token<'source>(token: &Token<'source>) -> Option<Operator> {
        match *token {
            Token::Not => Some(Operator::Not),
            _ => None,
        }
    }

    fn precedence(&self) -> Precedence {
        match *self {
            Operator::Or => 0,
            Operator::And => 1,
            Operator::Not => 2,
            Operator::Equals => 20,
            Operator::LessThan => 20,
            Operator::GreaterThan => 20,
            Operator::LessThanEquals => 20,
            Operator::GreaterThanEquals => 20,
            Operator::Is => 20,
            Operator::Plus => 30,
            Operator::Minus => 30,
            Operator::Times => 31,
            Operator::Divide => 31,
            Operator::Modulo => 31,
        }
    }

    pub fn symbol(&self) -> &'static str {
        match *self {
            Operator::Plus => "+",
            Operator::Minus => "-",
            Operator::Times => "*",
            Operator::Divide => "/",
            Operator::Modulo => "%",

            Operator::Equals => "=",
            Operator::LessThan => "<",
            Operator::GreaterThan => ">",
            Operator::LessThanEquals => "<=",
            Operator::GreaterThanEquals => ">=",
            Operator::Is => "is",

            Operator::And => "and",
            Operator::Or => "or",
            Operator::Not => "not",
        }
    }

    pub fn is_binary(&self) -> bool {
        match *self {
            Operator::Not => false,
            _ => true,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Expression<'source> {
    Integer(u64, Option<(bool, u8)>),
    Null,
    Bool(bool),
    String(Box<[u8]>),
    Variable(&'source str),
    VariableDefinition(&'source str, Box<Expression<'source>>),
    Call(Box<FunctionName<'source>>, Vec<Box<Expression<'source>>>),
    Record(Box<Expression<'source>>, Box<[(&'source str, Box<Expression<'source>>)]>),
    Operator(Operator, Box<Expression<'source>>, Box<Expression<'source>>),
    Reference(Box<Expression<'source>>),
    MutableReference(Box<Expression<'source>>),
    ArrayReference(Box<Expression<'source>>),
    MutableArrayReference(Box<Expression<'source>>),
    Dereference(Box<Expression<'source>>),
    Field(&'source str, Box<Expression<'source>>),
    Index(Box<Expression<'source>>, Box<Expression<'source>>),
    Cast(Box<Expression<'source>>, Box<Expression<'source>>),
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
    Type(&'source str, Box<Expression<'source>>),
    Record(&'source str, Box<[(&'source str, Box<Expression<'source>>)]>),
    Import(Box<[u8]>),
}

/// The name of a function; e.g., `Foo _ _ Bar _`.
///
/// Uppercase identifiers which form parts of the name are represented by `Some(name)`; 'gaps' for
/// arguments are represented by `None`.
pub type FunctionName<'source> = [Option<&'source str>];

/// The full signature of a function (including argument names & types).
#[derive(PartialEq)]
pub struct FunctionSignature<'source> {
    /// The name of the function, i.e., its signature without its argument names & types.
    pub name: Box<FunctionName<'source>>,
    /// A list of `(name, type)` representing the names & types of the function's arguments.
    pub arguments: Vec<(&'source str, Box<Expression<'source>>)>,

    pub return_type: Box<Expression<'source>>,
}

impl<'source> fmt::Debug for FunctionSignature<'source> {
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
    UnexpectedCharacter(&'source str, char),
    UnexpectedEndOfFile(&'source str),
    InvalidEscapeSequence(&'source str),
    UnexpectedToken(&'source str, Token<'source>),
    ExpectedFoundToken { span: &'source str, expected: Token<'source>, found: Token<'source> },
    ExpectedLowercaseIdentifier(&'source str, Token<'source>),
    InvalidNumericSize(&'source str, u32),
}

type Precedence = i8;

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

        if let Some(';') = self.peek() {
            // comment!
            while let Some(c) = self.peek() {
                if c == '\n' {
                    break
                }
                self.advance();
            }
            return self.skip_whitespace()
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
            Some('[') => Ok(Token::LeftSquareBracket),
            Some(']') => Ok(Token::RightSquareBracket),
            Some('{') => Ok(Token::LeftBrace),
            Some('}') => Ok(Token::RightBrace),
            Some('←') => Ok(Token::ColonEquals),
            Some(':') => {
                match self.peek() {
                    Some('=') => {
                        self.advance();
                        Ok(Token::ColonEquals)
                    },
                    Some(':') => {
                        self.advance();
                        Ok(Token::T_PAAMAYIM_NEKUDOTAYIM)
                    },
                    _ => Ok(Token::Colon),
                }
            },
            Some('=') => Ok(Token::Equals),
            Some('<') => {
                match self.peek() {
                    Some('=') => {
                        self.advance();
                        Ok(Token::LessThanEquals)
                    },
                    _ => Ok(Token::LessThan),
                }
            },
            Some('>') => {
                match self.peek() {
                    Some('=') => {
                        self.advance();
                        Ok(Token::GreaterThanEquals)
                    },
                    _ => Ok(Token::GreaterThan),
                }
            },
            Some('+') => Ok(Token::Plus),
            Some('-') => Ok(Token::Minus),
            Some('*') => Ok(Token::Asterisk),
            Some('/') => Ok(Token::Slash),
            Some('%') => Ok(Token::Percent),
            Some('@') => Ok(Token::At),
            Some('~') | Some('¯') => Ok(Token::Tilde),
            Some('.') => Ok(Token::Dot),
            Some(c @ '0'..= '9') => {
                let mut i = c as u64 - '0' as u64;
                while let Some(c @ '0'..= '9') = self.peek() {
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
                        Some(match (self.advance(), self.peek()) {
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
                            (Some(a @ '0'..= '9'), Some(b @ '0'..= '9')) => {
                                self.advance();
                                let size = (a as u32 - '0' as u32) * 10 + b as u32 - '0' as u32;
                                let span = &self.source[old_position..self.real_position];
                                return Err(Error::InvalidNumericSize(span, size))
                            },
                            (Some(a @ '0'..= '9'), _) => {
                                let size = a as u32 - '0' as u32;
                                let span = &self.source[old_position..self.real_position];
                                return Err(Error::InvalidNumericSize(span, size))
                            },
                            _ => { self.real_position = old_position; self.position = old_position; 32 },
                        })
                    },
                    _ => None,
                };
                Ok(Token::Integer(i, size.map(|size| (signed, size))))
            },
            Some(c @ 'A'..= 'Z') | Some(c @ '\'') => {
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
            Some(c @ 'a'..= 'z') | Some(c @ '_') => {
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
                    "refs" => Ok(Token::Refs),
                    "muts" => Ok(Token::Muts),
                    "null" => Ok(Token::Null),
                    "false" => Ok(Token::False),
                    "true" => Ok(Token::True),
                    "type" => Ok(Token::Type),
                    "record" => Ok(Token::Record),
                    "is" => Ok(Token::Is),
                    "and" => Ok(Token::And),
                    "or" => Ok(Token::Or),
                    "not" => Ok(Token::Not),
                    "import" => Ok(Token::Import),
                    _ => Ok(Token::LowercaseIdentifier(identifier)),
                }
            },
            Some('"') => {
                let mut chars = vec![];
                loop {
                    let c = self.advance();
                    match c {
                        Some('"') => break,
                        Some('\\') => {
                            let escape_position = self.position;
                            let escape_code = self.advance();
                            match escape_code {
                                Some('\\') => chars.push(b'\\'),
                                Some('"') => chars.push(b'"'),
                                Some('n') => chars.push(b'\n'),
                                Some('r') => chars.push(b'\r'),
                                Some('t') => chars.push(b'\t'),
                                Some('x') => {
                                    let high_nibble = self.advance();
                                    let low_nibble = self.advance();
                                    match (high_nibble.and_then(|x| x.to_digit(16)), low_nibble.and_then(|x| x.to_digit(16))) {
                                        (Some(h), Some(l)) => {
                                            chars.push(h as u8 * 16 + l as u8);
                                        },
                                        _ => return Err(Error::InvalidEscapeSequence(&self.source[escape_position..self.position])),
                                    }
                                },
                                Some(_) => return Err(Error::InvalidEscapeSequence(self.char_at(escape_position))),
                                None => return Err(Error::UnexpectedEndOfFile(&self.source[self.position..])),
                            }
                        },
                        Some(c) => {
                            let start = chars.len();
                            chars.extend(&[0, 0, 0, 0]);
                            let length = c.encode_utf8(&mut chars[start..]).len();
                            for _ in 0..4 - length {
                                chars.pop();
                            }
                        }
                        None => return Err(Error::UnexpectedEndOfFile(&self.source[self.position..])),
                    };
                }

                Ok(Token::String(chars.into()))
            },
            Some(c) => Err(Error::UnexpectedCharacter(self.char_at(self.token_low), c)),
            None => Ok(Token::EndOfFile),
        }
    }

    fn parse_string(&mut self) -> Result<'source, Box<[u8]>> {
        match self.parse_token()? {
            Token::String(string) => Ok(string),
            token => Err(Error::UnexpectedToken(&self.source[self.token_low..self.position], token)),
        }
    }

    fn char_at(&self, position: usize) -> &'source str {
        let len = self.source[position..].chars().next().unwrap().len_utf8();
        &self.source[position..position+len]
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
            let span = &self.source[self.token_low..self.position];
            return Err(Error::ExpectedFoundToken { span, expected: expected.clone(), found })
        }

        Ok(())
    }

    fn parse_lowercase_identifier(&mut self) -> Result<'source, &'source str> {
        match self.parse_token()? {
            Token::LowercaseIdentifier(s) => Ok(s),
            t => {
                let span = &self.source[self.token_low..self.position];
                Err(Error::ExpectedLowercaseIdentifier(span, t))
            },
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

        let left_span = self.compiler.expression_span(&left);
        let low = self.string_low(left_span);

        let operator_token = self.peek_token()?;
        if let Some(operator) = Operator::binary_from_token(&operator_token) {
            let _ = self.parse_token()?;
            let right = self.parse_expression()?;

            let mut boxed_expression = Box::new(Expression::Operator(operator, left, right));
            self.correct_precedence(&mut *boxed_expression);

            self.compiler.expression_spans.insert(&*boxed_expression, &self.source[low..self.position]);

            Ok(boxed_expression)
        } else {
            Ok(left)
        }
    }

    fn correct_precedence(&mut self, expression: &mut Expression<'source>) {
        if let Expression::Operator(ref mut operator, ref mut left, ref mut right) = *expression {
            if let Expression::Operator(ref mut operator2, ref mut right_left, ref mut right_right) = **right {
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
            Token::Integer(i, meta) => {
                Expression::Integer(i, meta)
            },
            Token::String(bytes) => {
                Expression::String(bytes)
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
            Token::Refs => {
                let subexpression = self.parse_atom()?;
                Expression::ArrayReference(subexpression)
            },
            Token::Muts => {
                let subexpression = self.parse_atom()?;
                Expression::MutableArrayReference(subexpression)
            },
            Token::Var => {
                let variable_name = self.parse_lowercase_identifier()?;
                self.expect(&Token::Colon)?;
                let type_expression = self.parse_atom()?;
                Expression::VariableDefinition(variable_name, type_expression)
            },
            Token::Null => {
                Expression::Null
            },
            Token::False => {
                Expression::Bool(false)
            },
            Token::True => {
                Expression::Bool(true)
            },
            Token::Not => {
                // We treat unary operators as binary operators which ignore their first argument
                let subexpression = self.parse_expression()?;

                let null_box = Box::new(Expression::Null);
                self.compiler.expression_spans.insert(&*null_box, &self.source[low..low]);

                let mut expression_box = Box::new(Expression::Operator(Operator::Not, null_box, subexpression));
                self.correct_precedence(&mut *expression_box);
                self.compiler.expression_spans.insert(&*expression_box, &self.source[low..self.position]);
                return Ok(expression_box)
            },
            t => {
                let span = &self.source[low..self.position];
                return Err(Error::UnexpectedToken(span, t))
            },
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
                Token::Dot => {
                    let _ = self.parse_token();
                    let field_name = self.parse_lowercase_identifier()?;
                    expression_box = Box::new(Expression::Field(field_name, expression_box));
                    self.compiler.expression_spans.insert(&*expression_box, &self.source[low..self.position]);
                },
                Token::LeftSquareBracket => {
                    let _ = self.parse_token();
                    self.ignore_dents += 1;
                    let index = self.parse_expression()?;
                    self.expect(&Token::RightSquareBracket)?;
                    self.ignore_dents -= 1;
                    expression_box = Box::new(Expression::Index(expression_box, index));
                    self.compiler.expression_spans.insert(&*expression_box, &self.source[low..self.position]);
                },
                Token::LeftBrace => {
                    let _ = self.parse_token();
                    self.ignore_dents += 1;
                    let mut fields = vec![];
                    loop {
                        match self.parse_token()? {
                            Token::LowercaseIdentifier(field_name) => {
                                self.expect(&Token::ColonEquals)?;
                                let value = self.parse_expression()?;
                                fields.push((field_name, value));
                            },
                            Token::RightBrace => break,
                            token => {
                                return Err(Error::UnexpectedToken(&self.source[self.token_low..self.position], token))
                            }
                        }
                    }
                    self.ignore_dents -= 1;
                    expression_box = Box::new(Expression::Record(expression_box, fields.into()));
                    self.compiler.expression_spans.insert(&*expression_box, &self.source[low..self.position]);
                },
                Token::T_PAAMAYIM_NEKUDOTAYIM => {
                    let _ = self.parse_token();
                    let typ = self.parse_atom()?;
                    expression_box = Box::new(Expression::Cast(expression_box, typ));
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
                match self.peek_token()? {
                    Token::Colon => {
                        let _ = self.parse_token();
                        let typ = self.parse_atom()?;
                        let left_span = &self.source[low..self.position];

                        match self.peek_token()? {
                            Token::ColonEquals => {
                                let _ = self.parse_token();
                                let value = self.parse_expression()?;

                                let left = Box::new(Expression::VariableDefinition(variable_name, typ));
                                self.compiler.expression_spans.insert(&*left, left_span);
                                Statement::Assignment(left, value)
                            },
                            _ => {
                                let expression = Box::new(Expression::VariableDefinition(variable_name, typ));
                                self.compiler.expression_spans.insert(&*expression, left_span);
                                Statement::Expression(expression)
                            },
                        }
                    },
                    _ => {
                        self.expect(&Token::ColonEquals)?;
                        let value = self.parse_expression()?;
                        Statement::VariableDefinition(variable_name, value)
                    },
                }
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
                    Token::ColonEquals => {
                        // Assignment expression `a := b`
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

                Definition::Extern(signature)
            },
            Token::Type => {
                let _ = self.parse_token();
                let name = self.parse_lowercase_identifier()?;
                self.expect(&Token::ColonEquals)?;
                let typ = self.parse_atom()?;
                span = &self.source[low..self.position];

                Definition::Type(name, typ)
            },
            Token::Record => {
                let _ = self.parse_token();
                let name = self.parse_lowercase_identifier()?;
                self.expect(&Token::Indent)?;
                let mut fields = vec![];
                loop {
                    let token = self.peek_token()?;
                    if token == Token::Dedent {
                        let _ = self.parse_token();
                        break
                    }
                    let field_name = self.parse_lowercase_identifier()?;
                    self.expect(&Token::Colon)?;
                    let field_type = self.parse_atom()?;
                    fields.push((field_name, field_type));
                }
                span = &self.source[low..self.position];

                Definition::Record(name, fields.into())
            },
            Token::Import => {
                let _ = self.parse_token();
                let path = self.parse_string()?;
                span = &self.source[low..self.position];

                Definition::Import(path)
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
        let low = self.token_low;

        let mut name = vec![];
        let mut arguments = vec![];

        self.ignore_dents += 1;
        loop {
            match self.parse_token()? {
                Token::UppercaseIdentifier(part) => {
                    name.push(Some(part));
                },
                ref t if Operator::binary_from_token(t).is_some() && *t != Token::And && *t != Token::Or => {
                    let operator = Operator::binary_from_token(t).unwrap();
                    name.push(Some(operator.symbol()));
                },
                ref t if Operator::unary_from_token(t).is_some() => {
                    let operator = Operator::unary_from_token(t).unwrap();
                    name.push(Some(operator.symbol()));
                },
                Token::LowercaseIdentifier(identifier) => {
                    self.expect(&Token::Colon)?;
                    let typ = self.parse_atom()?;
                    name.push(None);
                    arguments.push((identifier, typ));
                },
                Token::RightParenthesis => break,
                t => {
                    let span = &self.source[low..self.position];
                    return Err(Error::UnexpectedToken(span, t))
                },
            }
        }
        self.ignore_dents -= 1;

        self.expect(&Token::Colon)?;
        let return_type = self.parse_atom()?;

        Ok(FunctionSignature {
            name: name.into(),
            arguments,
            return_type,
        })
    }
}
