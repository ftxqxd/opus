use std::fmt;
use std::cell::Cell;
use std::collections::HashMap;
use crate::parse::{FunctionName, FunctionNameDisplayer, Definition, Expression, Statement};
use crate::frontend::Options;

#[derive(Debug)]
pub struct Compiler<'source> {
    pub resolution_map: HashMap<&'source FunctionName<'source>, Function>,
    pub has_errors: Cell<bool>,

    pub expression_spans: HashMap<*const Expression<'source>, &'source str>,
    pub statement_spans: HashMap<*const Statement<'source>, &'source str>,
    pub definition_spans: HashMap<*const Definition<'source>, &'source str>,

    pub options: Options,

    pub source: &'source str,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Integer8,
    Integer16,
    Integer32,
    Integer64,
    Natural8,
    Natural16,
    Natural32,
    Natural64,
    Bool,
    Null,
    Reference(Box<Type>),
    MutableReference(Box<Type>),
    Error,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: Box<[Option<Box<str>>]>,
    pub arguments: Box<[Type]>,
    pub return_type: Type,
    pub is_extern: bool,
}

impl fmt::Display for Function {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "(")?;

        let mut i = 0;

        let mut written_anything = false;

        for part in self.name.iter() {
            if written_anything {
                write!(formatter, " ")?;
            }

            match *part {
                Some(ref x) => write!(formatter, "{}", x)?,
                None => {
                    write!(formatter, ":{}", self.arguments[i])?;
                    i += 1;
                },
            }

            written_anything = true;
        }

        write!(formatter, ")")?;

        write!(formatter, ": {}", self.return_type)
    }
}

#[derive(Debug)]
pub enum Error<'source> {
    ParseError(crate::parse::Error<'source>),
    UndefinedVariable(&'source str),
    ShadowedName(&'source str),
    UndefinedFunction(&'source str, &'source FunctionName<'source>),
    UnexpectedType { span: &'source str, expected: Type, found: Type },
    InvalidOperandTypes { span: &'source str, left: Type, right: Type },
    InvalidOperandType { span: &'source str, typ: Type },
    FunctionMightNotReturn(&'source str),
    BreakOutsideLoop(&'source str),
    ContinueOutsideLoop(&'source str),
    InvalidLvalue(&'source str),
    ImmutableLvalue(&'source str),
    InvalidCast { span: &'source str, from: Type, to: Type },
    InvalidExternFunctionName(&'source str, Function),
}

impl Type {
    pub fn can_autocast_to(&self, other: &Type) -> bool {
        if self == other {
            return true
        }

        match (self, other) {
            // errors
            (&Type::Error, _)
            | (_, &Type::Error)
            // integer upcasts
            | (&Type::Integer8, &Type::Integer64)
            | (&Type::Integer16, &Type::Integer64)
            | (&Type::Integer32, &Type::Integer64)
            | (&Type::Integer8, &Type::Integer32)
            | (&Type::Integer16, &Type::Integer32)
            | (&Type::Integer8, &Type::Integer16)
            // natural upcasts
            | (&Type::Natural8, &Type::Natural64)
            | (&Type::Natural16, &Type::Natural64)
            | (&Type::Natural32, &Type::Natural64)
            | (&Type::Natural8, &Type::Natural32)
            | (&Type::Natural16, &Type::Natural32)
            | (&Type::Natural8, &Type::Natural16)
            // natural -> integer upcasts
            | (&Type::Natural8, &Type::Integer64)
            | (&Type::Natural16, &Type::Integer64)
            | (&Type::Natural32, &Type::Integer64)
            | (&Type::Natural8, &Type::Integer32)
            | (&Type::Natural16, &Type::Integer32)
            | (&Type::Natural8, &Type::Integer16)
              => true,
            // mut -> ref
            (&Type::MutableReference(ref typ1), &Type::Reference(ref typ2)) if typ1 == typ2
              => true,
            _ => false,
        }
    }

    pub fn can_cast_to(&self, other: &Type) -> bool {
        if self.can_autocast_to(other) {
            true
        } else {
            match (self, other) {
                (_, _) if self.is_integral() && other.is_integral() => true,
                (&Type::Reference(_), &Type::Reference(_))
                | (&Type::MutableReference(_), &Type::MutableReference(_)) => true,
                _ => false,
            }
        }
    }

    pub fn is_integral(&self) -> bool {
        match *self {
            Type::Natural8 | Type::Natural16 | Type::Natural32 | Type::Natural64
            | Type::Integer8 | Type::Integer16 | Type::Integer32 | Type::Integer64 => true,
            _ => false,
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let string = match *self {
            Type::Integer8 => "int8",
            Type::Integer16 => "int16",
            Type::Integer32 => "int32",
            Type::Integer64 => "int64",
            Type::Natural8 => "nat8",
            Type::Natural16 => "nat16",
            Type::Natural32 => "nat32",
            Type::Natural64 => "nat64",
            Type::Bool => "bool",
            Type::Null => "null",
            Type::Reference(ref subtype) => {
                write!(formatter, "ref {}", subtype)?;
                ""
            },
            Type::MutableReference(ref subtype) => {
                write!(formatter, "mut {}", subtype)?;
                ""
            },
            Type::Error => "<error>",
        };

        write!(formatter, "{}", string)
    }
}

impl<'source> Compiler<'source> {
    pub fn with_options(options: Options, source: &'source str) -> Self {
        let mut resolution_map: HashMap<&FunctionName, _> = HashMap::new();
        static PRINT_NAME: [Option<&'static str>; 2] = [Some("Print"), None];
        let print_function = Function {
            name: Box::new([Some("Print".into()), None]),
            arguments: Box::new([Type::Integer64]),
            return_type: Type::Null,
            is_extern: false,
        };
        resolution_map.insert(&PRINT_NAME, print_function);
        Self {
            resolution_map,
            has_errors: Cell::new(false),
            expression_spans: HashMap::new(),
            statement_spans: HashMap::new(),
            definition_spans: HashMap::new(),
            options,
            source,
        }
    }

    pub fn report_error(&self, error: Error<'source>) {
        self.print_error(&error);
        self.has_errors.set(true);
    }

    pub fn print_error(&self, error: &Error) {
        use Error::*;
        use crate::frontend::print_span;
        use crate::parse::Error::*;
        eprint!("Error: ");
        match *error {
            ParseError(UnexpectedCharacter(span, c)) => {
                eprintln!("unexpected character: {}", c);
                print_span(self.source, span);
            },
            ParseError(UnexpectedToken(span, ref token)) => {
                eprintln!("unexpected token: {}", token);
                print_span(self.source, span);
            },
            ParseError(ExpectedFoundToken { span, ref expected, ref found }) => {
                eprintln!("unexpected token: expected {}, found {}", expected, found);
                print_span(self.source, span);
            },
            ParseError(ExpectedLowercaseIdentifier(span, ref token)) => {
                eprintln!("unexpected token: expected lowercase identifier, found {}", token);
                print_span(self.source, span);
            },
            ParseError(InvalidNumericSize(span, size)) => {
                eprintln!("invalid numeric size: {}", size);
                print_span(self.source, span);
            },
            UndefinedVariable(span) => {
                eprintln!("undefined variable: {}", span);
                print_span(self.source, span);
            },
            ShadowedName(span) => {
                eprintln!("shadowed variable: {}", span);
                print_span(self.source, span);
            },
            UndefinedFunction(span, name) => {
                eprintln!("undefined function: {}", FunctionNameDisplayer(name));
                print_span(self.source, span);
            },
            UnexpectedType { span, ref expected, ref found } => {
                eprintln!("invalid type: expected {}, found {}", expected, found);
                print_span(self.source, span);
            },
            InvalidOperandTypes { span, ref left, ref right } => {
                eprintln!("invalid operand types: {}, {}", left, right);
                print_span(self.source, span);
            },
            InvalidOperandType { span, ref typ } => {
                eprintln!("invalid operand type: {}", typ);
                print_span(self.source, span);
            },
            FunctionMightNotReturn(span) => {
                eprintln!("function might not return");
                print_span(self.source, span);
            },
            BreakOutsideLoop(span) => {
                eprintln!("break outside loop");
                print_span(self.source, span);
            },
            ContinueOutsideLoop(span) => {
                eprintln!("continue outside loop");
                print_span(self.source, span);
            },
            InvalidLvalue(span) => {
                eprintln!("invalid lvalue");
                print_span(self.source, span);
            },
            ImmutableLvalue(span) => {
                eprintln!("lvalue is immutable");
                print_span(self.source, span);
            },
            InvalidCast { span, ref from, ref to } => {
                eprintln!("invalid cast: {} to {}", from, to);
                print_span(self.source, span);
            },
            InvalidExternFunctionName(span, ref signature) => {
                eprintln!("invalid extern function signature: {}", signature);
                print_span(self.source, span);
            },
        }
    }

    pub fn resolve_type(&self, typ: &Expression) -> Type {
        match *typ {
            Expression::Variable("int8") => Type::Integer8,
            Expression::Variable("int16") => Type::Integer16,
            Expression::Variable("int32") => Type::Integer32,
            Expression::Variable("int64") => Type::Integer64,
            Expression::Variable("nat8") => Type::Natural8,
            Expression::Variable("nat16") => Type::Natural16,
            Expression::Variable("nat32") => Type::Natural32,
            Expression::Variable("nat64") => Type::Natural64,
            Expression::Variable("bool") => Type::Bool,
            Expression::Null => Type::Null,
            Expression::Reference(ref subexpression) => Type::Reference(Box::new(self.resolve_type(subexpression))),
            Expression::MutableReference(ref subexpression) => Type::MutableReference(Box::new(self.resolve_type(subexpression))),
            _ => Type::Error,
        }
    }

    pub fn parse_definition(&mut self, definition: &'source Definition<'source>) {
        match *definition {
            Definition::Function(ref signature, ..) | Definition::Extern(ref signature) => {
                let name = signature.name.iter().map(|part| part.map(|x| x.into())).collect();
                let arguments = signature.arguments.iter().map(|&(_, ref type_expression)| self.resolve_type(type_expression)).collect();
                let return_type = self.resolve_type(&signature.return_type);

                let is_extern = if let Definition::Extern(..) = *definition {
                    true
                } else {
                    false
                };

                let function = Function { name, arguments, return_type, is_extern };

                if is_extern
                && (signature.name.len() == 0
                    || !signature.name[1..].iter().all(|x| x.is_none())
                    || signature.name[0].is_none()
                    || signature.name[0].as_ref().unwrap().chars().next() != Some('\''))
                {
                    let span = self.definition_span(definition);
                    self.report_error(Error::InvalidExternFunctionName(span, function.clone()));
                }

                self.resolution_map.insert(&signature.name, function);
            },
        }
    }

    pub fn statement_span(&self, statement: &Statement<'source>) -> &'source str {
        self.statement_spans[&(statement as *const _)]
    }

    pub fn expression_span(&self, expression: &Expression<'source>) -> &'source str {
        self.expression_spans[&(expression as *const _)]
    }

    pub fn definition_span(&self, definition: &Definition<'source>) -> &'source str {
        self.definition_spans[&(definition as *const _)]
    }
}
