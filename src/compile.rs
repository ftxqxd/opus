use std::fmt;
use std::cell::Cell;
use std::collections::HashMap;
use crate::parse::{FunctionName, Definition, Expression, Statement};

#[derive(Debug)]
pub struct Compiler<'source> {
    pub resolution_map: HashMap<&'source FunctionName<'source>, Function>,
    pub has_errors: Cell<bool>,

    pub expression_spans: HashMap<*const Expression<'source>, &'source str>,
    pub statement_spans: HashMap<*const Statement<'source>, &'source str>,
    pub definition_spans: HashMap<*const Definition<'source>, &'source str>,
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
    Null,
    Pointer(Box<Type>),
    Error,
}

#[derive(Debug)]
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
                    // FIXME: implement Display for Type
                    write!(formatter, ":{:?}", self.arguments[i])?;
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
            _ => false,
        }
    }
}

impl<'source> Compiler<'source> {
    pub fn new() -> Self {
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
        }
    }

    pub fn report_error(&self, error: Error<'source>) {
        eprintln!("{:?}", error);
        self.has_errors.set(true);
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
            Expression::Variable("null") => Type::Null,
            Expression::Reference(ref subexpression) => Type::Pointer(Box::new(self.resolve_type(subexpression))),
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
}
