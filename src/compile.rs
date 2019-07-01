use std::fmt;
use std::cell::Cell;
use std::collections::HashMap;
use crate::parse::{FunctionName, Definition, Expression};

#[derive(Debug)]
pub struct Compiler<'source> {
    pub resolution_map: HashMap<&'source FunctionName<'source>, Function>,
    pub has_errors: Cell<bool>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Integer64,
    Natural64,
    Null,
    Error,
}

#[derive(Debug)]
pub struct Function {
    pub name: Box<[Option<Box<str>>]>,
    pub arguments: Box<[Type]>,
    pub return_type: Type,
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
    EmptyBlock,
    UndefinedVariable(&'source str),
    UndefinedFunction(&'source FunctionName<'source>),
    UnexpectedType { expected: Type, found: Type },
}

impl Type {
    pub fn can_unify_with(&self, other: &Type) -> bool {
        if *self == Type::Error || *other == Type::Error {
            return true
        }
        self == other
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
        };
        resolution_map.insert(&PRINT_NAME, print_function);
        Self {
            resolution_map,
            has_errors: Cell::new(false),
        }
    }

    pub fn report_error(&self, error: Error<'source>) {
        eprintln!("{:?}", error);
        self.has_errors.set(true);
    }

    pub fn resolve_type(&self, typ: &Expression) -> Type {
        match *typ {
            Expression::Variable("int64") => Type::Integer64,
            Expression::Variable("nat64") => Type::Natural64,
            Expression::Variable("null") => Type::Null,
            _ => Type::Error,
        }
    }

    pub fn parse_definition(&mut self, definition: &'source Definition<'source>) {
        match definition {
            Definition::Function(ref signature, ..) => {
                let name = signature.name.iter().map(|part| part.map(|x| x.into())).collect();
                let arguments = signature.arguments.iter().map(|&(_, ref type_expression)| self.resolve_type(type_expression)).collect();
                let return_type = self.resolve_type(&signature.return_type);

                let function = Function { name, arguments, return_type };

                self.resolution_map.insert(&signature.name, function);
            },
        }
    }
}
