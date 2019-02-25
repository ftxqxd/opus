use crate::parse::{FunctionName, Definition, Expression};
use std::collections::HashMap;

pub type FunctionId = u32;

#[derive(Debug)]
pub struct Compiler<'source> {
    pub resolution_map: HashMap<&'source FunctionName<'source>, (FunctionId, Function)>,

    next_function_id: u32,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Integer64,
    Natural64,
    Error,
}

#[derive(Debug)]
pub struct Function {
    pub name: Box<[Option<Box<str>>]>,
    pub arguments: Box<[Type]>,
    pub return_type: Type,
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
        Self {
            resolution_map: HashMap::new(),

            next_function_id: 0,
        }
    }

    pub fn report_error(&self, error: Error<'source>) {
        println!("{:?}", error);
    }

    fn resolve_type(&mut self, typ: &Expression) -> Type {
        match *typ {
            Expression::Variable("int64") => Type::Integer64,
            Expression::Variable("nat64") => Type::Natural64,
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
                let id = self.next_function_id;
                self.next_function_id += 1;
                self.resolution_map.insert(&signature.name, (id, function));
            },
        }
    }
}
