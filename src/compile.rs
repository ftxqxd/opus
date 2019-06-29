use std::collections::HashMap;
use crate::parse::{FunctionName, Definition, Expression, FunctionSignature};

pub type FunctionId = u32;

#[derive(Debug)]
pub struct Compiler<'source> {
    pub resolution_map: HashMap<&'source FunctionName<'source>, FunctionId>,
    pub functions: Vec<Function>,
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
            functions: vec![],
        }
    }

    pub fn report_error(&self, error: Error<'source>) {
        println!("{:?}", error);
    }

    pub fn resolve_type(&self, typ: &Expression) -> Type {
        match *typ {
            Expression::Variable("int64") => Type::Integer64,
            Expression::Variable("nat64") => Type::Natural64,
            _ => Type::Error,
        }
    }

    pub fn resolve_signature<'source2>(&self, signature: &FunctionSignature) -> Function {
        let name = signature.name.iter().map(|part| part.map(|x| x.into())).collect();
        let arguments = signature.arguments.iter().map(|&(_, ref type_expression)| self.resolve_type(type_expression)).collect();
        let return_type = self.resolve_type(&signature.return_type);

        Function { name, arguments, return_type }
    }

    pub fn parse_definition(&mut self, definition: &'source Definition<'source>) {
        match definition {
            Definition::Function(ref signature, ..) => {
                let function = self.resolve_signature(signature);
                self.resolution_map.insert(&signature.name, self.functions.len() as FunctionId);
                self.functions.push(function);
            },
        }
    }
}
