use std::fmt;
use std::collections::HashMap;
use crate::parse::{Expression, FunctionSignature, Block};
use crate::compile::{Type, Compiler, Error, FunctionId};

#[derive(Debug)]
pub enum Instruction {
    ConstantInteger(VariableId, u64),
    Call(VariableId, FunctionId, Box<[VariableId]>),
    Return(VariableId),
    Error(VariableId),
}

type VariableId = usize;

#[derive(Debug)]
struct Variable {
    typ: Type,
}

#[derive(Debug)]
pub struct IrGenerator<'source> {
    compiler: &'source Compiler<'source>,
    locals: HashMap<&'source str, VariableId>,
    variables: Vec<Variable>,
    instructions: Vec<Instruction>,
}

impl<'source> IrGenerator<'source> {
    pub fn with_compiler(compiler: &'source Compiler<'source>) -> Self {
        Self {
            compiler,
            locals: HashMap::new(),
            variables: vec![],
            instructions: vec![],
        }
    }

    fn new_variable(&mut self, variable: Variable) -> VariableId {
        self.variables.push(variable);
        self.variables.len() - 1
    }

    fn generate_error(&mut self) -> VariableId {
        let variable = self.new_variable(Variable { typ: Type::Error });
        self.instructions.push(Instruction::Error(variable));
        variable
    }

    pub fn generate_ir_from_function(&mut self, signature: &'source FunctionSignature<'source>, block: &'source Block<'source>) {
        for &(name, ref type_expression) in &signature.arguments {
            let typ = self.compiler.resolve_type(type_expression);
            let argument_id = self.new_variable(Variable { typ });
            self.locals.insert(name, argument_id);
        }

        let mut return_variable = !0;
        for expression in block {
            return_variable = self.generate_ir_from_expression(expression);
        }

        if block.is_empty() {
            return_variable = self.generate_error();
            self.compiler.report_error(Error::EmptyBlock);
        }

        let expected_return_type = self.compiler.resolve_type(&signature.return_type);
        let found_return_type = &self.variables[return_variable].typ;
        if !expected_return_type.can_unify_with(found_return_type) {
            self.compiler.report_error(Error::UnexpectedType {
                expected: expected_return_type,
                found: found_return_type.clone(),
            });
            return_variable = self.generate_error();
        }

        self.instructions.push(Instruction::Return(return_variable));
    }

    fn generate_ir_from_expression(&mut self, expression: &'source Expression<'source>) -> VariableId {
        match *expression {
            Expression::Integer(i) => {
                let variable = self.new_variable(Variable { typ: Type::Integer64 });
                self.instructions.push(Instruction::ConstantInteger(variable, i));
                variable
            },
            Expression::Variable(s) => {
                if let Some(&variable) = self.locals.get(s) {
                    variable
                } else {
                    self.compiler.report_error(Error::UndefinedVariable(s));
                    self.generate_error()
                }
            },
            Expression::Call(ref name, ref arguments) => {
                let argument_variables: Vec<_> = arguments.iter().map(|x| self.generate_ir_from_expression(x)).collect();

                if let Some(&(id, ref function)) = self.compiler.resolution_map.get(&**name) {
                    debug_assert_eq!(function.arguments.len(), arguments.len());

                    let mut had_error = false;
                    for (expected_type, found_variable) in function.arguments.iter().zip(argument_variables.iter()) {
                        let found_type = &self.variables[*found_variable].typ;
                        if !expected_type.can_unify_with(found_type) {
                            had_error = true;
                            self.compiler.report_error(Error::UnexpectedType { expected: expected_type.clone(), found: found_type.clone() });
                        }
                    }
                    if had_error {
                        return self.generate_error()
                    }

                    let variable = self.new_variable(Variable { typ: function.return_type.clone()});
                    self.instructions.push(Instruction::Call(variable, id, argument_variables.into()));
                    variable
                } else {
                    self.compiler.report_error(Error::UndefinedFunction(name));
                    self.generate_error()
                }
            },
            Expression::Assignment(name, ref value) => {
                let variable = self.generate_ir_from_expression(value);
                self.locals.insert(name, variable);
                variable
            },
        }
    }
}

impl<'source> fmt::Display for IrGenerator<'source> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, variable) in self.variables.iter().enumerate() {
            writeln!(f, "var %{}: {:?}", i, variable.typ)?;
        }

        let mut first = true;
        for instruction in &self.instructions {
            if !first {
                writeln!(f, "")?;
            }
            first = false;

            match *instruction {
                Instruction::ConstantInteger(destination, value) => write!(f, "%{} = {}", destination, value)?,
                Instruction::Call(destination, function, ref arguments) => {
                    write!(f, "%{} = call @{}", destination, function)?;
                    for argument in arguments.iter() {
                        write!(f, ", {}", argument)?;
                    }
                },
                Instruction::Return(variable) => write!(f, "return %{}", variable)?,
                Instruction::Error(destination) => write!(f, "%{} = error", destination)?,
            }
        }

        Ok(())
    }
}
