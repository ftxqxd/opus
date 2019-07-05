use std::mem;
use std::fmt;
use std::collections::HashMap;
use crate::parse::{Expression, Statement, FunctionSignature, Block, BinaryOperator};
use crate::compile::{Type, Compiler, Error, Function};

#[derive(Debug)]
pub enum Instruction<'source> {
    ConstantInteger(VariableId, u64),
    Call(VariableId, &'source Function, Box<[VariableId]>),

    Add(VariableId, VariableId, VariableId),
    Subtract(VariableId, VariableId, VariableId),
    Multiply(VariableId, VariableId, VariableId),
    Divide(VariableId, VariableId, VariableId),

    Negate(VariableId, VariableId),
    Reference(VariableId, VariableId),
    Dereference(VariableId, VariableId),

    Cast(VariableId, VariableId),

    Return(VariableId),
    Jump(usize),
    Branch(VariableId, usize, usize),

    Nop,
    BreakPlaceholder,
    Error(VariableId),
}

type VariableId = usize;

#[derive(Debug)]
pub struct Variable {
    pub typ: Type,
}

#[derive(Debug)]
pub struct IrGenerator<'source> {
    pub compiler: &'source Compiler<'source>,
    pub locals: HashMap<&'source str, VariableId>,
    pub variables: Vec<Variable>,
    pub instructions: Vec<Instruction<'source>>,
    pub signature: &'source FunctionSignature<'source>,
    pub function: &'source Function,

    /// The span of this function's definition.
    span: &'source str,

    /// A list of instructions which represent `break` statements, to be replaced with real `Jump`
    /// instructions once their containing loop has been generated.
    break_instructions_to_insert: Vec<usize>,
    /// The instruction index of the beginning of the innermost loop at the current point of
    /// compilation.  This is where a `continue` statement jumps back to.
    innermost_loop_begin: Option<usize>,
    /// An array of local variable names, in the order they were defined.  This stack is 'unwound'
    /// every time a block is exited, erasing all locals defined in the block from `self.locals`.
    locals_stack: Vec<&'source str>,
}

impl<'source> IrGenerator<'source> {
    pub fn from_function(compiler: &'source Compiler<'source>, signature: &'source FunctionSignature<'source>, block: &'source Block<'source>, span: &'source str) -> Self {
        let mut this = Self {
            compiler,
            locals: HashMap::new(),
            variables: vec![],
            instructions: vec![],
            signature,
            span,
            function: &compiler.resolution_map[&*signature.name],
            break_instructions_to_insert: vec![],
            innermost_loop_begin: None,
            locals_stack: vec![],
        };
        this.generate_ir_from_function(block);
        this
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

    fn generate_ir_from_function(&mut self, block: &'source Block<'source>) {
        for &(name, ref type_expression) in &self.signature.arguments {
            let typ = self.compiler.resolve_type(type_expression);
            let argument_id = self.new_variable(Variable { typ });
            self.locals.insert(name, argument_id);
        }

        let diverges = self.generate_ir_from_block(block);
        if !diverges {
            self.compiler.report_error(Error::FunctionMightNotReturn(self.span));
        }

        debug_assert_eq!(self.break_instructions_to_insert.len(), 0);

        // Push a nop to the end of instructions in case the function ends with a branch
        self.instructions.push(Instruction::Nop);
    }

    /// Generate IR for a block of statements.  Return `true` if the block is guaranteed to
    /// diverge.
    fn generate_ir_from_block(&mut self, block: &'source Block<'source>) -> bool {
        let locals_stack_length = self.locals_stack.len();
        let mut diverges = false;

        for statement in block {
            if self.generate_ir_from_statement(statement) {
                diverges = true;
            }
        }

        while self.locals_stack.len() > locals_stack_length {
            let name = self.locals_stack.pop().unwrap();
            self.locals.remove(name);
        }

        diverges
    }

    /// Autocast the given variable to the given type, if necessary.  If no such cast is possible,
    /// generate an error using the given span.
    fn autocast_variable_to_type(&mut self, variable: VariableId, expected_type: &Type, span: &'source str) -> VariableId {
        let found_type = &self.variables[variable].typ;

        if found_type == expected_type {
            // don't need to do anything
            variable
        } else if found_type.can_autocast_to(expected_type) {
            // do an autocast
            let return_variable = self.new_variable(Variable { typ: expected_type.clone() });
            self.instructions.push(Instruction::Cast(return_variable, variable));
            return_variable
        } else {
            // generate an error
            self.compiler.report_error(Error::UnexpectedType { span, expected: expected_type.clone(), found: found_type.clone() });
            let error = self.generate_error();
            error
        }
    }

    /// Generate IR for a single statement.  Return `true` if the statement is guaranteed to
    /// diverge.
    fn generate_ir_from_statement(&mut self, statement: &'source Statement<'source>) -> bool {
        match *statement {
            Statement::Expression(ref expression) => {
                self.generate_ir_from_expression(expression);
            },
            Statement::VariableDefinition(name, ref value) => {
                let variable = self.generate_ir_from_expression(value);
                self.locals_stack.push(name);
                self.locals.insert(name, variable);
            },
            Statement::Return(ref expression) => {
                let return_variable = self.generate_ir_from_expression(expression);

                let expected_type = &self.function.return_type;
                let span = self.compiler.expression_span(expression);
                let return_variable = self.autocast_variable_to_type(return_variable, expected_type, span);
                self.instructions.push(Instruction::Return(return_variable));
                return true
            },
            Statement::If(ref condition, ref then_block, ref else_block) => {
                let condition_variable = self.generate_ir_from_expression(condition);

                let mut diverges = true;

                let branch = self.instructions.len();
                self.instructions.push(Instruction::Nop);

                let then_branch = self.instructions.len();
                diverges &= self.generate_ir_from_block(then_block);
                let then_jump = self.instructions.len();
                self.instructions.push(Instruction::Nop);

                let else_branch = self.instructions.len();
                diverges &= self.generate_ir_from_block(else_block);
                let else_jump = self.instructions.len();
                self.instructions.push(Instruction::Nop);

                let merge = self.instructions.len();
                self.instructions[branch] = Instruction::Branch(condition_variable, then_branch, else_branch);
                self.instructions[then_jump] = Instruction::Jump(merge);
                self.instructions[else_jump] = Instruction::Jump(merge);

                return diverges
            },
            Statement::While(ref condition, ref then_block, ref else_block) => {
                let loop_start = self.instructions.len();

                let condition_variable = self.generate_ir_from_expression(condition);

                let branch = self.instructions.len();
                self.instructions.push(Instruction::Nop);

                let old_break_instructions_to_insert = mem::replace(&mut self.break_instructions_to_insert, vec![]);
                let old_innermost_loop_begin = self.innermost_loop_begin;
                self.innermost_loop_begin = Some(loop_start);
                let then_branch = self.instructions.len();
                self.generate_ir_from_block(then_block);
                self.instructions.push(Instruction::Jump(loop_start));
                let new_break_instructions_to_insert = mem::replace(&mut self.break_instructions_to_insert, old_break_instructions_to_insert);
                self.innermost_loop_begin = old_innermost_loop_begin;

                let else_branch = self.instructions.len();
                let diverges = self.generate_ir_from_block(else_block);
                let else_jump = self.instructions.len();
                self.instructions.push(Instruction::Nop);

                let merge = self.instructions.len();
                self.instructions[branch] = Instruction::Branch(condition_variable, then_branch, else_branch);
                self.instructions[else_jump] = Instruction::Jump(merge);
                // Fill in break instructions
                for index in new_break_instructions_to_insert {
                    self.instructions[index] = Instruction::Jump(merge);
                }

                return diverges
            },
            Statement::Break => {
                if let Some(_) = self.innermost_loop_begin {
                    self.break_instructions_to_insert.push(self.instructions.len());
                    self.instructions.push(Instruction::BreakPlaceholder);
                } else {
                    let span = self.compiler.statement_span(statement);
                    self.compiler.report_error(Error::BreakOutsideLoop(span));
                }
            },
            Statement::Continue => {
                if let Some(index) = self.innermost_loop_begin {
                    self.instructions.push(Instruction::Jump(index));
                } else {
                    let span = self.compiler.statement_span(statement);
                    self.compiler.report_error(Error::ContinueOutsideLoop(span));
                }
            },
        }

        false
    }

    fn generate_ir_from_expression(&mut self, expression: &'source Expression<'source>) -> VariableId {
        let expression_span = self.compiler.expression_span(expression);

        match *expression {
            Expression::Integer(i, signed, size) => {
                let typ = match (signed, size) {
                    (false, 8) => Type::Natural8,
                    (false, 16) => Type::Natural16,
                    (false, 32) => Type::Natural32,
                    (false, 64) => Type::Natural64,
                    (true, 8) => Type::Integer8,
                    (true, 16) => Type::Integer16,
                    (true, 32) => Type::Integer32,
                    (true, 64) => Type::Integer64,
                    _ => unreachable!(),
                };
                let variable = self.new_variable(Variable { typ });
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

                if let Some(function) = self.compiler.resolution_map.get(&**name) {
                    debug_assert_eq!(function.arguments.len(), arguments.len());

                    for (i, (expected_type, &found_variable)) in function.arguments.iter().zip(argument_variables.iter()).enumerate() {
                        let span = self.compiler.expression_span(&*arguments[i]);
                        self.autocast_variable_to_type(found_variable, expected_type, span);
                    }

                    let variable = self.new_variable(Variable { typ: function.return_type.clone()});
                    self.instructions.push(Instruction::Call(variable, function, argument_variables.into()));
                    variable
                } else {
                    self.compiler.report_error(Error::UndefinedFunction(expression_span, name));
                    self.generate_error()
                }
            },
            Expression::BinaryOperator(operator, ref left, ref right) => {
                let left_variable = self.generate_ir_from_expression(left);
                let right_variable = self.generate_ir_from_expression(right);

                let type1 = &self.variables[left_variable].typ;
                let type2 = &self.variables[right_variable].typ;
                let output_type = match (type1, type2) {
                    (&Type::Integer8, &Type::Integer8)
                    | (&Type::Integer16, &Type::Integer16)
                    | (&Type::Integer32, &Type::Integer32)
                    | (&Type::Integer64, &Type::Integer64)
                    | (&Type::Natural8, &Type::Natural8)
                    | (&Type::Natural16, &Type::Natural16)
                    | (&Type::Natural32, &Type::Natural32)
                    | (&Type::Natural64, &Type::Natural64)
                      => type1.clone(),
                    (ref type1, ref type2) => {
                        self.compiler.report_error(Error::InvalidOperandTypes {
                            span: expression_span,
                            left: (*type1).clone(),
                            right: (*type2).clone(),
                        });
                        return self.generate_error()
                    },
                };

                let operation = match operator {
                    BinaryOperator::Plus => Instruction::Add,
                    BinaryOperator::Minus => Instruction::Subtract,
                    BinaryOperator::Times => Instruction::Multiply,
                    BinaryOperator::Divide => Instruction::Divide,
                };
                let output_variable = self.new_variable(Variable { typ: output_type });
                self.instructions.push(operation(output_variable, left_variable, right_variable));

                output_variable
            },
            Expression::Reference(ref subexpression) => {
                let index = self.generate_ir_from_expression(subexpression);
                let variable = &self.variables[index];
                let output_variable = Variable { typ: Type::Pointer(Box::new(variable.typ.clone())) };
                let output_index = self.new_variable(output_variable);

                self.instructions.push(Instruction::Reference(output_index, index));

                output_index
            },
            Expression::Dereference(ref subexpression) => {
                let index = self.generate_ir_from_expression(subexpression);
                let variable = &self.variables[index];

                if let Type::Pointer(ref subtype) = variable.typ {
                    let output_variable = Variable { typ: (**subtype).clone() };
                    let output_index = self.new_variable(output_variable);

                    self.instructions.push(Instruction::Dereference(output_index, index));
                    output_index
                } else {
                    self.compiler.report_error(Error::InvalidOperandType { span: expression_span, typ: variable.typ.clone() });
                    self.generate_error()
                }
            },
            Expression::Negate(ref subexpression) => {
                let sub_index = self.generate_ir_from_expression(subexpression);
                let sub_variable = &self.variables[sub_index];

                match sub_variable.typ {
                    Type::Integer8
                    | Type::Integer16
                    | Type::Integer32
                    | Type::Integer64 => {
                        let output_variable = Variable { typ: sub_variable.typ.clone() };
                        let output_index = self.new_variable(output_variable);

                        self.instructions.push(Instruction::Negate(output_index, sub_index));
                        output_index
                    },
                    _ => {
                        self.compiler.report_error(Error::InvalidOperandType { span: expression_span, typ: sub_variable.typ.clone() });
                        self.generate_error()
                    }
                }
            },
        }
    }
}

impl<'source> fmt::Display for IrGenerator<'source> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{}", self.signature)?;

        for (i, variable) in self.variables.iter().enumerate() {
            writeln!(f, "VAR %{}: {:?}", i, variable.typ)?;
        }

        let mut first = true;
        for (instruction_index, instruction) in self.instructions.iter().enumerate() {
            if !first {
                writeln!(f, "")?;
            }
            first = false;

            write!(f, "{:<03} ", instruction_index)?;

            match *instruction {
                Instruction::ConstantInteger(destination, value) => write!(f, "%{} = {}", destination, value)?,
                Instruction::Call(destination, function, ref arguments) => {
                    write!(f, "%{} = call @{}", destination, function)?;
                    for argument in arguments.iter() {
                        write!(f, ", {}", argument)?;
                    }
                },

                Instruction::Add(variable1, variable2, variable3) => write!(f, "%{} = add %{}, %{}", variable1, variable2, variable3)?,
                Instruction::Subtract(variable1, variable2, variable3) => write!(f, "%{} = subtract %{}, %{}", variable1, variable2, variable3)?,
                Instruction::Multiply(variable1, variable2, variable3) => write!(f, "%{} = multiply %{}, %{}", variable1, variable2, variable3)?,
                Instruction::Divide(variable1, variable2, variable3) => write!(f, "%{} = divide %{}, %{}", variable1, variable2, variable3)?,

                Instruction::Negate(variable1, variable2) => write!(f, "%{} = negate %{}", variable1, variable2)?,
                Instruction::Reference(variable1, variable2) => write!(f, "%{} = reference %{}", variable1, variable2)?,
                Instruction::Dereference(variable1, variable2) => write!(f, "%{} = dereference %{}", variable1, variable2)?,

                Instruction::Cast(variable1, variable2) => {
                    let type1 = &self.variables[variable1].typ;
                    let type2 = &self.variables[variable2].typ;
                    // FIXME: impl Display for Type
                    write!(f, "%{} = cast [{:?} to {:?}] %{}", variable1, type1, type2, variable2)?;
                },

                Instruction::Return(variable) => write!(f, "return %{}", variable)?,
                Instruction::Jump(index) => write!(f, "jump @{:<03}", index)?,
                Instruction::Branch(variable, index1, index2) => write!(f, "branch %{}, @{:<03}, @{:<03}", variable, index1, index2)?,

                Instruction::Nop => write!(f, "nop")?,
                Instruction::BreakPlaceholder => write!(f, "<break placeholder>")?,
                Instruction::Error(destination) => write!(f, "%{} = error", destination)?,
            }
        }

        Ok(())
    }
}
