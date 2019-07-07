use std::mem;
use std::fmt;
use std::collections::HashMap;
use crate::parse::{Expression, Statement, FunctionSignature, Block, BinaryOperator};
use crate::compile::{Type, Compiler, Error, Function};

#[derive(Debug)]
pub enum Instruction<'source> {
    ConstantInteger(VariableId, u64),
    Null(VariableId),
    Bool(VariableId, bool),
    Call(VariableId, &'source Function, Box<[VariableId]>),

    Assign(Lvalue, VariableId),

    Add(VariableId, VariableId, VariableId),
    Subtract(VariableId, VariableId, VariableId),
    Multiply(VariableId, VariableId, VariableId),
    Divide(VariableId, VariableId, VariableId),
    Modulo(VariableId, VariableId, VariableId),
    Equals(VariableId, VariableId, VariableId),
    LessThan(VariableId, VariableId, VariableId),
    GreaterThan(VariableId, VariableId, VariableId),
    LessThanEquals(VariableId, VariableId, VariableId),
    GreaterThanEquals(VariableId, VariableId, VariableId),

    Negate(VariableId, VariableId),
    Reference(VariableId, Lvalue),
    MutableReference(VariableId, Lvalue),
    Dereference(VariableId, VariableId),

    Cast(VariableId, VariableId),

    Return(VariableId),
    Jump(usize),
    Branch(VariableId, usize, usize),

    Nop,
    BreakPlaceholder,
    Error(VariableId),
}

#[derive(Debug)]
pub enum Lvalue {
    Variable(VariableId),
    Dereference(VariableId),
    Error,
}

/// Contains an Lvalue as well as data about its type and whether it is mutable.
struct LvalueData {
    lvalue: Lvalue,
    typ: Type,
    mutable: bool,
}

type VariableId = usize;

#[derive(Debug, Clone)]
pub struct Variable {
    pub typ: Type,
    pub is_temporary: bool,
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
        let variable = self.new_variable(Variable { typ: Type::Error, is_temporary: true });
        self.instructions.push(Instruction::Error(variable));
        variable
    }

    fn generate_ir_from_function(&mut self, block: &'source Block<'source>) {
        for &(name, ref type_expression) in &self.signature.arguments {
            let typ = self.compiler.resolve_type(type_expression);
            let argument_id = self.new_variable(Variable { typ, is_temporary: false });
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
            let return_variable = self.new_variable(Variable { typ: expected_type.clone(), is_temporary: true });
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
                let variable_id = self.generate_ir_from_expression(value);
                let variable = &mut self.variables[variable_id];
                if self.locals_stack.contains(&name) {
                    self.compiler.report_error(Error::ShadowedName(name));
                } else {
                    let output_variable_id = if variable.is_temporary {
                        variable.is_temporary = false;
                        variable_id
                    } else {
                        let variable = variable.clone();
                        let new_variable_id = self.new_variable(Variable {
                            is_temporary: false,
                            ..variable
                        });
                        self.instructions.push(Instruction::Assign(Lvalue::Variable(new_variable_id), variable_id));
                        new_variable_id
                    };

                    self.locals_stack.push(name);
                    self.locals.insert(name, output_variable_id);
                }
            },
            Statement::Assignment(ref left, ref right) => {
                let LvalueData { lvalue, typ, mutable } = self.generate_ir_from_lvalue(left);

                if !mutable {
                    let span = self.compiler.expression_span(left);
                    self.compiler.report_error(Error::ImmutableLvalue(span));
                }

                let variable = self.generate_ir_from_expression(right);
                let span = self.compiler.expression_span(right);
                let return_variable = self.autocast_variable_to_type(variable, &typ, span);

                self.instructions.push(Instruction::Assign(lvalue, return_variable));
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
                let mut condition_variable = self.generate_ir_from_expression(condition);
                let typ = &self.variables[condition_variable].typ;
                if *typ != Type::Bool {
                    let span = self.compiler.expression_span(condition);
                    self.compiler.report_error(Error::UnexpectedType { span, expected: Type::Bool, found: typ.clone() });
                    condition_variable = self.generate_error();
                }

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

                let is_infinite = if let Expression::Bool(true) = **condition { true } else { false };

                let mut condition_variable = self.generate_ir_from_expression(condition);
                let typ = &self.variables[condition_variable].typ;
                if *typ != Type::Bool {
                    let span = self.compiler.expression_span(condition);
                    self.compiler.report_error(Error::UnexpectedType { span, expected: Type::Bool, found: typ.clone() });
                    condition_variable = self.generate_error();
                }

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
                let diverges = self.generate_ir_from_block(else_block) | (is_infinite && new_break_instructions_to_insert.len() == 0);
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
                let variable = self.new_variable(Variable { typ, is_temporary: true });
                self.instructions.push(Instruction::ConstantInteger(variable, i));
                variable
            },
            Expression::Null => {
                let variable_id = self.new_variable(Variable { typ: Type::Null, is_temporary: true });
                self.instructions.push(Instruction::Null(variable_id));
                variable_id
            },
            Expression::Bool(is_true) => {
                let variable_id = self.new_variable(Variable { typ: Type::Bool, is_temporary: true });
                self.instructions.push(Instruction::Bool(variable_id, is_true));
                variable_id
            },
            Expression::Variable(name) => {
                if let Some(&variable) = self.locals.get(name) {
                    variable
                } else {
                    self.compiler.report_error(Error::UndefinedVariable(name));
                    self.generate_error()
                }
            },
            Expression::VariableDefinition(name, ref type_expression) => {
                if self.locals_stack.contains(&name) {
                    self.compiler.report_error(Error::ShadowedName(name));
                    self.generate_error()
                } else {
                    let typ = self.compiler.resolve_type(type_expression);
                    let variable = self.new_variable(Variable { typ, is_temporary: false });
                    self.locals_stack.push(name);
                    self.locals.insert(name, variable);
                    variable
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

                    let variable = self.new_variable(Variable { typ: function.return_type.clone(), is_temporary: true });
                    self.instructions.push(Instruction::Call(variable, function, argument_variables.into()));
                    variable
                } else {
                    self.compiler.report_error(Error::UndefinedFunction(expression_span, name));
                    self.generate_error()
                }
            },
            Expression::BinaryOperator(operator, ref left, ref right) => {
                let operation = match operator {
                    BinaryOperator::Plus => Instruction::Add,
                    BinaryOperator::Minus => Instruction::Subtract,
                    BinaryOperator::Times => Instruction::Multiply,
                    BinaryOperator::Divide => Instruction::Divide,
                    BinaryOperator::Modulo => Instruction::Modulo,
                    BinaryOperator::Equals => Instruction::Equals,
                    BinaryOperator::LessThan => Instruction::LessThan,
                    BinaryOperator::GreaterThan => Instruction::GreaterThan,
                    BinaryOperator::LessThanEquals => Instruction::LessThanEquals,
                    BinaryOperator::GreaterThanEquals => Instruction::GreaterThanEquals,
                    BinaryOperator::Cast => {
                        let variable_id = self.generate_ir_from_expression(left);
                        let old_type = &self.variables[variable_id].typ;
                        let typ = self.compiler.resolve_type(right);
                        if old_type.can_cast_to(&typ) {
                            let new_variable_id = self.new_variable(Variable { typ, is_temporary: true });
                            self.instructions.push(Instruction::Cast(new_variable_id, variable_id));
                            return new_variable_id
                        } else {
                            self.compiler.report_error(Error::InvalidCast { span: expression_span, from: old_type.clone(), to: typ });
                            return self.generate_error()
                        }
                    },
                };

                let left_variable = self.generate_ir_from_expression(left);
                let right_variable = self.generate_ir_from_expression(right);

                let type1 = &self.variables[left_variable].typ;
                let type2 = &self.variables[right_variable].typ;
                let output_type = match (type1, type2) {
                    (_, _) if type1 == type2 && type1.is_integral() && operator.is_arithmetic() => type1.clone(),
                    (_, _) if type1 == type2 && type1.is_integral() && operator.is_comparison() => Type::Bool,
                    (&Type::Reference(_), _) | (&Type::MutableReference(_), _)
                        if type2.is_integral() && (operator == BinaryOperator::Plus || operator == BinaryOperator::Minus)
                      => type1.clone(),
                    (_, &Type::Error) | (&Type::Error, _) => Type::Error,
                    (_, _) => {
                        self.compiler.report_error(Error::InvalidOperandTypes {
                            span: expression_span,
                            left: (*type1).clone(),
                            right: (*type2).clone(),
                        });
                        return self.generate_error()
                    },
                };

                let output_variable = self.new_variable(Variable { typ: output_type, is_temporary: true });
                self.instructions.push(operation(output_variable, left_variable, right_variable));

                output_variable
            },
            Expression::Reference(ref subexpression) => {
                let LvalueData { lvalue, typ, .. } = self.generate_ir_from_lvalue(subexpression);
                let output_variable = Variable { typ: Type::Reference(Box::new(typ)), is_temporary: true };
                let output_index = self.new_variable(output_variable);

                self.instructions.push(Instruction::Reference(output_index, lvalue));

                output_index
            },
            Expression::MutableReference(ref subexpression) => {
                let LvalueData { lvalue, typ, mutable } = self.generate_ir_from_lvalue(subexpression);

                if !mutable {
                    let span = self.compiler.expression_span(subexpression);
                    self.compiler.report_error(Error::ImmutableLvalue(span));
                }

                let output_variable = Variable { typ: Type::MutableReference(Box::new(typ)), is_temporary: true };
                let output_index = self.new_variable(output_variable);

                self.instructions.push(Instruction::MutableReference(output_index, lvalue));

                output_index
            },
            Expression::Dereference(ref subexpression) => {
                let index = self.generate_ir_from_expression(subexpression);
                let variable = &self.variables[index];

                if let Type::Reference(ref subtype) = variable.typ {
                    let output_variable = Variable { typ: (**subtype).clone(), is_temporary: true };
                    let output_index = self.new_variable(output_variable);

                    self.instructions.push(Instruction::Dereference(output_index, index));
                    output_index
                } else if let Type::MutableReference(ref subtype) = variable.typ {
                    let output_variable = Variable { typ: (**subtype).clone(), is_temporary: true };
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
                        let output_variable = Variable { typ: sub_variable.typ.clone(), is_temporary: true };
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
            Expression::Parentheses(ref subexpression) => {
                self.generate_ir_from_expression(subexpression)
            },
        }
    }

    fn generate_ir_from_lvalue(&mut self, expression: &'source Expression<'source>) -> LvalueData {
        let span = self.compiler.expression_span(expression);
        match *expression {
            Expression::Variable(s) => {
                if let Some(&variable) = self.locals.get(s) {
                    let typ = self.variables[variable].typ.clone();
                    return LvalueData {
                        lvalue: Lvalue::Variable(variable),
                        typ,
                        mutable: true,
                    }
                } else {
                    self.compiler.report_error(Error::UndefinedVariable(s));
                }
            },
            Expression::VariableDefinition(name, ref type_expression) => {
                if self.locals_stack.contains(&name) {
                    self.compiler.report_error(Error::ShadowedName(name));
                } else {
                    let typ = self.compiler.resolve_type(type_expression);
                    let variable = self.new_variable(Variable { typ: typ.clone(), is_temporary: false });
                    self.locals_stack.push(name);
                    self.locals.insert(name, variable);
                    return LvalueData {
                        lvalue: Lvalue::Variable(variable),
                        typ,
                        mutable: true,
                    }
                }
            },
            Expression::Dereference(ref subexpression) => {
                let index = self.generate_ir_from_expression(subexpression);
                let variable = &self.variables[index];

                if let Type::Reference(ref subtype) = variable.typ {
                    return LvalueData {
                        lvalue: Lvalue::Dereference(index),
                        typ: (**subtype).clone(),
                        mutable: false,
                    }
                } else if let Type::MutableReference(ref subtype) = variable.typ {
                    return LvalueData {
                        lvalue: Lvalue::Dereference(index),
                        typ: (**subtype).clone(),
                        mutable: true,
                    }
                } else {
                    self.compiler.report_error(Error::InvalidOperandType { span, typ: variable.typ.clone() });
                }
            },
            Expression::Parentheses(ref subexpression) => {
                return self.generate_ir_from_lvalue(subexpression)
            },
            _ => {
                self.compiler.report_error(Error::InvalidLvalue(span));
            },
        }
        LvalueData { lvalue: Lvalue::Error, typ: Type::Error, mutable: true }
    }
}

impl<'source> fmt::Display for IrGenerator<'source> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{}", self.function)?;

        for (i, variable) in self.variables.iter().enumerate() {
            writeln!(f, "VAR %{}: {}", i, variable.typ)?;
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
                Instruction::Null(destination) => write!(f, "%{} = null", destination)?,
                Instruction::Bool(destination, is_true) => write!(f, "%{} = {:?}", destination, is_true)?,
                Instruction::Call(destination, function, ref arguments) => {
                    write!(f, "%{} = call @{}", destination, function)?;
                    for argument in arguments.iter() {
                        write!(f, ", {}", argument)?;
                    }
                },

                // FIXME: impl Display for Lvalue
                Instruction::Assign(ref lvalue, variable) => write!(f, "{:?} = %{}", lvalue, variable)?,

                Instruction::Add(variable1, variable2, variable3) => write!(f, "%{} = add %{}, %{}", variable1, variable2, variable3)?,
                Instruction::Subtract(variable1, variable2, variable3) => write!(f, "%{} = subtract %{}, %{}", variable1, variable2, variable3)?,
                Instruction::Multiply(variable1, variable2, variable3) => write!(f, "%{} = multiply %{}, %{}", variable1, variable2, variable3)?,
                Instruction::Divide(variable1, variable2, variable3) => write!(f, "%{} = divide %{}, %{}", variable1, variable2, variable3)?,
                Instruction::Modulo(variable1, variable2, variable3) => write!(f, "%{} = modulo %{}, %{}", variable1, variable2, variable3)?,
                Instruction::Equals(variable1, variable2, variable3) => write!(f, "%{} = equals %{}, %{}", variable1, variable2, variable3)?,
                Instruction::LessThan(variable1, variable2, variable3) => write!(f, "%{} = lessthan %{}, %{}", variable1, variable2, variable3)?,
                Instruction::GreaterThan(variable1, variable2, variable3) => write!(f, "%{} = greaterthan %{}, %{}", variable1, variable2, variable3)?,
                Instruction::LessThanEquals(variable1, variable2, variable3) => write!(f, "%{} = lessthanequals %{}, %{}", variable1, variable2, variable3)?,
                Instruction::GreaterThanEquals(variable1, variable2, variable3) => write!(f, "%{} = greaterthanequals %{}, %{}", variable1, variable2, variable3)?,

                Instruction::Negate(variable1, variable2) => write!(f, "%{} = negate %{}", variable1, variable2)?,
                Instruction::Reference(variable1, ref lvalue) => write!(f, "%{} = reference %{:?}", variable1, lvalue)?,
                Instruction::MutableReference(variable1, ref lvalue) => write!(f, "%{} = mutablereference %{:?}", variable1, lvalue)?,
                // FIXME: impl Display for Lvalue
                Instruction::Dereference(variable1, variable2) => write!(f, "%{} = dereference %{}", variable1, variable2)?,

                Instruction::Cast(variable1, variable2) => {
                    let type1 = &self.variables[variable1].typ;
                    let type2 = &self.variables[variable2].typ;
                    write!(f, "%{} = cast [{} to {}] %{}", variable1, type1, type2, variable2)?;
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
