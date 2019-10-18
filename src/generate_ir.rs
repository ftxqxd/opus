use std::mem;
use std::fmt;
use std::collections::HashMap;
use crate::parse::{Expression, Statement, FunctionSignature, Block, Operator};
use crate::compile::{Type, TypeId, PrimitiveType, PointerType, Compiler, Error, Function, FunctionId, GlobalId, TypePrinter, FunctionPrinter, CastType};

#[derive(Debug)]
pub enum Instruction<'source> {
    Integer(VariableId, i64),
    Float(VariableId, f64),
    Null(VariableId),
    Bool(VariableId, bool),
    String(VariableId, Box<[u8]>),

    Sizeof(VariableId, TypeId),
    Alignof(VariableId, TypeId),

    Call(VariableId, VariableId, Box<[VariableId]>),

    Allocate(VariableId),
    Load(VariableId, VariableId),
    Store(VariableId, VariableId),
    Field(VariableId, VariableId, &'source str),
    BuiltinField(VariableId, VariableId, u32),
    IndexPointer(VariableId, VariableId, VariableId),
    IndexArray(VariableId, VariableId, VariableId),

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

    Function(VariableId, FunctionId),
    GlobalVariable(VariableId, GlobalId),
    GlobalConstant(VariableId, GlobalId),

    Not(VariableId, VariableId),
    Negate(VariableId, VariableId),

    Cast(CastType, VariableId, VariableId),

    Return(VariableId),
    Jump(usize),
    Branch(VariableId, usize, usize),
    Unreachable,
    Phi(VariableId, usize, VariableId, usize, VariableId),

    BreakPlaceholder,
    Error(VariableId),
}

impl<'source> Instruction<'source> {
    fn is_terminator(&self) -> bool {
        match *self {
            Instruction::Return(..) | Instruction::Jump(..) | Instruction::Branch(..) | Instruction::Unreachable => true,
            _ => false,
        }
    }
}

type VariableId = usize;

#[derive(Debug, Clone)]
pub struct Variable {
    pub typ: TypeId,
    pub is_temporary: bool,
}

pub struct IrGenerator<'source> {
    pub compiler: &'source Compiler<'source>,
    pub locals: HashMap<&'source str, VariableId>,
    pub variables: Vec<Variable>,
    pub bbs: Vec<Vec<Instruction<'source>>>,
    pub signature: &'source FunctionSignature<'source>,
    pub function: &'source Function,

    bb_index: usize,

    /// The span of this function's definition.
    span: &'source str,

    /// A list of instructions which represent `break` statements, to be replaced with real `Jump`
    /// instructions once their containing loop has been generated.
    break_instructions_to_insert: Vec<(usize, usize)>,
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
            bbs: vec![vec![]],
            signature,
            bb_index: 0,
            span,
            function: compiler.get_function_info(compiler.signature_resolution_map[&(signature as *const _)]),
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

    fn instructions(&mut self) -> &mut Vec<Instruction<'source>> {
        &mut self.bbs[self.bb_index]
    }

    fn generate_error(&mut self) -> VariableId {
        let variable = self.new_variable(Variable { typ: self.compiler.type_error(), is_temporary: true });
        self.instructions().push(Instruction::Error(variable));
        variable
    }

    fn generate_ir_from_function(&mut self, block: &'source Block<'source>) {
        // First, generate the argument values
        let mut types = vec![];
        for &(_, ref type_expression) in &self.signature.arguments {
            let typ = self.compiler.resolve_type(type_expression);
            types.push(typ.clone());
            self.new_variable(Variable { typ, is_temporary: true });
        }

        // Then generate argument *locals* that we can mutate etc.
        for ((argument_id, &(ref name, _)), typ) in self.signature.arguments.iter().enumerate().zip(types.into_iter()) {
            let typ = self.compiler.type_mut(typ);
            let variable_id = self.new_variable(Variable { typ, is_temporary: false });
            self.instructions().push(Instruction::Allocate(variable_id));
            self.instructions().push(Instruction::Store(variable_id, argument_id));
            self.locals.insert(name.clone(), variable_id);
        }

        let returns_null = if let Type::Null = *self.compiler.get_type_info(self.function.return_type) {
            true
        } else {
            false
        };

        let diverges = self.generate_ir_from_block(block);
        if diverges || returns_null {
            let last_bb = &mut self.bbs[self.bb_index];
            if last_bb.last().filter(|x| x.is_terminator()).is_none() {
                if returns_null {
                    let variable_id = self.new_variable(Variable { typ: self.compiler.type_null(), is_temporary: true });
                    self.instructions().push(Instruction::Null(variable_id));
                    self.instructions().push(Instruction::Return(variable_id));
                } else {
                    last_bb.push(Instruction::Unreachable);
                }
            }
        } else {
            self.compiler.report_error(Error::FunctionMightNotReturn(self.span));
        }

        debug_assert_eq!(self.break_instructions_to_insert.len(), 0);
    }

    fn begin_scope(&mut self) -> usize {
        self.locals_stack.len()
    }

    fn end_scope(&mut self, locals_stack_length: usize) {
        while self.locals_stack.len() > locals_stack_length {
            let name = self.locals_stack.pop().unwrap();
            self.locals.remove(&name);
        }
    }

    /// Generate IR for a block of statements.  Return `true` if the block is guaranteed to
    /// diverge.
    fn generate_ir_from_block(&mut self, block: &'source Block<'source>) -> bool {
        let mut diverges = false;

        let scope = self.begin_scope();

        for statement in block {
            if self.generate_ir_from_statement(statement) {
                diverges = true;
            }
        }

        self.end_scope(scope);

        diverges
    }

    /// Autocast the given variable to the given type, if necessary.  If no such cast is possible,
    /// generate an error using the given span.
    fn autocast_variable_to_type(&mut self, variable: VariableId, expected_type: TypeId, span: &'source str) -> VariableId {
        let found_type = self.variables[variable].typ;

        if self.compiler.types_match(found_type, expected_type) {
            // don't need to do anything
            variable
        } else if let Some(cast_type) = self.compiler.can_autocast(found_type, expected_type) {
            if let Type::GenericInteger | Type::Generic = *self.compiler.get_type_info(found_type) {
                // This Generic* variable must be the argument of a function call, so we can
                // just change its type directly, as it's a temporary so isn't used anywhere else.
                self.variables[variable].typ = expected_type;
                variable
            } else {
                // do an autocast
                let return_variable = self.new_variable(Variable { typ: expected_type, is_temporary: true });
                self.instructions().push(Instruction::Cast(cast_type, return_variable, variable));
                return_variable
            }
        } else {
            // generate an error
            self.compiler.report_error(Error::UnexpectedType { span, expected: expected_type, found: found_type });
            let error = self.generate_error();
            error
        }
    }

    /// Return the type of the lvalue with the given ID.  The provided variable should always be of
    /// a reference type.
    pub fn get_lvalue_type(&self, variable_id: VariableId) -> TypeId {
        let type_id = self.variables[variable_id].typ;
        match *self.compiler.get_type_info(type_id) {
            Type::Pointer(_, typ) => typ,
            Type::Error => self.compiler.type_error(),
            _ => unreachable!("lvalue of type {}", TypePrinter(self.compiler, type_id)),
        }
    }

    /// Generate IR for a single statement.  Return `true` if the statement is guaranteed to
    /// diverge.
    fn generate_ir_from_statement(&mut self, statement: &'source Statement<'source>) -> bool {
        let span = self.compiler.statement_span(statement);
        match *statement {
            Statement::Expression(ref expression) => {
                self.generate_ir_from_expression(expression, None);
            },
            Statement::VariableDefinition(ref name, ref value) => {
                let variable_id = self.generate_ir_from_expression(value, None);
                let typ = self.variables[variable_id].typ;
                if self.locals_stack.contains(&name) {
                    self.compiler.report_error(Error::ShadowedName(span, name.clone()));
                } else {
                    let new_variable_id = self.new_variable(Variable { typ: self.compiler.type_mut(typ), is_temporary: false });
                    self.instructions().push(Instruction::Allocate(new_variable_id));
                    self.instructions().push(Instruction::Store(new_variable_id, variable_id));
                    self.locals_stack.push(name.clone());
                    self.locals.insert(name.clone(), new_variable_id);
                }
            },
            Statement::Assignment(ref left, ref right) => {
                let left_variable_id = self.generate_pointer_from_expression(left, PointerType::Mutable);
                let left_variable_type = self.get_lvalue_type(left_variable_id);

                let right_variable_id = self.generate_ir_from_expression(right, Some(left_variable_type));
                let span = self.compiler.expression_span(right);
                let final_variable_id = self.autocast_variable_to_type(right_variable_id, left_variable_type, span);

                self.instructions().push(Instruction::Store(left_variable_id, final_variable_id));
            },
            Statement::Return(ref expression) => {
                let return_variable = self.generate_ir_from_expression(expression, Some(self.function.return_type));

                let expected_type = self.function.return_type;
                let span = self.compiler.expression_span(expression);
                let return_variable = self.autocast_variable_to_type(return_variable, expected_type, span);
                self.instructions().push(Instruction::Return(return_variable));
                return true
            },
            Statement::If(ref condition, ref then_block, ref else_block) => {
                let condition_variable = self.generate_ir_from_expression(condition, Some(self.compiler.type_bool()));
                let condition_span = self.compiler.expression_span(condition);
                let condition_variable = self.autocast_variable_to_type(condition_variable, self.compiler.type_bool(), condition_span);

                let branch = self.bb_index;

                let mut diverges = true;

                let then_branch = self.bbs.len();
                self.bbs.push(vec![]);
                self.bb_index = then_branch;
                diverges &= self.generate_ir_from_block(then_block);
                let then_branch_end = self.bb_index;

                let else_branch = self.bbs.len();
                self.bbs.push(vec![]);
                self.bb_index = else_branch;
                diverges &= self.generate_ir_from_block(else_block);
                let else_branch_end = self.bb_index;

                let merge = self.bbs.len();
                self.bbs.push(vec![]);
                self.bb_index = merge;

                self.bbs[branch].push(Instruction::Branch(condition_variable, then_branch, else_branch));
                self.bbs[then_branch_end].push(Instruction::Jump(merge));
                self.bbs[else_branch_end].push(Instruction::Jump(merge));

                return diverges
            },
            Statement::While(ref condition, ref then_block, ref else_block) => {
                let loop_start = self.bbs.len();
                self.instructions().push(Instruction::Jump(loop_start));
                self.bb_index = loop_start;
                self.bbs.push(vec![]);

                let is_infinite = if let Expression::Bool(true) = **condition { true } else { false };

                let condition_variable = self.generate_ir_from_expression(condition, Some(self.compiler.type_bool()));
                let condition_span = self.compiler.expression_span(condition);
                let condition_variable = self.autocast_variable_to_type(condition_variable, self.compiler.type_bool(), condition_span);

                let branch = self.bb_index;

                let old_break_instructions_to_insert = mem::replace(&mut self.break_instructions_to_insert, vec![]);
                let old_innermost_loop_begin = self.innermost_loop_begin;
                self.innermost_loop_begin = Some(loop_start);

                let then_branch = self.bbs.len();
                self.bbs.push(vec![]);
                self.bb_index = then_branch;
                self.generate_ir_from_block(then_block);
                let then_branch_end = self.bb_index;

                let new_break_instructions_to_insert = mem::replace(&mut self.break_instructions_to_insert, old_break_instructions_to_insert);
                self.innermost_loop_begin = old_innermost_loop_begin;

                let else_branch = self.bbs.len();
                self.bbs.push(vec![]);
                self.bb_index = else_branch;
                let diverges = self.generate_ir_from_block(else_block) | (is_infinite && new_break_instructions_to_insert.len() == 0);
                let else_branch_end = self.bb_index;

                let merge = self.bbs.len();
                self.bbs.push(vec![]);
                self.bb_index = merge;

                self.bbs[branch].push(Instruction::Branch(condition_variable, then_branch, else_branch));
                self.bbs[then_branch_end].push(Instruction::Jump(loop_start));
                self.bbs[else_branch_end].push(Instruction::Jump(merge));

                // Fill in break instructions
                for (bb_index, instruction_index) in new_break_instructions_to_insert {
                    self.bbs[bb_index][instruction_index] = Instruction::Jump(merge);
                }

                return diverges
            },
            Statement::For(ref name, ref type_option, ref iteree, ref then_block, ref else_block) => {
                // We esentially want this:
                //
                //     for <name>[: <type>] in <iteree>
                //         <then>
                //     else
                //         <else>
                //
                // to be equivalent to this:
                //
                //     var iterator := (for <iteree>)
                //     var <name>[: <type>]
                //     while (continue mut iterator mut <name>)
                //         <then>
                //     else
                //         <else>
                //
                //  but where <name> is only accessible in the scope of the <then> block.

                // Generate the iterator
                let iteree_variable = self.generate_ir_from_expression(iteree, None);
                let mut argument_variables = vec![iteree_variable];
                let expression_span = self.compiler.expression_span(iteree);
                let argument_spans = vec![expression_span];
                let (for_function_variable, return_variable, _) = if let Some(x) = self.get_function_call_variables(expression_span, "for", &mut argument_variables, argument_spans) {
                    x
                } else {
                    (self.generate_error(), self.generate_error(), false)
                };
                let iterator_variable_type = self.compiler.type_mut(self.variables[return_variable].typ);
                let iterator_variable = self.new_variable(Variable { typ: iterator_variable_type, is_temporary: true });
                self.instructions().push(Instruction::Call(return_variable, for_function_variable, (*argument_variables).into()));
                self.instructions().push(Instruction::Allocate(iterator_variable));
                self.instructions().push(Instruction::Store(iterator_variable, return_variable));

                let loop_start = self.bbs.len();
                self.instructions().push(Instruction::Jump(loop_start));
                self.bb_index = loop_start;
                self.bbs.push(vec![]);

                // Define iteration variable
                let scope = self.begin_scope();
                let pointer_type = if let Some(type_expression) = type_option.as_ref() {
                    self.compiler.type_mut(self.compiler.resolve_type(type_expression))
                } else {
                    self.compiler.type_primitive(PrimitiveType::Generic)
                };
                let iteration_variable = if self.locals_stack.contains(&name) {
                    self.compiler.report_error(Error::ShadowedName(span, name.clone()));
                    self.generate_error()
                } else {
                    let new_variable_id = self.new_variable(Variable { typ: pointer_type, is_temporary: false });
                    self.instructions().push(Instruction::Allocate(new_variable_id));
                    self.locals_stack.push(name.clone());
                    self.locals.insert(name.clone(), new_variable_id);
                    new_variable_id
                };

                // Generate branching condition
                let mut argument_variables = vec![iterator_variable, iteration_variable];
                let argument_spans = vec![expression_span, expression_span]; // FIXME: spans could be better
                let (continue_function_variable, condition_variable, _) = if let Some(x) = self.get_function_call_variables(expression_span, "continue", &mut argument_variables, argument_spans) {
                    x
                } else {
                    (self.generate_error(), self.generate_error(), false)
                };
                self.instructions().push(Instruction::Call(condition_variable, continue_function_variable, (*argument_variables).into()));
                let condition_variable = self.autocast_variable_to_type(condition_variable, self.compiler.type_bool(), expression_span);

                let branch = self.bb_index;

                let old_break_instructions_to_insert = mem::replace(&mut self.break_instructions_to_insert, vec![]);
                let old_innermost_loop_begin = self.innermost_loop_begin;
                self.innermost_loop_begin = Some(loop_start);

                let then_branch = self.bbs.len();
                self.bbs.push(vec![]);
                self.bb_index = then_branch;
                self.generate_ir_from_block(then_block);
                let then_branch_end = self.bb_index;

                let new_break_instructions_to_insert = mem::replace(&mut self.break_instructions_to_insert, old_break_instructions_to_insert);
                self.innermost_loop_begin = old_innermost_loop_begin;

                self.end_scope(scope);

                let else_branch = self.bbs.len();
                self.bbs.push(vec![]);
                self.bb_index = else_branch;
                let diverges = self.generate_ir_from_block(else_block);
                let else_branch_end = self.bb_index;

                let merge = self.bbs.len();
                self.bbs.push(vec![]);
                self.bb_index = merge;

                self.bbs[branch].push(Instruction::Branch(condition_variable, then_branch, else_branch));
                self.bbs[then_branch_end].push(Instruction::Jump(loop_start));
                self.bbs[else_branch_end].push(Instruction::Jump(merge));

                // Fill in break instructions
                for (bb_index, instruction_index) in new_break_instructions_to_insert {
                    self.bbs[bb_index][instruction_index] = Instruction::Jump(merge);
                }

                return diverges
            },
            Statement::Break => {
                if let Some(_) = self.innermost_loop_begin {
                    let len = self.instructions().len();
                    self.break_instructions_to_insert.push((self.bb_index, len));
                    self.instructions().push(Instruction::BreakPlaceholder);
                    self.bb_index = self.bbs.len();
                    self.bbs.push(vec![]);
                } else {
                    self.compiler.report_error(Error::BreakOutsideLoop(span));
                }
            },
            Statement::Continue => {
                if let Some(index) = self.innermost_loop_begin {
                    self.instructions().push(Instruction::Jump(index));
                    self.bb_index = self.bbs.len();
                    self.bbs.push(vec![]);
                } else {
                    self.compiler.report_error(Error::ContinueOutsideLoop(span));
                }
            },
        }

        false
    }

    fn dereference_pointer(&mut self, pointer_variable_id: VariableId) -> VariableId {
        let typ = self.get_lvalue_type(pointer_variable_id);
        let new_variable_id = self.new_variable(Variable {
            typ,
            is_temporary: true,
        });
        self.instructions().push(Instruction::Load(new_variable_id, pointer_variable_id));
        new_variable_id
    }

    /// Generate IR for the given expression and return the index of the variable representing the
    /// result.
    ///
    /// The parameter `expected_type` isn't used for type checking; it is used to infer the type of
    /// integer literals.
    fn generate_ir_from_expression(&mut self, expression: &'source Expression<'source>, expected_type: Option<TypeId>) -> VariableId {
        let expression_span = self.compiler.expression_span(expression);

        match *expression {
            Expression::Integer(i, meta) => {
                let typ = match meta {
                    Some(x) => self.compiler.type_primitive(match x {
                        (false, 8) => PrimitiveType::Natural8,
                        (false, 16) => PrimitiveType::Natural16,
                        (false, 32) => PrimitiveType::Natural32,
                        (false, 64) => PrimitiveType::Natural64,
                        (false, 0) => PrimitiveType::Size,
                        (true, 8) => PrimitiveType::Integer8,
                        (true, 16) => PrimitiveType::Integer16,
                        (true, 32) => PrimitiveType::Integer32,
                        (true, 64) => PrimitiveType::Integer64,
                        (true, 0) => PrimitiveType::Offset,
                        _ => unreachable!(),
                    }),
                    None => match expected_type.map(|x| self.compiler.get_type_info(x)) {
                          Some(&Type::Integer8)
                        | Some(&Type::Integer16)
                        | Some(&Type::Integer32)
                        | Some(&Type::Integer64)
                        | Some(&Type::Natural8)
                        | Some(&Type::Natural16)
                        | Some(&Type::Natural32)
                        | Some(&Type::Natural64)
                        | Some(&Type::Size)
                        | Some(&Type::Offset)
                        | Some(&Type::GenericInteger) => {
                            expected_type.unwrap()
                        },
                        _ => self.compiler.type_primitive(PrimitiveType::Integer32),
                    },
                };
                let variable = self.new_variable(Variable { typ, is_temporary: true });
                self.instructions().push(Instruction::Integer(variable, i as i64));
                variable
            },
            Expression::Float(f, size) => {
                let typ = match size {
                    Some(32) => self.compiler.type_primitive(PrimitiveType::Float32),
                    Some(64) => self.compiler.type_primitive(PrimitiveType::Float64),
                    Some(_) => unreachable!(),
                    None => self.compiler.type_primitive(PrimitiveType::Float64),
                };
                let variable = self.new_variable(Variable { typ, is_temporary: true });
                self.instructions().push(Instruction::Float(variable, f));
                variable
            },
            Expression::Null => {
                let variable_id = self.new_variable(Variable { typ: self.compiler.type_null(), is_temporary: true });
                self.instructions().push(Instruction::Null(variable_id));
                variable_id
            },
            Expression::Bool(is_true) => {
                let variable_id = self.new_variable(Variable { typ: self.compiler.type_bool(), is_temporary: true });
                self.instructions().push(Instruction::Bool(variable_id, is_true));
                variable_id
            },
            Expression::String(ref bytes) => {
                let typ = self.compiler.type_string();
                let variable_id = self.new_variable(Variable { typ, is_temporary: true });
                self.instructions().push(Instruction::String(variable_id, bytes.clone()));
                variable_id
            },
            Expression::Variable(..) | Expression::Dereference(..) | Expression::VariableDefinition(..)
            | Expression::Field(..) | Expression::NamedCall(..) | Expression::CallOrIndex(..) | Expression::Record(..) => {
                let (pointer_variable_id, is_lvalue) = self.try_generate_pointer_from_expression(expression, PointerType::Reference);
                if is_lvalue {
                    self.dereference_pointer(pointer_variable_id)
                } else {
                    pointer_variable_id
                }
            },
            Expression::Proc(name, ref type_expressions) => {
                let types: Vec<_> = type_expressions.iter().map(|e| self.compiler.resolve_type(e)).collect();
                if let Some(function_id) = self.compiler.lookup_function(expression_span, name, &types) {
                    let function = self.compiler.get_function_info(function_id);
                    let typ = self.compiler.type_function(function.arguments.clone(), function.return_type);
                    let output_variable = self.new_variable(Variable { typ, is_temporary: true });
                    self.instructions().push(Instruction::Function(output_variable, function_id));
                    output_variable
                } else {
                    self.generate_error()
                }
            },
            Expression::Operator(operator, ref left, ref right) => {
                if operator.is_binary() {
                    let instruction = match operator {
                        Operator::Plus => Instruction::Add,
                        Operator::Minus => Instruction::Subtract,
                        Operator::Times => Instruction::Multiply,
                        Operator::Divide => Instruction::Divide,
                        Operator::Modulo => Instruction::Modulo,
                        Operator::Equals => Instruction::Equals,
                        Operator::LessThan => Instruction::LessThan,
                        Operator::GreaterThan => Instruction::GreaterThan,
                        Operator::LessThanEquals => Instruction::LessThanEquals,
                        Operator::GreaterThanEquals => Instruction::GreaterThanEquals,
                        Operator::Is => {
                            let left_variable = self.generate_ir_from_expression(left, None);
                            let right_variable = self.generate_ir_from_expression(right, None);
                            let left_type = self.variables[left_variable].typ;
                            let right_type = self.variables[right_variable].typ;
                            let left_type_info = self.compiler.get_type_info(left_type);
                            let right_type_info = self.compiler.get_type_info(right_type);
                            match (left_type_info, right_type_info) {
                                (&Type::Pointer(pointer_type1, type1), &Type::Pointer(pointer_type2, type2)) if pointer_type1 == pointer_type2 && self.compiler.types_match(type1, type2) => {
                                    let variable = self.new_variable(Variable { typ: self.compiler.type_bool(), is_temporary: true });
                                    self.instructions().push(Instruction::Equals(variable, left_variable, right_variable));
                                    return variable
                                },
                                _ => {
                                    self.compiler.report_error(Error::InvalidOperandTypes { span: expression_span, operator, left: left_type, right: right_type });
                                    return self.generate_error()
                                },
                            }
                        },
                        Operator::And | Operator::Or => {
                            let condition_variable = self.generate_ir_from_expression(left, Some(self.compiler.type_bool()));
                            let condition_span = self.compiler.expression_span(left);
                            let condition_variable = self.autocast_variable_to_type(condition_variable, self.compiler.type_bool(), condition_span);

                            let branch = self.bb_index;
                            let then_branch = self.bbs.len();
                            self.bbs.push(vec![]);

                            self.bb_index = then_branch;
                            let then_variable = self.generate_ir_from_expression(right, Some(self.compiler.type_bool()));
                            let then_type = self.variables[then_variable].typ;
                            if !self.compiler.types_match(then_type, self.compiler.type_bool()) {
                                let span = self.compiler.expression_span(right);
                                self.compiler.report_error(Error::InvalidOperandType { span, typ: then_type });
                                return self.generate_error()
                            }
                            let then_end_index = self.bb_index;

                            let merge = self.bbs.len();
                            self.bbs.push(vec![]);
                            self.instructions().push(Instruction::Jump(merge));

                            if operator == Operator::And {
                                self.bbs[branch].push(Instruction::Branch(condition_variable, then_branch, merge));
                            } else {
                                self.bbs[branch].push(Instruction::Branch(condition_variable, merge, then_branch));
                            }

                            self.bb_index = merge;
                            let output_variable = self.new_variable(Variable { typ: self.compiler.type_bool(), is_temporary: true });
                            self.instructions().push(Instruction::Phi(output_variable, branch, condition_variable, then_end_index, then_variable));

                            return output_variable
                        },
                        Operator::Not => unreachable!(),
                    };

                    let name = operator.symbol();

                    let generic_integer = Some(self.compiler.type_primitive(PrimitiveType::GenericInteger));
                    let left_variable = self.generate_ir_from_expression(left, generic_integer);
                    let right_variable = self.generate_ir_from_expression(right, generic_integer);
                    let left_span = self.compiler.expression_span(left);
                    let right_span = self.compiler.expression_span(right);

                    let mut argument_variables = vec![left_variable, right_variable];
                    let argument_spans = vec![left_span, right_span];

                    if let Some((function_variable, output_variable, is_builtin)) = self.get_function_call_variables(expression_span, name, &mut argument_variables, argument_spans) {
                        if is_builtin {
                            self.instructions().push(instruction(output_variable, argument_variables[0], argument_variables[1]));
                        } else {
                            self.instructions().push(Instruction::Call(output_variable, function_variable, (*argument_variables).into()));
                        }
                        output_variable
                    } else {
                        self.generate_error()
                    }
                } else {
                    let instruction = match operator {
                        Operator::Not => Instruction::Not,
                        _ => unreachable!(),
                    };
                    let name = operator.symbol();

                    let generic_integer = Some(self.compiler.type_primitive(PrimitiveType::GenericInteger));
                    let right_variable = self.generate_ir_from_expression(right, generic_integer);
                    let right_span = self.compiler.expression_span(right);

                    let mut argument_variables = vec![right_variable];
                    let argument_spans = vec![right_span];

                    if let Some((function_variable, output_variable, is_builtin)) = self.get_function_call_variables(expression_span, name, &mut argument_variables, argument_spans) {
                        if is_builtin {
                            self.instructions().push(instruction(output_variable, argument_variables[0]));
                        } else {
                            self.instructions().push(Instruction::Call(output_variable, function_variable, (*argument_variables).into()));
                        }
                        output_variable
                    } else {
                        self.generate_error()
                    }
                }
            },
            Expression::Cast(ref subexpression, ref type_expression) => {
                let variable_id = self.generate_ir_from_expression(subexpression, None);
                let old_type = self.variables[variable_id].typ;
                let typ = self.compiler.resolve_type(type_expression);
                if let Some(cast_type) = self.compiler.can_cast(old_type, typ) {
                    let new_variable_id = self.new_variable(Variable { typ, is_temporary: true });
                    self.instructions().push(Instruction::Cast(cast_type, new_variable_id, variable_id));
                    new_variable_id
                } else {
                    self.compiler.report_error(Error::InvalidCast { span: expression_span, from: old_type.clone(), to: typ });
                    self.generate_error()
                }
            },
            Expression::Reference(ref subexpression) => {
                let variable_id = self.generate_pointer_from_expression(subexpression, PointerType::Reference);
                variable_id
            },
            Expression::MutableReference(ref subexpression) => {
                let variable_id = self.generate_pointer_from_expression(subexpression, PointerType::Mutable);
                variable_id
            },
            Expression::ArrayReference(ref subexpression) => {
                let variable_id = self.generate_pointer_from_expression(subexpression, PointerType::Array);
                variable_id
            },
            Expression::MutableArrayReference(ref subexpression) => {
                let variable_id = self.generate_pointer_from_expression(subexpression, PointerType::ArrayMutable);
                variable_id
            },
            Expression::Negate(ref subexpression) => {
                let sub_index = self.generate_ir_from_expression(subexpression, expected_type);
                let sub_variable = &self.variables[sub_index];

                let subtype = sub_variable.typ;
                match *self.compiler.get_type_info(subtype) {
                    Type::Integer8
                    | Type::Integer16
                    | Type::Integer32
                    | Type::Integer64
                    | Type::Offset => {
                        let output_variable = Variable { typ: subtype.clone(), is_temporary: true };
                        let output_index = self.new_variable(output_variable);

                        self.instructions().push(Instruction::Negate(output_index, sub_index));
                        output_index
                    },
                    Type::GenericInteger => {
                        // Since our variable has type GenericInteger, it must have been generated
                        // from an integer literal expression.  Hence the last instruction
                        // generated must be an Instruction::Integer, and we can just negate its
                        // value.
                        //
                        // This allows us to infer integer types even after we have applied a unary
                        // minus operation to them.
                        if let Some(&Instruction::Integer(variable, value)) = self.instructions().last() {
                            *self.instructions().last_mut().unwrap() = Instruction::Integer(variable, -value);
                            variable
                        } else {
                            unreachable!()
                        }
                    },
                    Type::Error => {
                        self.generate_error()
                    },
                    _ => {
                        self.compiler.report_error(Error::InvalidOperandType { span: expression_span, typ: subtype });
                        self.generate_error()
                    }
                }
            },
            Expression::Sizeof(ref type_expression) => {
                let variable = self.new_variable(Variable { typ: self.compiler.type_primitive(PrimitiveType::Size), is_temporary: true });
                let typ = self.compiler.resolve_type(type_expression);
                self.instructions().push(Instruction::Sizeof(variable, typ));
                variable
            },
            Expression::Alignof(ref type_expression) => {
                let variable = self.new_variable(Variable { typ: self.compiler.type_primitive(PrimitiveType::Size), is_temporary: true });
                let typ = self.compiler.resolve_type(type_expression);
                self.instructions().push(Instruction::Alignof(variable, typ));
                variable
            },
            Expression::Parentheses(ref subexpression) => {
                self.generate_ir_from_expression(subexpression, expected_type)
            },
        }
    }

    fn try_cast_pointer(&mut self, variable_id: VariableId, pointer_type: PointerType, span: &'source str) -> VariableId {
        let typ = self.variables[variable_id].typ;
        let type_info = self.compiler.get_type_info(typ);
        match *type_info {
            Type::Pointer(pointer_type2, subtype) => {
                if pointer_type2 == pointer_type {
                    // No need to cast
                    return variable_id
                } else {
                    match (pointer_type2, pointer_type) {
                        (PointerType::Mutable, PointerType::Reference)
                        | (PointerType::ArrayMutable, PointerType::Array)
                        | (PointerType::Array, PointerType::Reference)
                        | (PointerType::ArrayMutable, PointerType::Mutable)
                        | (PointerType::ArrayMutable, PointerType::Reference) => {
                            let new_type = self.compiler.type_pointer(pointer_type, subtype);
                            let new_variable_id = self.new_variable(Variable {
                                typ: new_type,
                                is_temporary: true,
                            });
                            self.instructions().push(Instruction::Cast(CastType::PointerType, new_variable_id, variable_id));
                            new_variable_id
                        },
                        (PointerType::Reference, PointerType::Mutable)
                        | (PointerType::Array, PointerType::ArrayMutable) => {
                            self.compiler.report_error(Error::ImmutableLvalue(span));
                            self.generate_error()
                        },
                        (PointerType::Reference, PointerType::Array)
                        | (PointerType::Mutable, PointerType::ArrayMutable)
                        | (PointerType::Reference, PointerType::ArrayMutable)
                        | (PointerType::Mutable, PointerType::Array) => {
                            self.compiler.report_error(Error::ArrayPointerToNonArray(span));
                            self.generate_error()
                        },
                        _ => unreachable!(),
                    }
                }
            },
            Type::Error => {
                self.generate_error()
            },
            _ => {
                self.compiler.report_error(Error::InvalidOperandType { span, typ });
                self.generate_error()
            },
        }
    }

    fn lookup_name(&mut self, name: &'source str, span: &'source str, pointer_type: PointerType) -> Option<(VariableId, bool)> { 
        let mut is_lvalue = true;
        let var = if let Some(&variable_id) = self.locals.get(&name) {
            self.try_cast_pointer(variable_id, pointer_type, span)
        } else if let Some(&global_id) = self.compiler.global_resolution_map.get(&name) {
            if self.compiler.global_is_constant[global_id] {
                return None
            }

            let (subtype, _) = self.compiler.globals[global_id];
            let typ = self.compiler.type_mut(subtype);
            let variable_id = self.new_variable(Variable { typ, is_temporary: true });
            self.instructions().push(Instruction::GlobalVariable(variable_id, global_id));
            self.try_cast_pointer(variable_id, pointer_type, span)
        } else if let Some(function_ids) = self.compiler.name_resolution_map.get(&name) {
            if function_ids.len() == 0 {
                // Probably shouldn't happen, but good to be sure
                self.compiler.report_error(Error::UndefinedVariable(name));
                self.generate_error()
            } else if function_ids.len() > 1 {
                self.compiler.report_error(Error::AmbiguousFunctionReference(name));
                self.generate_error()
            } else {
                is_lvalue = false;
                let function_id = function_ids[0];
                let function = self.compiler.get_function_info(function_id);
                let typ = self.compiler.type_function(function.arguments.clone(), function.return_type);
                let output_variable = self.new_variable(Variable { typ, is_temporary: true });
                self.instructions().push(Instruction::Function(output_variable, function_id));
                output_variable
            }
        } else {
            self.compiler.report_error(Error::UndefinedVariable(name));
            self.generate_error()
        };
        Some((var, is_lvalue))
    }

    fn generate_ir_for_index(&mut self, mut indexee_variable: VariableId, indexee_is_lvalue: bool, span: &'source str, indexee_span: &'source str, arguments: &'source [Box<Expression<'source>>], pointer_type: PointerType) -> (VariableId, bool) {
        let indexee_type = if indexee_is_lvalue {
            self.compiler.type_deref(self.variables[indexee_variable].typ)
        } else {
            self.variables[indexee_variable].typ
        };

        let mut is_lvalue = true;
        let type_size = self.compiler.type_primitive(PrimitiveType::Size);
        let var = match *self.compiler.get_type_info(indexee_type) {
            Type::Pointer(pointer_type2, subtype) => {
                if indexee_is_lvalue {
                    indexee_variable = self.dereference_pointer(indexee_variable);
                }

                let mut argument_variables: Vec<_> = arguments.iter().map(|x| self.generate_ir_from_expression(x, Some(type_size))).collect();
                if argument_variables.len() != 1 {
                    self.compiler.report_error(Error::InvalidNumberOfArgs(span))
                }
                let index_variable = argument_variables.pop().unwrap();

                let result_type = match pointer_type2 {
                    PointerType::Array => self.compiler.type_refs(subtype),
                    PointerType::ArrayMutable => self.compiler.type_muts(subtype),
                    _ => {
                        self.compiler.report_error(Error::InvalidOperandType { span: indexee_span, typ: indexee_type });
                        return (self.generate_error(), true)
                    },
                };
                let result_variable = self.new_variable(Variable { typ: result_type, is_temporary: true });
                self.instructions().push(Instruction::IndexPointer(result_variable, indexee_variable, index_variable));
                self.try_cast_pointer(result_variable, pointer_type, indexee_span)
            },
            Type::Array(_, subtype) => {
                if !indexee_is_lvalue {
                    self.compiler.report_error(Error::InvalidLvalue(span));
                    return (self.generate_error(), true)
                }
                let mut argument_variables: Vec<_> = arguments.iter().map(|x| self.generate_ir_from_expression(x, Some(type_size))).collect();
                if argument_variables.len() != 1 {
                    self.compiler.report_error(Error::InvalidNumberOfArgs(span))
                }
                let index_variable = argument_variables.pop().unwrap();

                let pointer_type2 = match *self.compiler.get_type_info(self.variables[indexee_variable].typ) {
                    Type::Pointer(pointer_type2, ..) => pointer_type2,
                    _ => unreachable!(),
                };
                let result_type = self.compiler.type_pointer(pointer_type2, subtype);
                let result_variable = self.new_variable(Variable { typ: result_type, is_temporary: true });
                self.instructions().push(Instruction::IndexArray(result_variable, indexee_variable, index_variable));
                self.try_cast_pointer(result_variable, pointer_type, indexee_span)
            },
            Type::Function { return_type, .. } => {
                if indexee_is_lvalue {
                    indexee_variable = self.dereference_pointer(indexee_variable);
                }

                is_lvalue = false;

                // TODO: use argument types for type inference instead of None
                let argument_variables: Vec<_> = arguments.iter().map(|x| self.generate_ir_from_expression(x, None)).collect();
                let output_variable = self.new_variable(Variable { typ: return_type, is_temporary: true });
                self.instructions().push(Instruction::Call(output_variable, indexee_variable, (*argument_variables).into()));
                output_variable
            },
            _ => {
                self.compiler.report_error(Error::InvalidOperandType { span: indexee_span, typ: indexee_type });
                self.generate_error()
            },
        };
        (var, is_lvalue)
    }

    /// Like `generate_ir_from_expression`, but returns a variable of pointer type.  Used for lvalues.
    fn generate_pointer_from_expression(&mut self, expression: &'source Expression<'source>, pointer_type: PointerType) -> VariableId {
        let (var, lvalue) = self.try_generate_pointer_from_expression(expression, pointer_type);
        if !lvalue {
            let span = self.compiler.expression_span(expression);
            self.compiler.report_error(Error::InvalidLvalue(span));
            self.generate_error()
        } else {
            var
        }
    }

    /// Tries to generate an lvalue from the given expression.
    ///
    /// If the given expression is not a valid lvalue, generates an rvalue instead and returns
    /// `false` as the second return value.
    fn try_generate_pointer_from_expression(&mut self, expression: &'source Expression<'source>, pointer_type: PointerType) -> (VariableId, bool) {
        let span = self.compiler.expression_span(expression);
        let mut is_lvalue = true;
        let var = match *expression {
            Expression::Variable(name) => {
                if let Some((variable_id, name_is_lvalue)) = self.lookup_name(name, span, pointer_type) {
                    is_lvalue = name_is_lvalue;
                    variable_id
                } else if let Some(&global_id) = self.compiler.global_resolution_map.get(name) {
                    if self.compiler.global_is_constant[global_id] {
                        let (typ, _) = self.compiler.globals[global_id];
                        let variable_id = self.new_variable(Variable { typ, is_temporary: true });
                        self.instructions().push(Instruction::GlobalConstant(variable_id, global_id));
                        return (variable_id, false)
                   } else {
                       self.compiler.report_error(Error::UndefinedVariable(name));
                       self.generate_error()
                    }
                } else {
                    self.compiler.report_error(Error::UndefinedVariable(name));
                    self.generate_error()
                }
            },
            Expression::VariableDefinition(ref name, ref type_expression) => {
                if self.locals_stack.contains(name) {
                    self.compiler.report_error(Error::ShadowedName(span, name.clone()));
                    self.generate_error()
                } else {
                    let typ = self.compiler.resolve_type(type_expression);
                    let variable_id = self.new_variable(Variable { typ: self.compiler.type_mut(typ), is_temporary: false });
                    self.instructions().push(Instruction::Allocate(variable_id));
                    self.locals_stack.push(name.clone());
                    self.locals.insert(name.clone(), variable_id);

                    self.try_cast_pointer(variable_id, pointer_type, span)
                }
            },
            Expression::Dereference(ref subexpression) => {
                let variable_id = self.generate_ir_from_expression(subexpression, None);
                let subspan = self.compiler.expression_span(subexpression);
                self.try_cast_pointer(variable_id, pointer_type, subspan)
            },
            Expression::Field(field_name, ref subexpression) => {
                let record_variable = self.generate_pointer_from_expression(subexpression, pointer_type);
                self.generate_ir_for_field_access(record_variable, field_name, pointer_type, span)
            },
            Expression::NamedCall(name, ref arguments) => {
                if self.compiler.name_resolution_map.contains_key(&name) {
                    is_lvalue = false;
                    let mut argument_variables: Vec<_> = arguments.iter().map(|x| self.generate_ir_from_expression(x, Some(self.compiler.type_primitive(PrimitiveType::GenericInteger)))).collect();
                    let argument_spans = arguments.iter().map(|x| self.compiler.expression_span(x)).collect();
                    if let Some((function_variable, output_variable, _)) = self.get_function_call_variables(span, name, &mut argument_variables, argument_spans) {
                        self.instructions().push(Instruction::Call(output_variable, function_variable, (*argument_variables).into()));
                        output_variable
                    } else {
                        self.generate_error()
                    }
                } else {
                    if let Some((variable_id, indexee_is_lvalue)) = self.lookup_name(name, span, pointer_type) {
                        let (var, is_lvalue2) = self.generate_ir_for_index(variable_id, indexee_is_lvalue, span, name, arguments, pointer_type);
                        is_lvalue = is_lvalue2;
                        var
                    } else {
                        self.compiler.report_error(Error::AttemptToCallOrIndexConstant(span));
                        self.generate_error()
                    }
                }
            },
            Expression::CallOrIndex(ref indexee_expression, ref arguments) => {
                let pointer_type2 = match pointer_type {
                    PointerType::Array | PointerType::Reference => PointerType::Reference,
                    PointerType::ArrayMutable | PointerType::Mutable => PointerType::Mutable,
                };
                let (indexee_variable, indexee_is_lvalue) = self.try_generate_pointer_from_expression(indexee_expression, pointer_type2);
                let indexee_span = self.compiler.expression_span(indexee_expression);
                let (var, is_lvalue2) = self.generate_ir_for_index(indexee_variable, indexee_is_lvalue, span, indexee_span, arguments, pointer_type);
                is_lvalue = is_lvalue2;
                var
            },
            Expression::Record(ref type_expression, ref fields) => {
                let typ = self.compiler.type_mut(self.compiler.resolve_type(type_expression));
                let output_variable = self.new_variable(Variable { typ, is_temporary: true });
                self.instructions().push(Instruction::Allocate(output_variable));

                for &(name, ref value) in fields.iter() {
                    let field_type_option = self.get_field_type(output_variable, name);
                    let value_variable = self.generate_ir_from_expression(value, field_type_option);
                    let span = self.compiler.expression_span(value);
                    let field_variable = self.generate_ir_for_field_access(output_variable, name, PointerType::Mutable, span);
                    self.instructions().push(Instruction::Store(field_variable, value_variable));
                }

                output_variable
            },
            Expression::Parentheses(ref subexpression) => {
                return self.try_generate_pointer_from_expression(subexpression, pointer_type)
            },
            _ => {
                is_lvalue = false;
                self.generate_ir_from_expression(expression, None)
            },
        };
        (var, is_lvalue)
    }

    fn get_field_type(&mut self, record_variable: VariableId, field_name: &'source str) -> Option<TypeId> {
        let typ = self.get_lvalue_type(record_variable);
        let type_info = self.compiler.get_type_info(typ);
        match *type_info {
            Type::Record(ref fields) => {
                fields.iter().find(|&&(ref field_name2, _)| {
                    **field_name2 == *field_name
                }).map(|&(_, field_type)| field_type)
            },
            _ => None,
        }
    }

    fn generate_ir_for_field_access(&mut self, record_variable: VariableId, field_name: &'source str, pointer_type: PointerType, span: &'source str) -> VariableId {
        match pointer_type {
            PointerType::Array | PointerType::ArrayMutable => {
                self.compiler.report_error(Error::ArrayPointerToNonArray(span));
                return self.generate_error()
            },
            _ => {}
        }

        let typ = self.get_lvalue_type(record_variable);
        let type_info = self.compiler.get_type_info(typ);
        match *type_info {
            Type::Record(ref fields) => {
                let field_type_option = fields.iter().find(|&&(ref field_name2, _)| {
                    **field_name2 == *field_name
                }).map(|&(_, field_type)| field_type);
                if let Some(field_type) = field_type_option {
                    let result_type = self.compiler.type_pointer(pointer_type, field_type);
                    let result_variable = self.new_variable(Variable { typ: result_type, is_temporary: true });
                    self.instructions().push(Instruction::Field(result_variable, record_variable, field_name));
                    result_variable
                } else {
                    self.compiler.report_error(Error::FieldDoesNotExist(span, typ, field_name));
                    self.generate_error()
                }
            },
            Type::String => {
                let (field_index, field_type) = match field_name {
                    "data" => (0, self.compiler.type_refs(self.compiler.type_primitive(PrimitiveType::Natural8))),
                    "length" => (1, self.compiler.type_primitive(PrimitiveType::Size)),
                    _ => {
                        self.compiler.report_error(Error::FieldDoesNotExist(span, typ, field_name));
                        return self.generate_error()
                    },
                };

                let result_type = self.compiler.type_pointer(pointer_type, field_type);
                let result_variable = self.new_variable(Variable { typ: result_type, is_temporary: true });
                self.instructions().push(Instruction::BuiltinField(result_variable, record_variable, field_index));
                result_variable
            },
            _ => {
                self.compiler.report_error(Error::FieldAccessOnNonRecord(span, typ));
                self.generate_error()
            },
        }
    }

    fn lookup_function(&mut self, span: &'source str, name: &'source str, argument_types: &[TypeId]) -> Option<(VariableId, &'source [TypeId], TypeId, bool)> {
        if let Some(&variable) = self.locals.get(&name) {
            let typ = self.get_lvalue_type(variable);
            let new_variable = self.new_variable(Variable {
                typ,
                is_temporary: true,
            });
            self.instructions().push(Instruction::Load(new_variable, variable));
            match *self.compiler.get_type_info(typ) {
                Type::Function { ref argument_types, return_type } => Some((new_variable, &**argument_types, return_type, false)),
                _ => {
                    self.compiler.report_error(Error::CallOfNonFunction(span, typ));
                    None
                },
            }
        } else if let Some(function_id) = self.compiler.lookup_function(span, name, argument_types) {
            let function = self.compiler.get_function_info(function_id);
            let typ = self.compiler.type_function(function.arguments.clone(), function.return_type);
            if function.is_builtin {
                Some((!0, &*function.arguments, function.return_type, true))
            } else {
                let variable = self.new_variable(Variable { typ, is_temporary: true });
                self.instructions().push(Instruction::Function(variable, function_id));
                Some((variable, &*function.arguments, function.return_type, false))
            }
        } else {
            None
        }
    }

    fn get_function_call_variables(&mut self, span: &'source str, name: &'source str, argument_variables: &mut [VariableId], argument_spans: Vec<&'source str>) -> Option<(VariableId, VariableId, bool)> {
        let argument_types: Box<[_]> = argument_variables.iter().map(|&x| self.variables[x].typ).collect();

        if argument_types.iter().any(|&x| self.compiler.is_error_type(x)) {
            return None
        }

        self.lookup_function(span, name, &argument_types).map(|(function_variable, arguments, return_type, is_builtin)| {
            debug_assert_eq!(arguments.len(), argument_variables.len());

            for (i, (&expected_type, found_variable)) in arguments.iter().zip(argument_variables.iter_mut()).enumerate() {
                *found_variable = self.autocast_variable_to_type(*found_variable, expected_type, argument_spans[i]);
            }

            let variable = self.new_variable(Variable { typ: return_type.clone(), is_temporary: true });
            (function_variable, variable, is_builtin)
        })
    }
}

impl<'source> fmt::Display for IrGenerator<'source> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{}", FunctionPrinter(self.compiler, self.function.id))?;

        for (i, variable) in self.variables.iter().enumerate() {
            writeln!(f, "VAR %{}: {}", i, TypePrinter(self.compiler, variable.typ))?;
        }

        let mut first = true;
        for (bb_index, bb) in self.bbs.iter().enumerate() {
            if !first {
                writeln!(f, "")?;
            }
            first = false;
            write!(f, "@{}", bb_index)?;

            for instruction in bb.iter() {
                write!(f, "\n  ")?;

                match *instruction {
                    Instruction::Integer(destination, value) => write!(f, "%{} = {}", destination, value)?,
                    Instruction::Float(destination, value) => write!(f, "%{} = {}", destination, value)?,
                    Instruction::Null(destination) => write!(f, "%{} = null", destination)?,
                    Instruction::Bool(destination, is_true) => write!(f, "%{} = {:?}", destination, is_true)?,
                    Instruction::String(destination, ref bytes) => write!(f, "%{} = {:?}", destination, String::from_utf8_lossy(bytes))?,

                    Instruction::Sizeof(destination, typ) => write!(f, "%{} = sizeof {}", destination, TypePrinter(self.compiler, typ))?,
                    Instruction::Alignof(destination, typ) => write!(f, "%{} = alignof {}", destination, TypePrinter(self.compiler, typ))?,

                    Instruction::Call(destination, variable, ref arguments) => {
                        write!(f, "%{} = call %{}", destination, variable)?;
                        for argument in arguments.iter() {
                            write!(f, ", {}", argument)?;
                        }
                    },

                    Instruction::Allocate(destination) => write!(f, "%{} = alloc", destination)?,
                    Instruction::Load(destination, source) => write!(f, "%{} = load %{}", destination, source)?,
                    Instruction::Store(destination, source) => write!(f, "in %{} store %{}", destination, source)?,
                    Instruction::Field(destination, source, field_name) => write!(f, "%{} = fieldptr %{}, {}", destination, source, field_name)?,
                    Instruction::BuiltinField(destination, source, field_index) => write!(f, "%{} = builtinfieldptr %{}, {}", destination, source, field_index)?,
                    Instruction::IndexPointer(destination, source, index) => write!(f, "%{} = indexptr %{}, %{}", destination, source, index)?,
                    Instruction::IndexArray(destination, source, index) => write!(f, "%{} = indexarray %{}, %{}", destination, source, index)?,

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

                    Instruction::Function(variable, function) => write!(f, "%{} = global ${}", variable, FunctionPrinter(self.compiler, function))?,
                    Instruction::GlobalVariable(variable, global_id) => write!(f, "%{} = globalvar %{}", variable, global_id)?,
                    Instruction::GlobalConstant(variable, global_id) => write!(f, "%{} = globalconst %{}", variable, global_id)?,

                    Instruction::Not(variable1, variable2) => write!(f, "%{} = not %{}", variable1, variable2)?,
                    Instruction::Negate(variable1, variable2) => write!(f, "%{} = negate %{}", variable1, variable2)?,

                    Instruction::Cast(cast_type, variable1, variable2) => {
                        let type1 = self.variables[variable1].typ;
                        let type2 = self.variables[variable2].typ;
                        write!(f, "%{} = cast {:?} [{} to {}] %{}", variable1, cast_type, TypePrinter(self.compiler, type2), TypePrinter(self.compiler, type1), variable2)?;
                    },

                    Instruction::Return(variable) => write!(f, "return %{}", variable)?,
                    Instruction::Jump(index) => write!(f, "jump @{}", index)?,
                    Instruction::Branch(variable, index1, index2) => write!(f, "branch %{}, @{}, @{}", variable, index1, index2)?,
                    Instruction::Unreachable => write!(f, "unreachable")?,
                    Instruction::Phi(variable, index1, variable1, index2, variable2) => write!(f, "%{} = phi @{} => %{}, @{} => %{}", variable, index1, variable1, index2, variable2)?,

                    Instruction::BreakPlaceholder => write!(f, "<break placeholder>")?,
                    Instruction::Error(destination) => write!(f, "%{} = error", destination)?,
                }
            }
        }

        Ok(())
    }
}
