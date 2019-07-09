use std::fmt;
use std::cell::Cell;
use std::collections::HashMap;
use typed_arena::Arena;
use crate::parse::{FunctionSignature, FunctionName, Definition, Expression, Statement};
use crate::frontend::Options;

pub struct Compiler<'source> {
    pub name_resolution_map: HashMap<&'source FunctionName<'source>, Vec<Function>>,
    pub signature_resolution_map: HashMap<*const FunctionSignature<'source>, Function>,
    pub has_errors: Cell<bool>,

    pub expression_spans: HashMap<*const Expression<'source>, &'source str>,
    pub statement_spans: HashMap<*const Statement<'source>, &'source str>,
    pub definition_spans: HashMap<*const Definition<'source>, &'source str>,

    pub options: Options,

    pub source: &'source str,

    primitive_types: Box<[TypeId; PrimitiveType::NumberOfPrimitives as usize]>,
    type_arena: &'source Arena<Type>,

    pub type_resolution_map: HashMap<&'source str, TypeId>,
    reverse_type_resolution_map: HashMap<*mut Type, &'source str>,
}

#[derive(Debug, Clone)]
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
    Pointer(PointerType, TypeId),
    Record {
        name: Box<str>,
        fields: Box<[(Box<str>, TypeId)]>,
    },
    Error,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PointerType {
    Reference,
    Mutable,
    Array,
    ArrayMutable,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: Box<[Option<Box<str>>]>,
    pub arguments: Box<[TypeId]>,
    pub return_type: TypeId,
    pub is_extern: bool,
}

/// A function name together with its argument types.
///
/// This is used for error messages.
#[derive(Debug, Clone)]
pub struct FunctionIdentifier {
    pub name: Box<[Option<Box<str>>]>,
    pub arguments: Box<[TypeId]>,
}

#[derive(Debug)]
pub enum Error<'source> {
    ParseError(crate::parse::Error<'source>),
    UndefinedVariable(&'source str),
    ShadowedName(&'source str),
    UndefinedFunction(&'source str, FunctionIdentifier),
    NoOverloadForFunction(&'source str, FunctionIdentifier),
    AmbiguousOverload(&'source str, FunctionIdentifier),
    UnexpectedType { span: &'source str, expected: TypeId, found: TypeId },
    InvalidOperandTypes { span: &'source str, left: TypeId, right: TypeId },
    InvalidOperandType { span: &'source str, typ: TypeId },
    FunctionMightNotReturn(&'source str),
    BreakOutsideLoop(&'source str),
    ContinueOutsideLoop(&'source str),
    InvalidLvalue(&'source str),
    ImmutableLvalue(&'source str),
    ArrayPointerToNonArray(&'source str),
    InvalidCast { span: &'source str, from: TypeId, to: TypeId },
    InvalidExternFunctionName(&'source str, Function),
    UndefinedType(&'source str),
    FieldAccessOnNonRecord(&'source str, TypeId),
    FieldDoesNotExist(&'source str, TypeId, &'source str),
}

impl Type {
    pub fn is_integral(&self) -> bool {
        match *self {
            Type::Natural8 | Type::Natural16 | Type::Natural32 | Type::Natural64
            | Type::Integer8 | Type::Integer16 | Type::Integer32 | Type::Integer64 => true,
            _ => false,
        }
    }
}

/// An opaque type that identifies a type.
///
/// Note that the relationship between a `Type` and its `TypeId` is not one-to-one: the same `Type`
/// can have multiple corresponding `TypeId`s.
#[derive(Copy, Clone, Debug)]
pub struct TypeId(*mut Type);

pub struct TypePrinter<'source>(pub &'source Compiler<'source>, pub TypeId);

impl<'source> fmt::Display for TypePrinter<'source> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        if let Some(name) = self.0.reverse_type_resolution_map.get(&self.1 .0) {
            write!(formatter, "{}", name)?;
            return Ok(())
        }

        let type_info = self.0.get_type_info(self.1);
        let string = match *type_info {
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
            Type::Pointer(PointerType::Reference, subtype) => {
                write!(formatter, "ref {}", TypePrinter(self.0, subtype))?;
                ""
            },
            Type::Pointer(PointerType::Mutable, subtype) => {
                write!(formatter, "mut {}", TypePrinter(self.0, subtype))?;
                ""
            },
            Type::Pointer(PointerType::Array, subtype) => {
                write!(formatter, "refs {}", TypePrinter(self.0, subtype))?;
                ""
            },
            Type::Pointer(PointerType::ArrayMutable, subtype) => {
                write!(formatter, "muts {}", TypePrinter(self.0, subtype))?;
                ""
            },
            Type::Record { ref name, .. } => {
                write!(formatter, "{}", name)?;
                ""
            },
            Type::Error => "<error>",
        };

        write!(formatter, "{}", string)
    }
}

pub struct FunctionPrinter<'source>(pub &'source Compiler<'source>, pub &'source Function);

impl<'source> fmt::Display for FunctionPrinter<'source> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "(")?;

        let mut i = 0;

        let mut written_anything = false;

        for part in self.1.name.iter() {
            if written_anything {
                write!(formatter, " ")?;
            }

            match *part {
                Some(ref x) => write!(formatter, "{}", x)?,
                None => {
                    write!(formatter, ":{}", TypePrinter(self.0, self.1.arguments[i]))?;
                    i += 1;
                },
            }

            written_anything = true;
        }

        write!(formatter, "): {}", TypePrinter(self.0, self.1.return_type))
    }
}

pub struct FunctionIdentifierPrinter<'source>(&'source Compiler<'source>, &'source FunctionIdentifier);

impl<'source> fmt::Display for FunctionIdentifierPrinter<'source> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "(")?;

        let mut i = 0;

        let mut written_anything = false;

        for part in self.1.name.iter() {
            if written_anything {
                write!(formatter, " ")?;
            }

            match *part {
                Some(ref x) => write!(formatter, "{}", x)?,
                None => {
                    write!(formatter, ":{}", TypePrinter(self.0, self.1.arguments[i]))?;
                    i += 1;
                },
            }

            written_anything = true;
        }

        write!(formatter, ")")
    }
}

#[repr(usize)]
pub enum PrimitiveType {
    Integer8 = 0,
    Integer16,
    Integer32,
    Integer64,
    Natural8,
    Natural16,
    Natural32,
    Natural64,
    Bool,
    Null,
    Error,
    NumberOfPrimitives,
}

impl<'source> Compiler<'source> {
    pub fn new(options: Options, source: &'source str, type_arena: &'source mut Arena<Type>) -> Self {
        const SIZE: usize = PrimitiveType::NumberOfPrimitives as usize;
        let mut primitive_types = Box::new([TypeId(0 as *mut _); SIZE]);
        for i in 0..SIZE {
            let type_info = match i {
                0 => Type::Integer8,
                1 => Type::Integer16,
                2 => Type::Integer32,
                3 => Type::Integer64,
                4 => Type::Natural8,
                5 => Type::Natural16,
                6 => Type::Natural32,
                7 => Type::Natural64,
                8 => Type::Bool,
                9 => Type::Null,
                10 => Type::Error,
                _ => unreachable!(),
            };
            let pointer = type_arena.alloc(type_info);
            primitive_types[i] = TypeId(pointer);
        }

        Self {
            name_resolution_map: HashMap::with_capacity(32),
            signature_resolution_map: HashMap::with_capacity(32),
            has_errors: Cell::new(false),
            expression_spans: HashMap::with_capacity(1024),
            statement_spans: HashMap::with_capacity(1024),
            definition_spans: HashMap::with_capacity(64),
            options,
            source,
            type_arena,
            type_resolution_map: HashMap::with_capacity(32),
            reverse_type_resolution_map: HashMap::with_capacity(32),
            primitive_types,
        }
    }

    pub fn new_type_id(&self, typ: Type) -> TypeId {
        let type_id = TypeId(self.type_arena.alloc(typ.clone()));
        type_id
    }

    pub fn get_type_info(&self, type_id: TypeId) -> &Type {
        // This is safe so long as all TypeIds come from functions like `Compiler::new_type_id`
        // that generate pointers to `self.type_arena`, since all memory allocated in that arena
        // stays around while the `Compiler` still exists.
        unsafe {
            &*type_id.0
        }
    }

    pub fn is_error_type(&self, type_id: TypeId) -> bool {
        if let Type::Error = *self.get_type_info(type_id) { true } else { false }
    }

    pub fn type_primitive(&self, primitive: PrimitiveType) -> TypeId {
        self.primitive_types[primitive as usize]
    }

    pub fn type_error(&self) -> TypeId {
        self.type_primitive(PrimitiveType::Error)
    }

    pub fn type_bool(&self) -> TypeId {
        self.type_primitive(PrimitiveType::Bool)
    }

    pub fn type_null(&self) -> TypeId {
        self.type_primitive(PrimitiveType::Null)
    }

    pub fn type_pointer(&self, pointer_type: PointerType, other: TypeId) -> TypeId {
        self.new_type_id(Type::Pointer(pointer_type, other))
    }

    pub fn type_ref(&self, other: TypeId) -> TypeId {
        self.new_type_id(Type::Pointer(PointerType::Reference, other))
    }

    pub fn type_mut(&self, other: TypeId) -> TypeId {
        self.new_type_id(Type::Pointer(PointerType::Mutable, other))
    }

    pub fn type_refs(&self, other: TypeId) -> TypeId {
        self.new_type_id(Type::Pointer(PointerType::Array, other))
    }

    pub fn type_muts(&self, other: TypeId) -> TypeId {
        self.new_type_id(Type::Pointer(PointerType::ArrayMutable, other))
    }

    pub fn can_autocast(&self, from: TypeId, to: TypeId) -> bool {
        if self.types_match(from, to) {
            return true
        }

        let type1 = self.get_type_info(from);
        let type2 = self.get_type_info(to);

        match (type1, type2) {
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
            // mut -> ref, muts -> refs
            (&Type::Pointer(pointer_type1, typ1), &Type::Pointer(pointer_type2, typ2))
                if self.can_autocast_pointer_type(pointer_type1, pointer_type2) && self.types_match(typ1, typ2)
              => true,
            _ => false,
        }
    }

    pub fn can_autocast_pointer_type(&self, from: PointerType, to: PointerType) -> bool {
        if from == to { return true }

        match (from, to) {
            (PointerType::Mutable, PointerType::Reference) => true,
            (PointerType::ArrayMutable, PointerType::Array) => true,
            _ => false,
        }
    }

    pub fn can_cast(&self, from: TypeId, to: TypeId) -> bool {
        if self.can_autocast(from, to) {
            true
        } else {
            let type1 = self.get_type_info(from);
            let type2 = self.get_type_info(to);
            match (type1, type2) {
                (_, _) if type1.is_integral() && type2.is_integral() => true,
                (&Type::Pointer(type1, _), &Type::Pointer(type2, _)) if type1 == type2 => true,
                _ => false,
            }
        }
    }

    pub fn types_match(&self, type_id1: TypeId, type_id2: TypeId) -> bool {
        let type1 = self.get_type_info(type_id1);
        let type2 = self.get_type_info(type_id2);
        match (type1, type2) {
            (&Type::Integer8, &Type::Integer8) => true,
            (&Type::Integer16, &Type::Integer16) => true,
            (&Type::Integer32, &Type::Integer32) => true,
            (&Type::Integer64, &Type::Integer64) => true,
            (&Type::Natural8, &Type::Natural8) => true,
            (&Type::Natural16, &Type::Natural16) => true,
            (&Type::Natural32, &Type::Natural32) => true,
            (&Type::Natural64, &Type::Natural64) => true,
            (&Type::Bool, &Type::Bool) => true,
            (&Type::Null, &Type::Null) => true,
            (&Type::Pointer(type1, subtype1), &Type::Pointer(type2, subtype2)) => type1 == type2 && self.types_match(subtype1, subtype2),
            (&Type::Record { name: ref name1, fields: ref fields1 }, &Type::Record { name: ref name2, fields: ref fields2 }) => {
                if name1 != name2 {
                    return false
                }

                if fields1.len() != fields2.len() {
                    return false
                }

                for (&(ref field_name1, field_type1), &(ref field_name2, field_type2)) in fields1.iter().zip(fields2.iter()) {
                    if field_name1 != field_name2 || !self.types_match(field_type1, field_type2) {
                        return false
                    }
                }

                true
            },
            (&Type::Error, &Type::Error) => true,
            _ => false,
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
            ParseError(UnexpectedEndOfFile(span)) => {
                eprintln!("unexpected end of file");
                print_span(self.source, span);
            },
            ParseError(InvalidEscapeSequence(span)) => {
                eprintln!("invalid escape sequence");
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
            UndefinedFunction(span, ref identifier) => {
                eprintln!("undefined function: {}", FunctionIdentifierPrinter(self, identifier));
                print_span(self.source, span);
            },
            NoOverloadForFunction(span, ref identifier) => {
                eprintln!("no matching overload for function: {}", FunctionIdentifierPrinter(self, identifier));
                print_span(self.source, span);
            },
            AmbiguousOverload(span, ref identifier) => {
                eprintln!("call to overloaded function is ambiguous: {}", FunctionIdentifierPrinter(self, identifier));
                print_span(self.source, span);
            },
            UnexpectedType { span, expected, found } => {
                eprintln!("invalid type: expected {}, found {}", TypePrinter(self, expected), TypePrinter(self, found));
                print_span(self.source, span);
            },
            InvalidOperandTypes { span, left, right } => {
                eprintln!("invalid operand types: {}, {}", TypePrinter(self, left), TypePrinter(self, right));
                print_span(self.source, span);
            },
            InvalidOperandType { span, typ } => {
                eprintln!("invalid operand type: {}", TypePrinter(self, typ));
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
            ArrayPointerToNonArray(span) => {
                eprintln!("attempt to take array reference to non-array lvalue");
                print_span(self.source, span);
            },
            InvalidCast { span, from, to } => {
                eprintln!("invalid cast: {} to {}", TypePrinter(self, from), TypePrinter(self, to));
                print_span(self.source, span);
            },
            InvalidExternFunctionName(span, ref function) => {
                eprintln!("invalid extern function signature: {}", FunctionPrinter(self, function));
                print_span(self.source, span);
            },
            UndefinedType(span) => {
                eprintln!("undefined type: {}", span);
                print_span(self.source, span);
            },
            FieldAccessOnNonRecord(span, typ) => {
                eprintln!("attempt to set or access field of non-record: {}", TypePrinter(self, typ));
                print_span(self.source, span);
            },
            FieldDoesNotExist(span, typ, field_name) => {
                eprintln!("type {} has no field named '{}'", TypePrinter(self, typ), field_name);
                print_span(self.source, span);
            },
        }
    }

    pub fn resolve_type(&self, typ: &Expression) -> TypeId {
        let span = self.expression_span(typ);
        match *typ {
            Expression::Variable("int8")  => self.type_primitive(PrimitiveType::Integer8),
            Expression::Variable("int16") => self.type_primitive(PrimitiveType::Integer16),
            Expression::Variable("int32") => self.type_primitive(PrimitiveType::Integer32),
            Expression::Variable("int64") => self.type_primitive(PrimitiveType::Integer64),
            Expression::Variable("nat8")  => self.type_primitive(PrimitiveType::Natural8),
            Expression::Variable("nat16") => self.type_primitive(PrimitiveType::Natural16),
            Expression::Variable("nat32") => self.type_primitive(PrimitiveType::Natural32),
            Expression::Variable("nat64") => self.type_primitive(PrimitiveType::Natural64),
            Expression::Variable("bool")  => self.type_primitive(PrimitiveType::Bool),
            Expression::Variable(name) => {
                if let Some(&typ) = self.type_resolution_map.get(name) {
                    typ
                } else {
                    self.report_error(Error::UndefinedType(span));
                    self.type_error()
                }
            },
            Expression::Null => self.type_null(),
            Expression::Reference(ref subexpression) => self.type_ref(self.resolve_type(subexpression)),
            Expression::MutableReference(ref subexpression) => self.type_mut(self.resolve_type(subexpression)),
            Expression::ArrayReference(ref subexpression) => self.type_refs(self.resolve_type(subexpression)),
            Expression::MutableArrayReference(ref subexpression) => self.type_muts(self.resolve_type(subexpression)),
            _ => {
                self.report_error(Error::UndefinedType(span));
                self.type_error()
            },
        }
    }

    pub fn load_type_definition(&mut self, definition: &'source Definition<'source>) {
        match *definition {
            Definition::Type(name, ..) | Definition::Record(name, ..) => {
                // Make a new placeholder TypeId to be filled in with real type information later
                let type_id = TypeId(self.type_arena.alloc(Type::Error));
                self.type_resolution_map.insert(name, type_id);
                self.reverse_type_resolution_map.insert(type_id.0, name);
            },
            Definition::Function(..) | Definition::Extern(..) => {},
        }
    }

    pub fn load_function_definition(&mut self, definition: &'source Definition<'source>) {
        match *definition {
            Definition::Function(ref signature, ..) | Definition::Extern(ref signature) => {
                let name: Box<_> = signature.name.iter().map(|part| part.map(|x| x.into())).collect();
                let arguments: Box<_> = signature.arguments.iter().map(|&(_, ref type_expression)| self.resolve_type(type_expression)).collect();
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

                self.name_resolution_map.entry(&signature.name)
                    .and_modify(|v| v.push(function.clone()))
                    .or_insert_with(|| vec![function.clone()]);
                self.signature_resolution_map.insert(signature, function);
            },
            Definition::Type(name, ref type_expression) => {
                let type_id = self.resolve_type(type_expression);
                let typ = self.get_type_info(type_id).clone();
                let TypeId(pointer) = self.type_resolution_map[name];
                unsafe {
                    *pointer = typ;
                }
            },
            Definition::Record(name, ref fields) => {
                let mut resolved_fields = vec![];
                for &(field_name, ref type_expression) in fields.iter() {
                    resolved_fields.push((field_name.into(), self.resolve_type(type_expression)));
                }
                let typ = Type::Record { name: name.into(), fields: resolved_fields.into() };
                let TypeId(pointer) = self.type_resolution_map[name];
                unsafe {
                    *pointer = typ;
                }
            },
        }
    }

    /// Look for a function with the given name that matches the given argument types.
    ///
    /// Because we have implicit typecasts like `mut T -> ref T`, this isn't as easy as it sounds:
    /// sometimes multiple functions could be possible matches for the given argument types.  So we
    /// need a strategy to decide which function to use, and when to declare that the situation is
    /// too ambiguous and reject all options.  Such a strategy should have the following
    /// properties:
    ///
    /// 1. Exact type matches always work: if the arguments have type `(mut T, mut U)` and there is
    ///    a function with argument types `(mut T, mut U)`, then we should pick that function.
    /// 2. If one argument has the same type in every matching function, it should never cause the
    ///    algorithm to reject declare an ambiguity.  For instance, if we have two functions
    ///    `(Format :T To :mut nat8)` and `(Format :U To :mut nat8)`, the `mut nat8` parameter
    ///    should be able to be ignored as far as the matching strategy is concerned.
    ///
    /// This function employs the obvious algorithm that satisfies the above properties.
    pub fn lookup_function(&self, span: &'source str, name: &'source FunctionName<'source>, argument_types: &[TypeId]) -> Option<&Function> {
        // FIXME(cleanup): this code isn't ideal and could probably be simplified & optimized
        let function_identifier = FunctionIdentifier {
            name: name.iter().map(|x| x.map(|y| y.into())).collect(),
            arguments: argument_types.into(),
        };

        if let Some(functions) = self.name_resolution_map.get(&name) {
            let candidates: Box<[_]> = functions.iter()
                // Can we autocast our parameters to match this function's types?
                .filter(|function| argument_types.iter().zip(function.arguments.iter()).all(|(&x, &y)| self.can_autocast(x, y))).collect();

            if candidates.len() == 0 {
                self.report_error(Error::NoOverloadForFunction(span, function_identifier));
                return None
            }

            let candidate1 = &candidates[0];
            let ignorable = candidates.iter().fold(
                vec![true; argument_types.len()],
                |mut x, candidate| {
                    for i in 0..x.len() {
                        x[i] &= self.types_match(candidate.arguments[i], candidate1.arguments[i]);
                    }
                    x
                }
            );

            for function in candidates.iter() {
                if function.arguments.iter()
                    .zip(argument_types.iter())
                    .enumerate()
                    .filter(|&(i, _)| !ignorable[i])
                    .all(|(_, (&x, &y))| self.types_match(x, y))
                {
                    // We have a match!
                    return Some(function)
                }
            }

            self.report_error(Error::AmbiguousOverload(span, function_identifier));
            None
        } else {
            self.report_error(Error::UndefinedFunction(span, function_identifier));
            None
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
