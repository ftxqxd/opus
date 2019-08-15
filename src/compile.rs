use std::fmt;
use std::cell::Cell;
use std::collections::HashMap;
use std::path::PathBuf;
use typed_arena::Arena;
use crate::parse::{self, FunctionSignature, FunctionName, Definition, Expression, Statement, Operator, Name};
use crate::frontend::Options;

pub struct Compiler<'source> {
    pub name_resolution_map: HashMap<Box<FunctionName<'source>>, Vec<FunctionId>>,
    pub signature_resolution_map: HashMap<*const FunctionSignature<'source>, FunctionId>,
    function_arena: &'source Arena<Function>,

    pub variable_resolution_map: HashMap<Name<'source>, GlobalId>,
    pub globals: Vec<(TypeId, Value)>,

    pub has_errors: Cell<bool>,

    pub expression_spans: HashMap<*const Expression<'source>, &'source str>,
    pub type_spans: HashMap<*const parse::Type<'source>, &'source str>,
    pub statement_spans: HashMap<*const Statement<'source>, &'source str>,
    pub definition_spans: HashMap<*const Definition<'source>, &'source str>,

    pub options: Options,

    pub sources: Vec<&'source str>,
    pub filenames: Vec<PathBuf>,

    primitive_types: Box<[TypeId; PrimitiveType::NumberOfPrimitives as usize]>,
    type_arena: &'source Arena<Type>,

    pub type_resolution_map: HashMap<&'source str, TypeId>,
    reverse_type_resolution_map: HashMap<*mut Type, &'source str>,
}

#[derive(Debug, Clone)]
pub enum Value {
    None,
    Integer(i64),
    Error,
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
    /// This is an internal type used to resolve integer literal types in function calls.  See
    /// `Compiler::lookup_function`.
    GenericInteger,
    /// This is an internal type used to resolve procedure name expressions like `proc (Foo :)`
    /// which don't specify types.
    Generic,
    Bool,
    Null,
    Pointer(PointerType, TypeId),
    Record(Box<[(Box<str>, TypeId)]>),
    Function {
        argument_types: Box<[TypeId]>,
        return_type: TypeId,
    },
    Array(u64, TypeId),
    Error,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CastType {
    /// A 'cast' between a type and itself.
    None,
    /// A cast between two pointers that point to different things.
    Pointer,
    /// A cast between two pointers of different `PointerType`.
    PointerType,
    /// A cast between two integer types.
    Integer,
    /// A cast from any pointer type to an integer type.
    PointerToInteger,
    /// A cast from an integer type to any pointer type.
    IntegerToPointer,
    /// A cast from a pointer to an array to an array pointer.
    PointerToArray,
    /// Any internal cast that should not actually appear in the IR.
    Error,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PointerType {
    Reference,
    Mutable,
    Array,
    ArrayMutable,
}

#[derive(Debug)]
pub struct Function {
    pub name: Box<[Option<Box<str>>]>,
    pub arguments: Box<[TypeId]>,
    pub return_type: TypeId,
    pub is_extern: bool,
    pub is_builtin: bool,
    pub id: FunctionId,
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
    ShadowedName(&'source str, Name<'source>),
    UndefinedFunction(&'source str, FunctionIdentifier),
    NoOverloadForFunction(&'source str, FunctionIdentifier),
    AmbiguousOverload(&'source str, FunctionIdentifier),
    UnexpectedType { span: &'source str, expected: TypeId, found: TypeId },
    InvalidType { span: &'source str, typ: TypeId },
    InvalidOperandType { span: &'source str, typ: TypeId },
    InvalidOperandTypes { span: &'source str, operator: Operator, left: TypeId, right: TypeId },
    FunctionMightNotReturn(&'source str),
    BreakOutsideLoop(&'source str),
    ContinueOutsideLoop(&'source str),
    InvalidLvalue(&'source str),
    ImmutableLvalue(&'source str),
    ArrayPointerToNonArray(&'source str),
    InvalidCast { span: &'source str, from: TypeId, to: TypeId },
    InvalidExternFunctionName(&'source str, FunctionId),
    UndefinedType(&'source str),
    FieldAccessOnNonRecord(&'source str, TypeId),
    FieldDoesNotExist(&'source str, TypeId, &'source str),
    CallOfNonFunction(&'source str, TypeId),
    ReferenceToBuiltinFunction(&'source str),
    InvalidConstantExpression(&'source str),
}

impl Value {
    pub fn type_is_valid(&self, typ: &Type) -> bool {
        match *self {
            Value::Error => return true,
            _ => {}
        }

        match *typ {
            Type::Natural8 | Type::Natural16 | Type::Natural32 | Type::Natural64
            | Type::Integer8 | Type::Integer16 | Type::Integer32 | Type::Integer64 => match *self {
                Value::Integer(..) => true,
                _ => false,
            },
            _ => false,
        }
    }
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

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct FunctionId(*mut Function);

pub type GlobalId = usize;

impl FunctionId {
    fn null() -> Self {
        FunctionId(std::ptr::null_mut())
    }
}

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
            Type::GenericInteger => "<integer>",
            Type::Generic => "<unknown>",
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
            Type::Record(ref fields) => {
                write!(formatter, "record {{")?;
                for &(ref name, type_id) in fields.iter() {
                    write!(formatter, " {}: {}", name, TypePrinter(self.0, type_id))?;
                }
                write!(formatter, " }}")?;
                ""
            },
            Type::Function { ref argument_types, return_type } => {
                write!(formatter, "proc (")?;
                let mut printed_anything = false;
                for &argument_type in argument_types.iter() {
                    if printed_anything {
                        write!(formatter, " ")?;
                    }
                    printed_anything = true;
                    write!(formatter, "{}", TypePrinter(self.0, argument_type))?;
                }
                write!(formatter, ") {}", TypePrinter(self.0, return_type))?;
                ""
            },
            Type::Array(size, subtype) => {
                write!(formatter, "{{{}}} {}", size, TypePrinter(self.0, subtype))?;
                ""
            },
            Type::Error => "<error>",
        };

        write!(formatter, "{}", string)
    }
}

pub struct FunctionPrinter<'source>(pub &'source Compiler<'source>, pub FunctionId);

impl<'source> fmt::Display for FunctionPrinter<'source> {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let function = self.0.get_function_info(self.1);

        write!(formatter, "(")?;

        let mut i = 0;

        let mut written_anything = false;

        for part in function.name.iter() {
            if written_anything {
                write!(formatter, " ")?;
            }

            match *part {
                Some(ref x) => write!(formatter, "{}", x)?,
                None => {
                    write!(formatter, ":{}", TypePrinter(self.0, function.arguments[i]))?;
                    i += 1;
                },
            }

            written_anything = true;
        }

        write!(formatter, "): {}", TypePrinter(self.0, function.return_type))
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
#[derive(Debug, Copy, Clone)]
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
    GenericInteger,
    Generic,
    NumberOfPrimitives,
}

#[derive(Debug, Copy, Clone)]
pub enum FrontendDirective<'source> {
    None,
    Import(&'source [u8]),
    Library(&'source [u8]),
}

impl<'source> Compiler<'source> {
    pub fn new(options: Options, type_arena: &'source mut Arena<Type>, function_arena: &'source mut Arena<Function>) -> Self {
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
                11 => Type::GenericInteger,
                12 => Type::Generic,
                _ => unreachable!(),
            };
            let pointer = type_arena.alloc(type_info);
            primitive_types[i] = TypeId(pointer);
        }

        let mut this = Self {
            name_resolution_map: HashMap::with_capacity(128),
            signature_resolution_map: HashMap::with_capacity(32),
            function_arena,
            variable_resolution_map: HashMap::with_capacity(8),
            globals: Vec::with_capacity(8),
            has_errors: Cell::new(false),
            expression_spans: HashMap::with_capacity(1024),
            type_spans: HashMap::with_capacity(64),
            statement_spans: HashMap::with_capacity(1024),
            definition_spans: HashMap::with_capacity(64),
            options,
            sources: vec![],
            filenames: vec![],
            type_arena,
            type_resolution_map: HashMap::with_capacity(32),
            reverse_type_resolution_map: HashMap::with_capacity(32),
            primitive_types,
        };

        for &operator in &[
            Operator::Plus,
            Operator::Minus,
            Operator::Times,
            Operator::Divide,
            Operator::Modulo,
        ] {
            let mut overloads = Vec::with_capacity(8);
            let operator_name = operator.symbol();
            let name: Box<[_]> = Box::new([None, Some(operator_name), None]);
            for &primitive in &[
                PrimitiveType::Integer8,
                PrimitiveType::Integer16,
                PrimitiveType::Integer32,
                PrimitiveType::Integer64,
                PrimitiveType::Natural8,
                PrimitiveType::Natural16,
                PrimitiveType::Natural32,
                PrimitiveType::Natural64,
            ] {
                let typ = this.type_primitive(primitive);
                let arguments = vec![typ, typ];
                let function = Function {
                    name: name.iter().map(|x| x.map(|y| y.into())).collect(),
                    arguments: arguments.into(),
                    return_type: typ,
                    is_extern: false,
                    is_builtin: true,
                    id: FunctionId::null(),
                };
                overloads.push(this.new_function_id(function));
            }
            this.name_resolution_map.insert(name, overloads);
        }

        for &operator in &[
            Operator::Equals,
            Operator::LessThan,
            Operator::GreaterThan,
            Operator::LessThanEquals,
            Operator::GreaterThanEquals,
        ] {
            let mut overloads = Vec::with_capacity(8);
            let operator_name = operator.symbol();
            let name: Box<[_]> = Box::new([None, Some(operator_name), None]);
            for &primitive in &[
                PrimitiveType::Integer8,
                PrimitiveType::Integer16,
                PrimitiveType::Integer32,
                PrimitiveType::Integer64,
                PrimitiveType::Natural8,
                PrimitiveType::Natural16,
                PrimitiveType::Natural32,
                PrimitiveType::Natural64,
                PrimitiveType::Bool,
                PrimitiveType::Null,
            ] {
                let typ = this.type_primitive(primitive);
                let arguments = vec![typ, typ];
                let function = Function {
                    name: name.iter().map(|x| x.map(|y| y.into())).collect(),
                    arguments: arguments.into(),
                    return_type: this.type_bool(),
                    is_extern: false,
                    is_builtin: true,
                    id: FunctionId::null(),
                };
                overloads.push(this.new_function_id(function));
            }
            this.name_resolution_map.insert(name, overloads);
        }

        for &operator in &[
            Operator::Not
        ] {
            let mut overloads = Vec::with_capacity(1);
            let operator_name = operator.symbol();
            let name: Box<[_]> = Box::new([Some(operator_name), None]);
            let primitive = PrimitiveType::Bool;
            let typ = this.type_primitive(primitive);
            let arguments = vec![typ];
            let function = Function {
                name: name.iter().map(|x| x.map(|y| y.into())).collect(),
                arguments: arguments.into(),
                return_type: this.type_bool(),
                is_extern: false,
                is_builtin: true,
                id: FunctionId::null(),
            };
            overloads.push(this.new_function_id(function));
            this.name_resolution_map.insert(name, overloads);
        }

        this
    }

    fn new_global(&mut self, typ: TypeId, value: Value) -> GlobalId {
        let id = self.globals.len();
        self.globals.push((typ, value));
        id
    }

    pub fn new_function_id(&self, function: Function) -> FunctionId {
        let mut ptr = self.function_arena.alloc(function);
        let id = FunctionId(ptr);
        ptr.id = id;
        id
    }

    pub fn new_type_id(&self, typ: Type) -> TypeId {
        TypeId(self.type_arena.alloc(typ))
    }

    pub fn get_type_info(&self, type_id: TypeId) -> &Type {
        // This is safe so long as all TypeIds come from functions like `Compiler::new_type_id`
        // that generate pointers to `self.type_arena`, since all memory allocated in that arena
        // stays around while the `Compiler` still exists.
        unsafe {
            &*type_id.0
        }
    }

    pub fn get_function_info(&self, function_id: FunctionId) -> &Function {
        // See above.
        unsafe {
            &*function_id.0
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

    pub fn type_array(&self, size: u64, other: TypeId) -> TypeId {
        self.new_type_id(Type::Array(size, other))
    }

    pub fn type_function(&self, argument_types: Box<[TypeId]>, return_type: TypeId) -> TypeId {
        self.new_type_id(Type::Function { argument_types, return_type })
    }

    pub fn type_deref(&self, typ: TypeId) -> TypeId {
        match *self.get_type_info(typ) {
            Type::Pointer(_, subtype) => subtype,
            Type::Error => self.type_error(),
            _ => unreachable!(),
        }
    }

    pub fn int_type_width(&self, typ: TypeId) -> i32 {
        match *self.get_type_info(typ) {
            Type::Integer8 | Type::Natural8 => 8,
            Type::Integer16 | Type::Natural16 => 16,
            Type::Integer32 | Type::Natural32 => 32,
            Type::Integer64 | Type::Natural64 => 64,
            _ => unreachable!(),
        }
    }

    pub fn type_is_signed(&self, typ: TypeId) -> bool {
        match *self.get_type_info(typ) {
            Type::Integer8 | Type::Integer16 | Type::Integer32 | Type::Integer64 => true,
            _ => false,
        }
    }

    pub fn can_autocast(&self, from: TypeId, to: TypeId) -> Option<CastType> {
        if self.types_match(from, to) {
            return Some(CastType::None)
        }

        let type1 = self.get_type_info(from);
        let type2 = self.get_type_info(to);

        match (type1, type2) {
            // errors
            (&Type::Error, _)
            | (_, &Type::Error) => Some(CastType::Error),
            // Used for function overload resolution
            (&Type::GenericInteger, _) if type2.is_integral() => Some(CastType::Error),
            // Used for `proc` expression resolution
            (&Type::Generic, _) => Some(CastType::Error),
            // mut -> ref, muts -> refs
            (&Type::Pointer(pointer_type1, typ1), &Type::Pointer(pointer_type2, typ2))
                if self.can_autocast_pointer_type(pointer_type1, pointer_type2) && self.types_match(typ1, typ2)
              => Some(CastType::PointerType),
            (&Type::Pointer(pointer_type1, typ1), &Type::Pointer(pointer_type2, typ2))
              => match *self.get_type_info(typ1) {
                Type::Array(_, element_type) if self.types_match(element_type, typ2) => {
                    match (pointer_type1, pointer_type2) {
                        (PointerType::Reference, PointerType::Array)
                        | (PointerType::Mutable, PointerType::ArrayMutable)
                        | (PointerType::Mutable, PointerType::Array) => Some(CastType::PointerToArray),
                        _ => None,
                    }
                },
                _ => None,
            },
            _ => None,
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

    pub fn can_cast(&self, from: TypeId, to: TypeId) -> Option<CastType> {
        if let Some(cast_type) = self.can_autocast(from, to) {
            Some(cast_type)
        } else {
            let type1 = self.get_type_info(from);
            let type2 = self.get_type_info(to);
            match (type1, type2) {
                (_, _) if type1.is_integral() && type2.is_integral() => Some(CastType::Integer),
                (&Type::Pointer(pointer_type1, _), &Type::Pointer(pointer_type2, _)) if pointer_type1 == pointer_type2 => Some(CastType::Pointer),
                (&Type::Pointer(..), _) | (&Type::Function { .. }, _) if type2.is_integral() => Some(CastType::PointerToInteger),
                (_, &Type::Pointer(..)) | (_, &Type::Function { .. }) if type1.is_integral() => Some(CastType::IntegerToPointer),
                _ => None,
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
            (&Type::GenericInteger, &Type::GenericInteger) => true,
            (&Type::Generic, &Type::Generic) => true,
            (&Type::Bool, &Type::Bool) => true,
            (&Type::Null, &Type::Null) => true,
            (&Type::Pointer(type1, subtype1), &Type::Pointer(type2, subtype2)) => type1 == type2 && self.types_match(subtype1, subtype2),
            (&Type::Record(ref fields1), &Type::Record(ref fields2)) => {
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
            (&Type::Function { argument_types: ref argument_types1, return_type: return_type1 }, &Type::Function { argument_types: ref argument_types2, return_type: return_type2 }) => {
                if argument_types1.len() != argument_types2.len() {
                    return false
                }
                if !self.types_match(return_type1, return_type2) {
                    return false
                }
                for (&type1, &type2) in argument_types1.iter().zip(argument_types2.iter()) {
                    if !self.types_match(type1, type2) {
                        return false
                    }
                }
                true
            },
            (&Type::Error, &Type::Error) => true,
            _ => false,
        }
    }

    fn types_match_allow_generic(&self, type_id1: TypeId, type_id2: TypeId) -> bool {
        let type1 = self.get_type_info(type_id1);
        let type2 = self.get_type_info(type_id2);
        match (type1, type2) {
            (&Type::GenericInteger, typ)
            | (typ, &Type::GenericInteger) if typ.is_integral() => true,
            (&Type::Generic, _)
            | (_, &Type::Generic) => true,
            _ => self.types_match(type_id1, type_id2),
        }
    }

    fn types_match_default_generic(&self, type_id1: TypeId, type_id2: TypeId) -> bool {
        let type1 = self.get_type_info(type_id1);
        let type2 = self.get_type_info(type_id2);
        match (type1, type2) {
            (&Type::GenericInteger, &Type::Integer32)
            | (&Type::Integer32, &Type::GenericInteger) => true,
            (&Type::Generic, _)
            | (_, &Type::Generic) => false,
            _ => self.types_match(type_id1, type_id2),
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
        eprint!("\x1b[31;1mError:\x1b[0m ");
        match *error {
            ParseError(UnexpectedCharacter(span, c)) => {
                eprintln!("unexpected character: {}", c);
                print_span(&self, span);
            },
            ParseError(UnexpectedEndOfFile(span)) => {
                eprintln!("unexpected end of file");
                print_span(&self, span);
            },
            ParseError(InvalidEscapeSequence(span)) => {
                eprintln!("invalid escape sequence");
                print_span(&self, span);
            },
            ParseError(UnexpectedToken(span, ref token)) => {
                eprintln!("unexpected token: {}", token);
                print_span(&self, span);
            },
            ParseError(ExpectedFoundToken { span, ref expected, ref found }) => {
                eprintln!("unexpected token: expected {}, found {}", expected, found);
                print_span(&self, span);
            },
            ParseError(ExpectedLowercaseIdentifier(span, ref token)) => {
                eprintln!("unexpected token: expected name, found {}", token);
                print_span(&self, span);
            },
            ParseError(InvalidNumericSize(span, size)) => {
                eprintln!("invalid numeric size: {}", size);
                print_span(&self, span);
            },
            UndefinedVariable(span) => {
                eprintln!("undefined variable: {}", span);
                print_span(&self, span);
            },
            ShadowedName(span, ref name) => {
                eprintln!("shadowed variable: {}", name);
                print_span(&self, span);
            },
            UndefinedFunction(span, ref identifier) => {
                eprintln!("undefined function: {}", FunctionIdentifierPrinter(self, identifier));
                print_span(&self, span);
            },
            NoOverloadForFunction(span, ref identifier) => {
                eprintln!("no matching overload for function: {}", FunctionIdentifierPrinter(self, identifier));
                print_span(&self, span);
            },
            AmbiguousOverload(span, ref identifier) => {
                eprintln!("call to overloaded function is ambiguous: {}", FunctionIdentifierPrinter(self, identifier));
                print_span(&self, span);
            },
            UnexpectedType { span, expected, found } => {
                eprintln!("invalid type: expected {}, found {}", TypePrinter(self, expected), TypePrinter(self, found));
                print_span(&self, span);
            },
            InvalidType { span, typ } => {
                eprintln!("invalid type: {}", TypePrinter(self, typ));
                print_span(&self, span);
            },
            InvalidOperandType { span, typ } => {
                eprintln!("invalid operand type: {}", TypePrinter(self, typ));
                print_span(&self, span);
            },
            InvalidOperandTypes { span, operator, left, right } => {
                eprintln!("invalid operand types: {} {} {}", TypePrinter(self, left), operator.symbol(), TypePrinter(self, right));
                print_span(&self, span);
            },
            FunctionMightNotReturn(span) => {
                eprintln!("function might not return");
                print_span(&self, span);
            },
            BreakOutsideLoop(span) => {
                eprintln!("break outside loop");
                print_span(&self, span);
            },
            ContinueOutsideLoop(span) => {
                eprintln!("continue outside loop");
                print_span(&self, span);
            },
            InvalidLvalue(span) => {
                eprintln!("invalid lvalue");
                print_span(&self, span);
            },
            ImmutableLvalue(span) => {
                eprintln!("lvalue is immutable");
                print_span(&self, span);
            },
            ArrayPointerToNonArray(span) => {
                eprintln!("attempt to take array reference to non-array lvalue");
                print_span(&self, span);
            },
            InvalidCast { span, from, to } => {
                eprintln!("invalid cast: {} to {}", TypePrinter(self, from), TypePrinter(self, to));
                print_span(&self, span);
            },
            InvalidExternFunctionName(span, function) => {
                eprintln!("invalid extern function signature: {}", FunctionPrinter(self, function));
                print_span(&self, span);
            },
            UndefinedType(span) => {
                eprintln!("undefined type: {}", span);
                print_span(&self, span);
            },
            FieldAccessOnNonRecord(span, typ) => {
                eprintln!("attempt to set or access field of non-record: {}", TypePrinter(self, typ));
                print_span(&self, span);
            },
            FieldDoesNotExist(span, typ, field_name) => {
                eprintln!("type {} has no field named '{}'", TypePrinter(self, typ), field_name);
                print_span(&self, span);
            },
            CallOfNonFunction(span, typ) => {
                eprintln!("cannot call value of type {}", TypePrinter(self, typ));
                print_span(&self, span);
            },
            ReferenceToBuiltinFunction(span) => {
                eprintln!("reference to built-in function");
                print_span(&self, span);
            },
            InvalidConstantExpression(span) => {
                eprintln!("invalid constant expression");
                print_span(&self, span);
            },
        }
    }

    pub fn resolve_type(&self, typ: &parse::Type) -> TypeId {
        let span = self.type_span(typ);
        match *typ {
            parse::Type::Name("int8")  => self.type_primitive(PrimitiveType::Integer8),
            parse::Type::Name("int16") => self.type_primitive(PrimitiveType::Integer16),
            parse::Type::Name("int32") => self.type_primitive(PrimitiveType::Integer32),
            parse::Type::Name("int64") => self.type_primitive(PrimitiveType::Integer64),
            parse::Type::Name("nat8")  => self.type_primitive(PrimitiveType::Natural8),
            parse::Type::Name("nat16") => self.type_primitive(PrimitiveType::Natural16),
            parse::Type::Name("nat32") => self.type_primitive(PrimitiveType::Natural32),
            parse::Type::Name("nat64") => self.type_primitive(PrimitiveType::Natural64),
            parse::Type::Name("bool")  => self.type_primitive(PrimitiveType::Bool),
            parse::Type::Name(name) => {
                if let Some(&typ) = self.type_resolution_map.get(name) {
                    typ
                } else {
                    self.report_error(Error::UndefinedType(span));
                    self.type_error()
                }
            },
            parse::Type::Null => self.type_null(),
            parse::Type::Reference(ref subtype) => self.type_ref(self.resolve_type(subtype)),
            parse::Type::MutableReference(ref subtype) => self.type_mut(self.resolve_type(subtype)),
            parse::Type::ArrayReference(ref subtype) => self.type_refs(self.resolve_type(subtype)),
            parse::Type::MutableArrayReference(ref subtype) => self.type_muts(self.resolve_type(subtype)),
            parse::Type::Proc(ref argument_types, ref return_type) => {
                let type_info = Type::Function {
                    argument_types: argument_types.iter().map(|x| self.resolve_type(x)).collect(),
                    return_type: self.resolve_type(return_type),
                };
                self.new_type_id(type_info)
            },
            parse::Type::Record(ref fields) => {
                let mut resolved_fields = vec![];
                for &(field_name, ref type_expression) in fields.iter() {
                    resolved_fields.push((field_name.into(), self.resolve_type(type_expression)));
                }
                let typ = Type::Record(resolved_fields.into());
                self.new_type_id(typ)
            },
            parse::Type::Array(size, ref subtype) => self.type_array(size, self.resolve_type(subtype)),
        }
    }

    pub fn preload_definition(&mut self, definition: &'source Definition<'source>) -> FrontendDirective<'source> {
        match *definition {
            Definition::Type(name, ..) => {
                // Make a new placeholder TypeId to be filled in with real type information later
                let type_id = TypeId(self.type_arena.alloc(Type::Error));
                self.type_resolution_map.insert(name, type_id);
                self.reverse_type_resolution_map.insert(type_id.0, name);
                FrontendDirective::None
            },
            Definition::Variable(..) | Definition::Function(..) | Definition::Extern(..) => FrontendDirective::None,
            Definition::Import(ref path) => FrontendDirective::Import(&**path),
            Definition::Library(ref path) => FrontendDirective::Library(&**path),
        }
    }

    pub fn finalize_definition(&mut self, definition: &'source Definition<'source>) {
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

                let function = Function { name, arguments, return_type, is_extern, is_builtin: false, id: FunctionId::null() };

                if is_extern
                && (signature.name.len() == 0
                    || !signature.name[1..].iter().all(|x| x.is_none())
                    || signature.name[0].is_none()
                    || signature.name[0].as_ref().unwrap().chars().next() != Some('\''))
                {
                    let span = self.definition_span(definition);
                    self.report_error(Error::InvalidExternFunctionName(span, function.id));
                }

                let function_id = self.new_function_id(function);

                self.name_resolution_map.entry(signature.name.clone())
                    .and_modify(|v| v.push(function_id))
                    .or_insert_with(|| vec![function_id]);
                self.signature_resolution_map.insert(signature, function_id);
            },
            Definition::Variable(ref name, ref type_expression, ref value_expression_option) => {
                let typ = self.resolve_type(type_expression);
                let mut value = Value::None;

                if let Some(value_expression) = value_expression_option.as_ref() {
                    let expression_span = self.expression_span(value_expression);
                    value = match **value_expression {
                        Expression::Integer(i, _) => Value::Integer(i as i64),
                        Expression::Negate(ref subexpression) => match **subexpression {
                            Expression::Integer(i, _) => Value::Integer(-(i as i64)),
                            _ => {
                                self.report_error(Error::InvalidConstantExpression(expression_span));
                                Value::Error
                            },
                        },
                        _ => {
                            self.report_error(Error::InvalidConstantExpression(expression_span));
                            Value::Error
                        },
                    };

                    if !value.type_is_valid(self.get_type_info(typ)) {
                        self.report_error(Error::InvalidType { span: expression_span, typ });
                        value = Value::Error;
                    }
                }

                let global_id = self.new_global(typ, value);

                self.variable_resolution_map.insert(name.clone(), global_id);
            },
            Definition::Type(name, ref type_expression) => {
                let type_id = self.resolve_type(type_expression);
                let typ = self.get_type_info(type_id).clone();
                let TypeId(pointer) = self.type_resolution_map[name];
                unsafe {
                    *pointer = typ;
                }
            },
            Definition::Import(..) | Definition::Library(..) => {},
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
    pub fn lookup_function(&self, span: &'source str, name: &FunctionName<'source>, argument_types: &[TypeId]) -> Option<FunctionId> {
        // FIXME(cleanup): this code isn't ideal and could probably be simplified & optimized
        let function_identifier = FunctionIdentifier {
            name: name.iter().map(|x| x.map(|y| y.into())).collect(),
            arguments: argument_types.into(),
        };

        if let Some(function_ids) = self.name_resolution_map.get::<Box<_>>(&name.into()) {
            let candidates: Box<[_]> = function_ids.iter()
                .map(|&id| self.get_function_info(id))
                // Can we autocast our parameters to match this function's types?
                .filter(|function| argument_types.iter().zip(function.arguments.iter()).all(|(&x, &y)| self.can_autocast(x, y).is_some())).collect();

            if candidates.len() == 0 {
                self.report_error(Error::NoOverloadForFunction(span, function_identifier));
                return None
            }

            let candidate1 = &candidates[0];
            let ignorable = candidates.iter().fold(
                vec![true; argument_types.len()],
                |mut x, candidate| {
                    for i in 0..x.len() {
                        x[i] &= self.types_match_allow_generic(candidate.arguments[i], candidate1.arguments[i]);
                    }
                    x
                }
            );

            // We need to be careful here, as if one of our argument types is a GenericInteger,
            // there may be more than one match (as GenericInteger `types_match_allow_generic`s
            // with every integer type).  If possible, we want to select the match where the
            // non-ignorable GenericInteger arguments are all Integer32; otherwise, we reject the
            // call as ambiguous.
            //
            // That's what `types_match_default_generic` is for: it treats `GenericInteger` as
            // matching *only* `Integer32` (instead of any integer type).
            for function in candidates.iter()
                .filter(|function| function.arguments.iter()
                        .zip(argument_types.iter())
                        .enumerate()
                        .filter(|&(i, _)| !ignorable[i])
                        .all(|(_, (&x, &y))| self.types_match_default_generic(x, y)))
            {
                // We have a match!
                return Some(function.id)
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

    pub fn type_span(&self, typ: &parse::Type<'source>) -> &'source str {
        self.type_spans[&(typ as *const _)]
    }

    pub fn definition_span(&self, definition: &Definition<'source>) -> &'source str {
        self.definition_spans[&(definition as *const _)]
    }
}
