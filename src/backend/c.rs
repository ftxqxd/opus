//! The C backend for the Opus compiler.
//!
//! This part of the compiler governs the translation between the Opus IR format (defined in
//! `generate_ir.rs`) and C code.

use std::io::{self, Write};
use crate::generate_ir::{IrGenerator, Instruction};
use crate::compile::{Function, Type, TypeId, PointerType, Compiler};
use super::Backend;

pub struct CBackend<'source, W: Write> {
    compiler: &'source Compiler<'source>,
    writer: W,
}

impl<'source, W: Write> Backend for CBackend<'source, W> {
    /// Initialize C code generation by writing necessary `#include` statements, function prototypes,
    /// and the main function.
    fn initialize(&mut self) -> io::Result<()> {
        // Headers
        writeln!(self.writer, "#include <stdint.h>")?;

        // Builtin types
        writeln!(self.writer, "typedef uint8_t _opust_null;")?;
        writeln!(self.writer, "typedef uint8_t _opust_bool;")?;

        // User-defined types
        for (_, &type_id) in &self.compiler.type_resolution_map {
            let typ = self.compiler.get_type_info(type_id);
            if let Type::Record { ref name, ref fields } = *typ {
                write!(self.writer, "struct {} {{", name)?;
                for &(ref field_name, field_type) in fields.iter() {
                    write!(self.writer, "{}", self.translate_type_to_c(field_type, Some(field_name)))?;
                    write!(self.writer, ";")?;
                }
                writeln!(self.writer, "}};")?;
            }
        }

        // Prototypes
        for (_, function) in self.compiler.signature_resolution_map.iter() {
            self.translate_function_signature_to_c(function)?;
            writeln!(self.writer, ";")?;
        }

        // Main
        writeln!(self.writer, "int main(void) {{ return _opus_Main(); }}")?;

        Ok(())
    }

    /// Generate C code for a single function from Opus IR and write the generated code to the self.writer
    /// writer `self.writer`.
    fn translate_ir(&mut self, ir: &IrGenerator) -> io::Result<()> {
        ////// Generate function signature //////
        self.translate_function_signature_to_c(ir.function)?;
        write!(self.writer, " {{\n")?;

        ////// Generate function body //////
        // Write variables
        for (i, variable) in ir.variables.iter().enumerate() {
            if i < ir.function.arguments.len() {
                continue
            }

            write!(self.writer, "\t")?;
            write!(self.writer, "{}", self.translate_type_to_c(variable.typ, Some(&format!("var{}", i))))?;
            write!(self.writer, ";\n")?;
        }
        writeln!(self.writer, "\tint last_instruction;")?;

        // Write instructions
        for instruction_index in 0..ir.instructions.len() {
            write!(self.writer, "\t")?;
            self.translate_instruction_to_c(ir, instruction_index)?;
        }

        write!(self.writer, "}}\n")?;

        Ok(())
    }
}

impl<'source, W: Write> CBackend<'source, W> {
    pub fn new(compiler: &'source Compiler<'source>, writer: W) -> Self {
        CBackend {
            compiler,
            writer,
        }
    }

    fn translate_function_signature_to_c(&mut self, function: &Function) -> io::Result<()> {
        // Write return type
        write!(self.writer, "{}", self.translate_type_to_c(function.return_type, None))?;
        write!(self.writer, " ")?;
        self.mangle_function_name(function)?;
        write!(self.writer, "(")?;
        // Write argument types
        let mut written_anything = false;
        if function.arguments.len() == 0 {
            write!(self.writer, "void")?;
        }
        for (i, &argument_type) in function.arguments.iter().enumerate() {
            if written_anything {
                write!(self.writer, ", ")?;
            }
            written_anything = true;

            write!(self.writer, "{}", self.translate_type_to_c(argument_type, Some(&format!("var{}", i))))?;
        }
        write!(self.writer, ")")
    }

    fn translate_type_to_c(&self, typ: TypeId, name: Option<&str>) -> String {
        let type_info = self.compiler.get_type_info(typ);
        let mut output = match *type_info {
            Type::Integer8 => "int8_t".into(),
            Type::Integer16 => "int16_t".into(),
            Type::Integer32 => "int32_t".into(),
            Type::Integer64 => "int64_t".into(),
            Type::Natural8 => "uint8_t".into(),
            Type::Natural16 => "uint16_t".into(),
            Type::Natural32 => "uint32_t".into(),
            Type::Natural64 => "uint64_t".into(),
            Type::GenericInteger | Type::Generic => unreachable!(),
            Type::Null => "_opust_null".into(),
            Type::Bool => "_opust_bool".into(),
            Type::Pointer(PointerType::Reference, subtype) | Type::Pointer(PointerType::Array, subtype) => {
                let name = format!("const *{}", name.unwrap_or(""));
                return self.translate_type_to_c(subtype, Some(&name))
            },
            Type::Pointer(PointerType::Mutable, subtype) | Type::Pointer(PointerType::ArrayMutable, subtype) => {
                let name = format!("*{}", name.unwrap_or(""));
                return self.translate_type_to_c(subtype, Some(&name))
            },
            Type::Record { ref name, .. } => {
                format!("struct {}", name)
            },
            Type::Function { ref argument_types, return_type } => {
                let mut name = format!("(*{})(", name.unwrap_or(""));
                let mut first = true;

                if argument_types.len() == 0{
                    name += "void";
                }
                for &argument_type in argument_types.iter() {
                    if !first {
                        name += ", ";
                    }
                    first = false;
                    name += &*self.translate_type_to_c(argument_type, None);
                }
                name += ")";

                return self.translate_type_to_c(return_type, Some(&name))
            },
            Type::Error => "internal_compiler_error".into(),
        };

        if let Some(name) = name {
            output += &*format!(" {}", name);
        }

        output
    }

    fn translate_instruction_to_c(&mut self, ir: &IrGenerator, instruction_index: usize) -> io::Result<()> {
        let instruction = &ir.instructions[instruction_index];
        write!(self.writer, "i{}: ", instruction_index)?;
        if let Instruction::Phi(destination, index1, variable1, _, variable2) = *instruction {
            writeln!(self.writer, "var{} = last_instruction == {} ? var{} : var{};", destination, index1, variable1, variable2)?;
            writeln!(self.writer, "\tlast_instruction = {};", instruction_index)?;
        } else {
            write!(self.writer, "last_instruction = {};\n\t", instruction_index)?;
        }

        match *instruction {
            Instruction::Integer(destination, constant) => writeln!(self.writer, "var{} = {};", destination, constant)?,
            Instruction::Null(destination) => writeln!(self.writer, "var{} = 0;", destination)?,
            Instruction::Bool(destination, is_true) => writeln!(self.writer, "var{} = {};", destination, if is_true { 1 } else { 0 })?,
            Instruction::String(destination, ref bytes) => {
                write!(self.writer, "var{} = \"", destination)?;
                for &byte in bytes.iter() {
                    match byte {
                        b'\\' => write!(self.writer, "\\\\")?,
                        b'"' => write!(self.writer, "\\\"")?,
                        b'\n' => write!(self.writer, "\\n")?,
                        b' ' ..= b'~' => write!(self.writer, "{}", byte as char)?,
                        _ => write!(self.writer, "\\x{:02x}", byte)?,
                    }
                }
                writeln!(self.writer, "\";")?
            },

            Instruction::Call(destination, function, ref arguments) => {
                write!(self.writer, "var{} = var{}", destination, function)?;
                write!(self.writer, "(")?;
                for (i, argument) in arguments.iter().enumerate() {
                    if i > 0 {
                        write!(self.writer, ", ")?;
                    }
                    write!(self.writer, "var{}", argument)?;
                }
                writeln!(self.writer, ");")?;
            },

            Instruction::Allocate(destination) => {
                write!(self.writer, ";\n\t")?;
                let typ = ir.get_lvalue_type(destination);
                write!(self.writer, "{}", self.translate_type_to_c(typ, Some(&format!("storage{}", destination))))?;
                write!(self.writer, ";\n\t")?;
                writeln!(self.writer, "var{} = &storage{};", destination, destination)?;
            },
            Instruction::Load(destination, source) => writeln!(self.writer, "var{} = *var{};", destination, source)?,
            Instruction::Store(destination, source) => writeln!(self.writer, "*var{} = var{};", destination, source)?,
            Instruction::Field(destination, source, field_name) => writeln!(self.writer, "var{} = &var{}->{};", destination, source, field_name)?,
            Instruction::Index(destination, source, index) => writeln!(self.writer, "var{} = &var{}[var{}];", destination, source, index)?,

            Instruction::Add(destination, left, right) => writeln!(self.writer, "var{} = var{} + var{};", destination, left, right)?,
            Instruction::Subtract(destination, left, right) => writeln!(self.writer, "var{} = var{} - var{};", destination, left, right)?,
            Instruction::Multiply(destination, left, right) => writeln!(self.writer, "var{} = var{} * var{};", destination, left, right)?,
            Instruction::Divide(destination, left, right) => writeln!(self.writer, "var{} = var{} / var{};", destination, left, right)?,
            Instruction::Modulo(destination, left, right) => writeln!(self.writer, "var{} = var{} % var{};", destination, left, right)?,
            Instruction::Equals(destination, left, right) => writeln!(self.writer, "var{} = var{} == var{};", destination, left, right)?,
            Instruction::LessThan(destination, left, right) => writeln!(self.writer, "var{} = var{} < var{};", destination, left, right)?,
            Instruction::GreaterThan(destination, left, right) => writeln!(self.writer, "var{} = var{} > var{};", destination, left, right)?,
            Instruction::LessThanEquals(destination, left, right) => writeln!(self.writer, "var{} = var{} <= var{};", destination, left, right)?,
            Instruction::GreaterThanEquals(destination, left, right) => writeln!(self.writer, "var{} = var{} >= var{};", destination, left, right)?,

            Instruction::Function(destination, function) => {
                write!(self.writer, "var{} = ", destination)?;
                self.mangle_function_name(function)?;
                writeln!(self.writer, ";")?
            },

            Instruction::Not(destination, value) => writeln!(self.writer, "var{} = !var{};", destination, value)?,
            Instruction::Negate(destination, value) => writeln!(self.writer, "var{} = -var{};", destination, value)?,

            Instruction::Cast(destination, source) => {
                let type1 = ir.variables[destination].typ;
                let type_string = self.translate_type_to_c(type1, None);
                writeln!(self.writer, "var{} = ({}) var{};", destination, type_string, source)?;
            },

            Instruction::Return(variable) => writeln!(self.writer, "return var{};", variable)?,
            Instruction::Jump(index) => {
                writeln!(self.writer, "goto i{};", index)?;
            },
            Instruction::Branch(condition_variable, if_index, then_index) => {
                writeln!(self.writer, "if (var{}) goto i{}; else goto i{};", condition_variable, if_index, then_index)?;
            },
            Instruction::Phi(..) => {}, // special case above

            Instruction::Nop => writeln!(self.writer, ";")?,
            Instruction::BreakPlaceholder => panic!("break placeholder left unfilled"),
            Instruction::Error(variable) => panic!("error in var{} went unreported", variable),
        }
        Ok(())
    }

    /// Mangle an Opus function signature (including type information) into a name that C can
    /// understand.
    ///
    /// The mangling procedure converts signatures like
    ///
    ///     (Frobnicate :int64 With :nat64)
    ///
    /// to names like
    ///
    ///     _opus_Frobnicate__int_With__nat64.
    fn mangle_function_name(&mut self, function: &Function) -> io::Result<()> {
        if function.is_extern {
            write!(self.writer, "{}", &function.name[0].as_ref().unwrap()[1..])?;
        } else {
            write!(self.writer, "_opus")?;

            let mut i = 0;
            for part in function.name.iter() {
                match *part {
                    Some(ref x) => {
                        write!(self.writer, "_")?;
                        self.mangle_symbol(x)?;
                    },
                    None => {
                        write!(self.writer, "__")?;
                        self.mangle_type_name(function.arguments[i])?;
                        i += 1;
                    },
                }
            }
        }

        Ok(())
    }

    fn mangle_symbol(&mut self, x: &str) -> io::Result<()> {
        write!(self.writer, "{}", match x {
            "+" => "Plus",
            "-" => "Minus",
            "*" => "Times",
            "/" => "Divide",
            "%" => "Modulo",
            "=" => "Equals",
            "<" => "LessThan",
            ">" => "GreaterThan",
            "<=" => "LessThanEquals",
            ">=" => "GreaterThanEquals",
            _ => x,
        })
    }

    fn mangle_type_name(&mut self, typ: TypeId) -> io::Result<()> {
        // FIXME: mangling is just terrible.
        let type_info = self.compiler.get_type_info(typ);
        match *type_info {
            Type::Integer8 => write!(self.writer, "int8"),
            Type::Integer16 => write!(self.writer, "int16"),
            Type::Integer32 => write!(self.writer, "int32"),
            Type::Integer64 => write!(self.writer, "int64"),
            Type::Natural8 => write!(self.writer, "nat8"),
            Type::Natural16 => write!(self.writer, "nat16"),
            Type::Natural32 => write!(self.writer, "nat32"),
            Type::Natural64 => write!(self.writer, "nat64"),
            Type::GenericInteger | Type::Generic => unreachable!(),
            Type::Null => write!(self.writer, "null"),
            Type::Bool => write!(self.writer, "bool"),
            Type::Pointer(pointer_type, subtype) => {
                let prefix = match pointer_type {
                    PointerType::Reference => "Reference",
                    PointerType::Mutable => "Mutable",
                    PointerType::Array => "ArrayReference",
                    PointerType::ArrayMutable => "MutableArrayReference",
                };
                write!(self.writer, "{}To", prefix)?;
                self.mangle_type_name(subtype)
            },
            Type::Record { ref name, .. } => {
                write!(self.writer, "Record{}", name)
            },
            Type::Function { ref argument_types, return_type } => {
                write!(self.writer, "Function")?;
                for &typ in argument_types.iter() {
                    write!(self.writer, "Arg")?;
                    self.mangle_type_name(typ)?;
                }
                write!(self.writer, "Returns")?;
                self.mangle_type_name(return_type)?;
                Ok(())
            },
            Type::Error => write!(self.writer, "error"),
        }
    }
}
