//! The C backend for the Opus compiler.
//!
//! This part of the compiler governs the translation between the Opus IR format (defined in
//! `generate_ir.rs`) and C code.

use std::io::{self, Write};
use crate::generate_ir::{IrGenerator, Instruction};
use crate::compile::{Function, Type, TypeId, PointerType, Compiler};

/// Initialize C code generation by writing necessary `#include` statements, function prototypes,
/// and the main function.
pub fn initialize<W: Write>(compiler: &Compiler, output: &mut W) -> io::Result<()> {
    // Headers
    writeln!(output, "#include <stdint.h>")?;

    // Builtin types
    writeln!(output, "typedef uint8_t _opust_null;")?;
    writeln!(output, "typedef uint8_t _opust_bool;")?;

    // User-defined types
    for (_, &type_id) in &compiler.type_resolution_map {
        let typ = compiler.get_type_info(type_id);
        if let Type::Record { ref name, ref fields } = *typ {
            write!(output, "struct {} {{", name)?;
            for &(ref field_name, field_type) in fields.iter() {
                translate_type_to_c(compiler, output, field_type, Some(field_name))?;
                write!(output, ";")?;
            }
            writeln!(output, "}};")?;
        }
    }

    // Prototypes
    for (_, function) in compiler.signature_resolution_map.iter() {
        translate_function_signature_to_c(compiler, function, output)?;
        writeln!(output, ";")?;
    }

    // Main
    writeln!(output, "int main(void) {{ return _opus_Main(); }}")?;

    Ok(())
}

/// Generate C code for a single function from Opus IR and write the generated code to the output
/// writer `output`.
pub fn translate_ir_to_c<W: Write>(ir: &IrGenerator, output: &mut W) -> io::Result<()> {
    ////// Generate function signature //////
    translate_function_signature_to_c(&ir.compiler, ir.function, output)?;
    write!(output, " {{\n")?;

    ////// Generate function body //////
    // Write variables
    for (i, variable) in ir.variables.iter().enumerate() {
        if i < ir.function.arguments.len() {
            continue
        }

        write!(output, "\t")?;
        translate_type_to_c(&ir.compiler, output, variable.typ, Some(&format!("var{}", i)))?;
        write!(output, ";\n")?;
    }
    writeln!(output, "\tint last_instruction;")?;

    // Write instructions
    for instruction_index in 0..ir.instructions.len() {
        write!(output, "\t")?;
        translate_instruction_to_c(ir, output, instruction_index)?;
    }

    write!(output, "}}\n")?;

    Ok(())
}

fn translate_function_signature_to_c<W: Write>(compiler: &Compiler, function: &Function, output: &mut W) -> io::Result<()> {
    // Write return type
    translate_type_to_c(compiler, output, function.return_type, None)?;
    write!(output, " ")?;
    mangle_function_name(compiler, function, output)?;
    write!(output, "(")?;
    // Write argument types
    let mut written_anything = false;
    if function.arguments.len() == 0 {
        write!(output, "void")?;
    }
    for (i, &argument_type) in function.arguments.iter().enumerate() {
        if written_anything {
            write!(output, ", ")?;
        }
        written_anything = true;

        translate_type_to_c(&compiler, output, argument_type, Some(&format!("var{}", i)))?;
    }
    write!(output, ")")
}

fn translate_type_to_c<W: Write>(compiler: &Compiler, output: &mut W, typ: TypeId, name: Option<&str>) -> io::Result<()> {
    let type_info = compiler.get_type_info(typ);
    match *type_info {
        Type::Integer8 => write!(output, "int8_t")?,
        Type::Integer16 => write!(output, "int16_t")?,
        Type::Integer32 => write!(output, "int32_t")?,
        Type::Integer64 => write!(output, "int64_t")?,
        Type::Natural8 => write!(output, "uint8_t")?,
        Type::Natural16 => write!(output, "uint16_t")?,
        Type::Natural32 => write!(output, "uint32_t")?,
        Type::Natural64 => write!(output, "uint64_t")?,
        Type::GenericInteger | Type::Generic => unreachable!(),
        Type::Null => write!(output, "_opust_null")?,
        Type::Bool => write!(output, "_opust_bool")?,
        Type::Pointer(PointerType::Reference, subtype) | Type::Pointer(PointerType::Array, subtype) => {
            let name = format!("const *{}", name.unwrap_or(""));
            translate_type_to_c(compiler, output, subtype, Some(&name))?;
            return Ok(())
        },
        Type::Pointer(PointerType::Mutable, subtype) | Type::Pointer(PointerType::ArrayMutable, subtype) => {
            let name = format!("*{}", name.unwrap_or(""));
            translate_type_to_c(compiler, output, subtype, Some(&name))?;
            return Ok(())
        },
        Type::Record { ref name, .. } => {
            write!(output, "struct {}", name)?;
        },
        Type::Function { ref argument_types, return_type } => {
            let name = format!("(*{})(", name.unwrap_or(""));
            let mut name: Vec<_> = name.into();
            let mut first = true;

            if argument_types.len() == 0{
                name.extend_from_slice(b"void");
            }
            for &argument_type in argument_types.iter() {
                if !first {
                    name.extend_from_slice(b", ");
                }
                first = false;
                translate_type_to_c(compiler, &mut name, argument_type, None)?;
            }
            name.extend_from_slice(b")");

            translate_type_to_c(compiler, output, return_type, Some(&String::from_utf8_lossy(&name)))?;
            return Ok(())
        },
        Type::Error => write!(output, "internal_compiler_error")?,
    }

    if let Some(name) = name {
        write!(output, " {}", name)?;
    }

    Ok(())
}

fn translate_instruction_to_c<W: Write>(ir: &IrGenerator, output: &mut W, instruction_index: usize) -> io::Result<()> {
    let instruction = &ir.instructions[instruction_index];
    write!(output, "i{}: ", instruction_index)?;
    if let Instruction::Phi(destination, index1, variable1, _, variable2) = *instruction {
        writeln!(output, "var{} = last_instruction == {} ? var{} : var{};", destination, index1, variable1, variable2)?;
        writeln!(output, "\tlast_instruction = {};", instruction_index)?;
    } else {
        write!(output, "last_instruction = {};\n\t", instruction_index)?;
    }

    match *instruction {
        Instruction::Integer(destination, constant) => writeln!(output, "var{} = {};", destination, constant)?,
        Instruction::Null(destination) => writeln!(output, "var{} = 0;", destination)?,
        Instruction::Bool(destination, is_true) => writeln!(output, "var{} = {};", destination, if is_true { 1 } else { 0 })?,
        Instruction::String(destination, ref bytes) => {
            write!(output, "var{} = \"", destination)?;
            for &byte in bytes.iter() {
                match byte {
                    b'\\' => write!(output, "\\\\")?,
                    b'"' => write!(output, "\\\"")?,
                    b'\n' => write!(output, "\\n")?,
                    b' ' ..= b'~' => write!(output, "{}", byte as char)?,
                    _ => write!(output, "\\x{:02x}", byte)?,
                }
            }
            writeln!(output, "\";")?
        },

        Instruction::Call(destination, function, ref arguments) => {
            write!(output, "var{} = ", destination)?;
            mangle_function_name(&ir.compiler, function, output)?;
            write!(output, "(")?;
            for (i, argument) in arguments.iter().enumerate() {
                if i > 0 {
                    write!(output, ", ")?;
                }
                write!(output, "var{}", argument)?;
            }
            writeln!(output, ");")?;
        },

        Instruction::Allocate(destination) => {
            write!(output, ";\n\t")?;
            let typ = ir.get_lvalue_type(destination);
            translate_type_to_c(&ir.compiler, output, typ, Some(&format!("storage{}", destination)))?;
            write!(output, ";\n\t")?;
            writeln!(output, "var{} = &storage{};", destination, destination)?;
        },
        Instruction::Load(destination, source) => writeln!(output, "var{} = *var{};", destination, source)?,
        Instruction::Store(destination, source) => writeln!(output, "*var{} = var{};", destination, source)?,
        Instruction::Field(destination, source, field_name) => writeln!(output, "var{} = &var{}->{};", destination, source, field_name)?,
        Instruction::Index(destination, source, index) => writeln!(output, "var{} = &var{}[var{}];", destination, source, index)?,

        Instruction::Add(destination, left, right) => writeln!(output, "var{} = var{} + var{};", destination, left, right)?,
        Instruction::Subtract(destination, left, right) => writeln!(output, "var{} = var{} - var{};", destination, left, right)?,
        Instruction::Multiply(destination, left, right) => writeln!(output, "var{} = var{} * var{};", destination, left, right)?,
        Instruction::Divide(destination, left, right) => writeln!(output, "var{} = var{} / var{};", destination, left, right)?,
        Instruction::Modulo(destination, left, right) => writeln!(output, "var{} = var{} % var{};", destination, left, right)?,
        Instruction::Equals(destination, left, right) => writeln!(output, "var{} = var{} == var{};", destination, left, right)?,
        Instruction::LessThan(destination, left, right) => writeln!(output, "var{} = var{} < var{};", destination, left, right)?,
        Instruction::GreaterThan(destination, left, right) => writeln!(output, "var{} = var{} > var{};", destination, left, right)?,
        Instruction::LessThanEquals(destination, left, right) => writeln!(output, "var{} = var{} <= var{};", destination, left, right)?,
        Instruction::GreaterThanEquals(destination, left, right) => writeln!(output, "var{} = var{} >= var{};", destination, left, right)?,

        Instruction::Function(destination, function) => {
            write!(output, "var{} = ", destination)?;
            mangle_function_name(ir.compiler, function, output)?;
            writeln!(output, ";")?
        },

        Instruction::Not(destination, value) => writeln!(output, "var{} = !var{};", destination, value)?,
        Instruction::Negate(destination, value) => writeln!(output, "var{} = -var{};", destination, value)?,

        Instruction::Cast(destination, source) => {
            let type1 = ir.variables[destination].typ;
            write!(output, "var{} = (", destination)?;
            translate_type_to_c(&ir.compiler, output, type1, None)?;
            writeln!(output, ") var{};", source)?;
        },

        Instruction::Return(variable) => writeln!(output, "return var{};", variable)?,
        Instruction::Jump(index) => {
            writeln!(output, "goto i{};", index)?;
        },
        Instruction::Branch(condition_variable, if_index, then_index) => {
            writeln!(output, "if (var{}) goto i{}; else goto i{};", condition_variable, if_index, then_index)?;
        },
        Instruction::Phi(..) => {}, // special case above

        Instruction::Nop => writeln!(output, ";")?,
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
fn mangle_function_name<W: Write>(compiler: &Compiler, function: &Function, output: &mut W) -> io::Result<()> {
    if function.is_extern {
        write!(output, "{}", &function.name[0].as_ref().unwrap()[1..])?;
    } else {
        write!(output, "_opus")?;

        let mut i = 0;
        for part in function.name.iter() {
            match *part {
                Some(ref x) => {
                    write!(output, "_")?;
                    mangle_symbol(output, x)?;
                },
                None => {
                    write!(output, "__")?;
                    mangle_type_name(compiler, function.arguments[i], output)?;
                    i += 1;
                },
            }
        }
    }

    Ok(())
}

fn mangle_symbol<W: Write>(output: &mut W, x: &str) -> io::Result<()> {
    write!(output, "{}", match x {
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

fn mangle_type_name<W: Write>(compiler: &Compiler, typ: TypeId, output: &mut W) -> io::Result<()> {
    // FIXME: mangling is just terrible.
    let type_info = compiler.get_type_info(typ);
    match *type_info {
        Type::Integer8 => write!(output, "int8"),
        Type::Integer16 => write!(output, "int16"),
        Type::Integer32 => write!(output, "int32"),
        Type::Integer64 => write!(output, "int64"),
        Type::Natural8 => write!(output, "nat8"),
        Type::Natural16 => write!(output, "nat16"),
        Type::Natural32 => write!(output, "nat32"),
        Type::Natural64 => write!(output, "nat64"),
        Type::GenericInteger | Type::Generic => unreachable!(),
        Type::Null => write!(output, "null"),
        Type::Bool => write!(output, "bool"),
        Type::Pointer(pointer_type, subtype) => {
            let prefix = match pointer_type {
                PointerType::Reference => "Reference",
                PointerType::Mutable => "Mutable",
                PointerType::Array => "ArrayReference",
                PointerType::ArrayMutable => "MutableArrayReference",
            };
            write!(output, "{}To", prefix)?;
            mangle_type_name(compiler, subtype, output)
        },
        Type::Record { ref name, .. } => {
            write!(output, "Record{}", name)
        },
        Type::Function { ref argument_types, return_type } => {
            write!(output, "Function")?;
            for &typ in argument_types.iter() {
                write!(output, "Arg")?;
                mangle_type_name(compiler, typ, output)?;
            }
            write!(output, "Returns")?;
            mangle_type_name(compiler, return_type, output)?;
            Ok(())
        },
        Type::Error => write!(output, "error"),
    }
}
