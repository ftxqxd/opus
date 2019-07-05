//! The C backend for the Opus compiler.
//!
//! This part of the compiler governs the translation between the Opus IR format (defined in
//! `generate_ir.rs`) and C code.

use std::io::{self, Write};
use crate::generate_ir::{IrGenerator, Instruction};
use crate::compile::{Function, Type, Compiler};

/// Initialize C code generation by writing necessary `#include` statements, function prototypes,
/// and the main function.
pub fn initialize<W: Write>(compiler: &Compiler, output: &mut W) -> io::Result<()> {
    // Headers
    writeln!(output, "#include <stdint.h>")?;
    writeln!(output, "#include <stdio.h>")?;

    // Builtin types
    writeln!(output, "typedef uint8_t _opust_null;")?;

    // Prototypes
    for (_, function) in compiler.resolution_map.iter() {
        translate_function_signature_to_c(compiler, function, output)?;
        writeln!(output, ";")?;
    }

    // Builtins
    writeln!(output, r#"_opust_null _opus_Print__int64(int64_t var0) {{ printf("%d\n", var0); return 0; }}"#)?;

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
        translate_type_to_c(&ir.compiler, output, &variable.typ)?;
        write!(output, " var{};\n", i)?;
    }

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
    translate_type_to_c(compiler, output, &function.return_type)?;
    write!(output, " ")?;
    mangle_function_name(function, output)?;
    write!(output, "(")?;
    // Write argument types
    let mut written_anything = false;
    if function.arguments.len() == 0 {
        write!(output, "void")?;
    }
    for (i, argument_type) in function.arguments.iter().enumerate() {
        if written_anything {
            write!(output, ", ")?;
        }
        written_anything = true;

        translate_type_to_c(&compiler, output, argument_type)?;
        write!(output, " var{}", i)?;
    }
    write!(output, ")")
}

fn translate_type_to_c<W: Write>(compiler: &Compiler, output: &mut W, typ: &Type) -> io::Result<()> {
    match *typ {
        Type::Integer8 => write!(output, "int8_t"),
        Type::Integer16 => write!(output, "int16_t"),
        Type::Integer32 => write!(output, "int32_t"),
        Type::Integer64 => write!(output, "int64_t"),
        Type::Natural8 => write!(output, "uint8_t"),
        Type::Natural16 => write!(output, "uint16_t"),
        Type::Natural32 => write!(output, "uint32_t"),
        Type::Natural64 => write!(output, "uint64_t"),
        Type::Null => write!(output, "_opust_null"),
        Type::Pointer(ref subtype) => {
            write!(output, "const ")?;
            translate_type_to_c(compiler, output, subtype)?;
            write!(output, " *")
        },
        Type::Error => write!(output, "internal_compiler_error"),
    }
}

fn translate_instruction_to_c<W: Write>(ir: &IrGenerator, output: &mut W, instruction_index: usize) -> io::Result<()> {
    write!(output, "i{}: ", instruction_index)?;
    let instruction = &ir.instructions[instruction_index];
    match *instruction {
        Instruction::ConstantInteger(destination, constant) => writeln!(output, "var{} = {};", destination, constant)?,
        Instruction::Call(destination, function, ref arguments) => {
            write!(output, "var{} = ", destination)?;
            mangle_function_name(function, output)?;
            write!(output, "(")?;
            for (i, argument) in arguments.iter().enumerate() {
                if i > 0 {
                    write!(output, ", ")?;
                }
                write!(output, "var{}", argument)?;
            }
            writeln!(output, ");")?;
        },

        Instruction::Add(destination, left, right) => writeln!(output, "var{} = var{} + var{};", destination, left, right)?,
        Instruction::Subtract(destination, left, right) => writeln!(output, "var{} = var{} - var{};", destination, left, right)?,
        Instruction::Multiply(destination, left, right) => writeln!(output, "var{} = var{} * var{};", destination, left, right)?,
        Instruction::Divide(destination, left, right) => writeln!(output, "var{} = var{} / var{};", destination, left, right)?,

        Instruction::Reference(destination, value) => writeln!(output, "var{} = &var{};", destination, value)?,
        Instruction::Dereference(destination, value) => writeln!(output, "var{} = *var{};", destination, value)?,

        Instruction::Cast(destination, source) => {
            let type1 = &ir.variables[destination].typ;
            write!(output, "var{} = (", destination)?;
            translate_type_to_c(&ir.compiler, output, type1)?;
            writeln!(output, ") var{};", source)?;
        },

        Instruction::Return(variable) => writeln!(output, "return var{};", variable)?,
        Instruction::Jump(index) => {
            writeln!(output, "goto i{};", index)?;
        },
        Instruction::Branch(condition_variable, if_index, then_index) => {
            writeln!(output, "if (var{}) goto i{}; else goto i{};", condition_variable, if_index, then_index)?;
        },

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
fn mangle_function_name<W: Write>(function: &Function, output: &mut W) -> io::Result<()> {
    if function.is_extern {
        debug_assert!(function.name.len() > 0);
        debug_assert!(function.name[1..].iter().all(|x| x.is_none()));
        debug_assert!(function.name[0].is_some());
        debug_assert_eq!(function.name[0].as_ref().unwrap().chars().next(), Some('\''));

        write!(output, "{}", &function.name[0].as_ref().unwrap()[1..])?;
    } else {
        write!(output, "_opus")?;

        let mut i = 0;
        for part in function.name.iter() {
            match *part {
                Some(ref x) => {
                    write!(output, "_{}", x)?;
                },
                None => {
                    write!(output, "__")?;
                    mangle_type_name(&function.arguments[i], output)?;
                    i += 1;
                },
            }
        }
    }

    Ok(())
}

fn mangle_type_name<W: Write>(typ: &Type, output: &mut W) -> io::Result<()> {
    match *typ {
        Type::Integer8 => write!(output, "int8"),
        Type::Integer16 => write!(output, "int16"),
        Type::Integer32 => write!(output, "int32"),
        Type::Integer64 => write!(output, "int64"),
        Type::Natural8 => write!(output, "nat8"),
        Type::Natural16 => write!(output, "nat16"),
        Type::Natural32 => write!(output, "nat32"),
        Type::Natural64 => write!(output, "nat64"),
        Type::Null => write!(output, "null"),
        Type::Pointer(ref subtype) => {
            write!(output, "PointerTo")?;
            mangle_type_name(subtype, output)
        },
        Type::Error => write!(output, "error"),
    }
}
