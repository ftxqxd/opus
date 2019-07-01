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

fn translate_type_to_c<W: Write>(_compiler: &Compiler, output: &mut W, typ: &Type) -> io::Result<()> {
    match *typ {
        Type::Integer64 => write!(output, "int64_t"),
        Type::Natural64 => write!(output, "uint64_t"),
        Type::Null => write!(output, "_opust_null"),
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
        Instruction::Return(variable) => writeln!(output, "return var{};", variable)?,
        Instruction::Jump(index) => {
            writeln!(output, "goto i{};", index)?;
        },
        Instruction::Branch(condition_variable, if_index, then_index) => {
            writeln!(output, "if (var{}) goto i{}; else goto i{};", condition_variable, if_index, then_index)?;
        },
        Instruction::Nop => writeln!(output, "")?,
        Instruction::Error(variable) => writeln!(output, "/* error with var{} */", variable)?,
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

    Ok(())
}

fn mangle_type_name<W: Write>(typ: &Type, output: &mut W) -> io::Result<()> {
    match *typ {
        Type::Integer64 => write!(output, "int64"),
        Type::Natural64 => write!(output, "nat64"),
        Type::Null => write!(output, "null"),
        Type::Error => write!(output, "error"),
    }
}
