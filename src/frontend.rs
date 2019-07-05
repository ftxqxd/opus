use std::io::Write;
use crate::parse::{Parser, Definition};
use crate::generate_ir::IrGenerator;
use crate::compile::Compiler;
use crate::backend::c;

pub fn compile_source<W: Write>(src: &str, output: &mut W) {
    let mut compiler = Compiler::new();
    let mut parser = Parser::from_source(&mut compiler, src);

    let mut definitions = vec![];

    while !parser.is_at_end_of_file() {
        match parser.parse_definition() {
            Ok(d) => {
                definitions.push(d);
            },
            Err(e) => { eprintln!("error: {:?}", e); return },
        }
    }

    for definition in &definitions {
        compiler.parse_definition(definition);
    }

    let mut translate = true;
    c::initialize(&compiler, output).unwrap();
    for definition in &definitions {
        if let Definition::Function(ref sig, ref block) = **definition {
            let span = compiler.definition_spans[&(&**definition as *const _)];
            let ir_generator = IrGenerator::from_function(&compiler, sig, block, span);

            eprintln!("{}", ir_generator);
            if compiler.has_errors.get() {
                translate = false;
            }

            if translate {
                c::translate_ir_to_c(&ir_generator, output).unwrap();
            }
        }
    }

    if !translate {
        panic!("compilation unsuccessful");
    }
}
