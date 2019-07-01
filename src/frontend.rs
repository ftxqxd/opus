use std::io::Write;
use crate::parse::{Parser, Definition, Error};
use crate::generate_ir::IrGenerator;
use crate::compile::Compiler;
use crate::backend::c;

pub fn compile_source<W: Write>(src: &str, output: &mut W) {
    let mut parser = Parser::from_source(src);

    let mut definitions = vec![];

    loop {
        match parser.parse_definition() {
            Ok(d) => {
                definitions.push(d);
            },
            Err(Error::UnexpectedEof) => break,
            Err(e) => { eprintln!("error: {:?}", e); return },
        }
    }

    let mut compiler = Compiler::new();
    for definition in &definitions {
        compiler.parse_definition(definition);
    }

    let mut translate = true;
    c::initialize(&compiler, output).unwrap();
    for &Definition::Function(ref sig, ref block) in &definitions {
        let ir_generator = IrGenerator::from_function(&compiler, sig, block);

        println!("{}", ir_generator);
        if compiler.has_errors.get() {
            translate = false;
        }

        if translate {
            c::translate_ir_to_c(&ir_generator, output).unwrap();
        }
    }

    if !translate {
        panic!("compilation unsuccessful");
    }
}
