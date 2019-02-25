mod parse;
mod generate_ir;
mod compile;

fn main() {
    use parse::{Parser, Definition};
    use generate_ir::IrGenerator;
    use compile::Compiler;

    let src = "\
(Frobnicate x: int64): int64
\t123
\t456
(Main): int64
\tvar x = 137
\tvar x = 893
\tvar y = 214
\t(Frobnicate x)";
    let mut parser = Parser::from_source(src);

    let mut definitions = vec![];

    loop {
        match parser.parse_definition() {
            Ok(d) => {
                definitions.push(d);
            },
            Err(e) => { println!("error: {:?}", e); break },
        }
    }

    let mut compiler = Compiler::new();
    for definition in &definitions {
        compiler.parse_definition(definition);
    }

    for &Definition::Function(ref sig, ref block) in &definitions {
        let mut ir_generator = IrGenerator::with_compiler(&compiler);
        ir_generator.generate_ir_from_function(sig, block);
        println!("{}", ir_generator);
    }
}
