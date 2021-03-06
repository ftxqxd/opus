use std::fs;
use std::path::{Path, PathBuf};
use std::process;
use std::collections::{HashSet, VecDeque};
use argparse::{ArgumentParser, Store, StoreTrue};
use typed_arena::Arena;
use crate::parse::{Parser, Definition};
use crate::generate_ir::IrGenerator;
use crate::compile::{self, Compiler, FrontendDirective};
//use crate::backend::c::CBackend;
use crate::backend::llvm::LlvmBackend;
use crate::backend::Backend;

#[derive(Debug, Clone)]
pub struct Options {
    pub debug: bool,
    pub no_link: bool,
    pub filename: String,
    pub output_path: Option<String>,
    pub linking: Vec<String>,
}

pub fn main() {
    let mut options = Options {
        debug: false,
        no_link: false,
        filename: String::new(),
        output_path: None,
        linking: vec![],
    };
    {
        let mut ap = ArgumentParser::new();
        ap.set_description("The Opus compiler");
        ap.refer(&mut options.output_path)
            .add_option(&["-o", "--output"], argparse::StoreOption, "The file to compile to");
        ap.refer(&mut options.debug)
            .add_option(&["-Z", "--debug"], StoreTrue, "Output debugging information");
        ap.refer(&mut options.no_link)
            .add_option(&["-c", "--no-link"], StoreTrue, "Emit object file, don't link");
        ap.refer(&mut options.filename)
            .required()
            .add_argument("filename", Store, "The path of the file to compile");
        ap.parse_args_or_exit();
    }

    let output_filename = if let Some(ref output_path) = &options.output_path {
        (*output_path).clone().into()
    } else {
        generate_output_path(&options.filename, options.no_link)
    };

    let mut type_arena = typed_arena::Arena::new();
    let mut function_arena = typed_arena::Arena::new();

    let mut compiler = Compiler::new(options, &mut type_arena, &mut function_arena);

    //
    // This part of the code deals largely with imports.
    //

    // Keep track of what paths we've already visited so we don't get into an infinite loop of
    // imports.
    let mut visited_paths = HashSet::new();

    let mut files: VecDeque<PathBuf> = VecDeque::new();
    files.push_back(compiler.options.filename.clone().into());
    compiler.filenames.push(files[0].clone());

    let mut definitions = vec![];

    // This code is kind of ew.  We use arenas for everything to get around a bunch of borrow
    // errors.  There's probably a Better Way To Do It???.
    let source_arena = Arena::new();
    let definition_arena = Arena::new();

    while let Some(file) = files.pop_front() {
        if let Ok(canonical_path) = file.canonicalize() {
            if visited_paths.contains(&canonical_path) {
                continue
            } else {
                visited_paths.insert(canonical_path);
            }
        }

        let source = fs::read_to_string(&file);
        if source.is_err() {
            // FIXME: this error should be reported better (maybe in Compiler) & with a span
            eprintln!("error: could not open file {:?}", file);
            process::exit(1)
        }
        let source = &**source_arena.alloc(source.unwrap());
        compiler.sources.push(source);

        // parent must always exist as `file` refers to a file not a directory
        let directory = file.parent().unwrap();
        for boxed_definition in get_definitions(&mut compiler, source) {
            let definition = &**definition_arena.alloc(boxed_definition);
            match compiler.preload_definition(definition) {
                FrontendDirective::Import(path) => {
                    let mut file2 = PathBuf::new();
                    file2.push(directory);
                    file2.push(String::from_utf8_lossy(path).to_string());
                    compiler.filenames.push(file2.clone());
                    files.push_back(file2);
                },
                FrontendDirective::Library(name) => {
                    compiler.options.linking.push(String::from_utf8_lossy(name).into());
                },
                FrontendDirective::None => {},
            }
            definitions.push(definition);
        }
    }

    // Do the compile!!!

    compile_source(&mut compiler, &definitions, &*output_filename);
}

fn get_definitions<'source>(compiler: &mut Compiler<'source>, source: &'source str) -> Vec<Box<Definition<'source>>> {
    let mut parser = Parser::from_source(compiler, &source);

    let mut definitions = vec![];

    while !parser.is_at_end_of_file() {
        match parser.parse_definition() {
            Ok(d) => {
                definitions.push(d);
            },
            Err(e) => {
                compiler.report_error(compile::Error::ParseError(e));
                process::exit(1)
            },
        }
    }

    definitions
}

fn compile_source<'source>(compiler: &'source mut Compiler<'source>, definitions: &'source [&'source Definition], output_filename: &str) {
    for definition in definitions {
        compiler.finalize_definition(definition);
    }

    let mut translate = !compiler.has_errors.get();
    let mut backend = LlvmBackend::new(compiler);

    backend.initialize();

    if translate {
        for definition in definitions {
            match **definition {
                Definition::Variable(ref name, ..) | Definition::Constant(ref name, ..) => {
                    let global_id = compiler.global_resolution_map[name];
                    let &(typ, ref value) = &compiler.globals[global_id];
                    backend.add_global(global_id, typ, value);
                },
                _ => {},
            }
        }

        for definition in definitions {
            if let Definition::Function(ref sig, ref block) = **definition {
                let span = compiler.definition_spans[&(&**definition as *const _)];
                let ir_generator = IrGenerator::from_function(&compiler, sig, block, span);

                if compiler.options.debug {
                    eprintln!("{}", ir_generator);
                }

                if compiler.has_errors.get() {
                    translate = false;
                }

                if translate {
                    backend.translate_ir(&ir_generator);
                }
            }
        }
    }

    if !translate {
        process::exit(1);
    }

    backend.output(output_filename).unwrap();
}

fn generate_output_path(input_filename: &str, no_link: bool) -> Box<str> {
    let path = Path::new(input_filename);
    let basename = path.file_name().unwrap().to_str().unwrap();

    let extension = if no_link { ".o" } else { "" };
    if basename.ends_with(".opus") {
        format!("{}{}", &basename[..basename.len() - 5], extension).into()
    } else {
        "a.out".into()
    }
}

pub fn print_span<'source>(compiler: &Compiler<'source>, span: &'source str) {
    use std::num::Wrapping;

    for (i, &source) in compiler.sources.iter().enumerate() {
        let low = (Wrapping(span as *const str as *const u8 as usize) - Wrapping(source as *const str as *const u8 as usize)).0;
        if low > source.len() {
            continue
        }
        eprintln!("\x1b[33m{}:\x1b[0m", compiler.filenames[i].to_string_lossy());
        let high = low + span.len();

        // Find the beginning and end of the line(s) containing this span as well as the line number
        let mut line_low = 0;
        let mut line_number = 1;
        let mut position = 0;
        for character in source[..low].chars() {
            if position == low {
                break
            }
            position += character.len_utf8();
            if character == '\n' {
                line_number += 1;
                line_low = position;
            }
        }
        let mut line_high = high;
        for character in source[high..].chars() {
            if character == '\n' {
                break
            }
            line_high += character.len_utf8();
        }

        eprint!("\x1b[33m{:>4}:\x1b[0m ", line_number);
        for (i, c) in source[line_low..line_high].char_indices() {
            let i = line_low + i;
            if i == low {
                eprint!("\x1b[31;1m");
            } else if i == high {
                eprint!("\x1b[0m");
            }
            match c {
                '\t' => eprint!("    "),
                '\n' => {
                    line_number += 1;
                    eprint!("\n\x1b[33m{:>4}:\x1b[0m ", line_number);
                    if i >= low && i < high {
                        eprint!("\x1b[31;1m");
                    }
                }
                _ => eprint!("{}", c),
            }
        }
        eprintln!("\x1b[0m");
    }
}
