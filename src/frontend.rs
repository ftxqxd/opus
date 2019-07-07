extern crate argparse;

use std::io::{Read, Write};
use std::fs;
use std::process::{self, Command, Stdio};
use argparse::{ArgumentParser, Store, StoreTrue};
use crate::parse::{Parser, Definition};
use crate::generate_ir::IrGenerator;
use crate::compile::{self, Compiler};
use crate::backend::c;

#[derive(Debug, Clone)]
pub struct Options {
    pub debug: bool,
    pub no_link: bool,
    pub filename: String,
    pub output_path: Option<String>,
}

pub fn main() {
    let mut options = Options {
        debug: false,
        no_link: false,
        filename: String::new(),
        output_path: None,
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

    let source = fs::read_to_string(&options.filename);
    match source {
        Ok(source) => {
            let s;
            let output_filename = if let Some(ref output_path) = &options.output_path {
                &*output_path
            } else {
                s = generate_output_filename(&options.filename, options.no_link);
                &*s
            };
            let mut command = Command::new("cc");

            command
                .arg("-x").arg("c")
                .arg("-")
                .arg("-o").arg(output_filename);
            if options.no_link {
                command.arg("-c");
            }

            let mut compiler_process = command
                .stdin(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .expect("failed to spawn cc process");

            let mut stdin = compiler_process.stdin.as_mut().expect("failed to open cc stdin");

            let mut compiler = Compiler::with_options(options, &source);
            let mut parser = Parser::from_source(&mut compiler, &source);

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

            compile_source(&mut compiler, &definitions, &mut stdin);

            let result = compiler_process.wait();
            let stderr = compiler_process.stderr.as_mut().expect("failed to open cc stderr");
            let mut err = String::new();
            stderr.read_to_string(&mut err).unwrap();

            if !result.unwrap().success() {
                eprintln!("internal compiler error: cc exited with non-zero status");
                eprint!("{}", err);
                process::exit(1)
            }

            if err.len() != 0 {
                eprintln!("cc emitted warnings:");
                eprint!("{}", err);
            }
        },
        Err(_) => {
            eprintln!("error: could not open file {}", options.filename);
            process::exit(1)
        },
    }
}

fn compile_source<'source, W: Write>(compiler: &mut Compiler<'source>, definitions: &'source [Box<Definition>], output: &mut W) {
    for definition in definitions {
        compiler.parse_definition(definition);
    }

    let mut translate = true;
    c::initialize(compiler, output).unwrap();
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
                c::translate_ir_to_c(&ir_generator, output).unwrap();
            }
        }
    }

    if !translate {
        process::exit(1);
    }
}

fn generate_output_filename(input_filename: &str, no_link: bool) -> Box<str> {
    let extension = if no_link { ".o" } else { "" };
    if input_filename.ends_with(".opus") {
        format!("{}{}", &input_filename[..input_filename.len() - 5], extension).into()
    } else {
        "a.out".into()
    }
}

pub fn print_span<'source>(source: &'source str, span: &'source str) {
    let low = span as *const str as *const u8 as usize - source as *const str as *const u8 as usize;
    debug_assert!(low <= source.len());
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
    for i in line_low..line_high {
        if i == low {
            eprint!("\x1b[31;1m");
        } else if i == high {
            eprint!("\x1b[0m");
        }
        let c = source[i..].chars().next().unwrap();
        match c {
            '\t' => eprint!("        "),
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
