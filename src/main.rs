extern crate typed_arena;
extern crate argparse;
extern crate llvm_sys;

mod parse;
mod generate_ir;
mod compile;
mod backend;
mod frontend;

fn main() {
    frontend::main();
}
