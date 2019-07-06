mod parse;
mod generate_ir;
mod compile;
mod backend;
mod frontend;

fn main() {
    frontend::main();
}
