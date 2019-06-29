mod parse;
mod generate_ir;
mod compile;
mod backend;
mod frontend;

fn main() {
    use std::io::Read;
    let mut src = String::new();
    std::io::stdin().read_to_string(&mut src).unwrap();
    frontend::compile_source(&src, &mut std::io::stdout());
}
