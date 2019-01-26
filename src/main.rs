pub mod parser;

fn main() {
    use parser::Parser;

    let src = "
        (Foo  (Baz) 456 Bar 71)
    ";
    let mut parser = Parser::from_src(src);

    println!("{:?}", parser.parse_expr());
}
