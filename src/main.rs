pub mod parser;

fn main() {
    use parser::Parser;

    let src = "1
(Foo
\t(Baz) 456 Bar 71)
345";
    let mut parser = Parser::from_src(src);

    loop {
        match parser.parse_expr() {
            Ok(e) => println!("{:?}", e),
            Err(e) => { println!("error: {:?}", e); break },
        }
    }
}
