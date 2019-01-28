pub mod parser;

fn main() {
    use parser::Parser;

    let src = "\
(Print foo: int64 To output: writableStream)
\t(Print (Convert foo To String) To output)
\t(Log something)";
    let mut parser = Parser::from_source(src);

    loop {
        match parser.parse_definition() {
            Ok(e) => println!("{:?}", e),
            Err(e) => { println!("error: {:?}", e); break },
        }
    }
}
