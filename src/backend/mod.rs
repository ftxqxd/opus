pub mod llvm;

use std::io;
use crate::generate_ir::IrGenerator;

pub trait Backend {
    fn initialize(&mut self);
    fn translate_ir(&mut self, ir: &IrGenerator);
    fn output(&mut self, filename: &str) -> io::Result<()>;
}
