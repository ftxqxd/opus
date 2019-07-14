pub mod c;
pub mod llvm;

use std::io;
use crate::generate_ir::IrGenerator;

pub trait Backend {
    fn initialize(&mut self) -> io::Result<()>;
    fn translate_ir(&mut self, ir: &IrGenerator) -> io::Result<()>;
}
