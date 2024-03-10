#![feature(iter_intersperse)]
#![feature(box_patterns)]

pub mod serialize;
pub mod syntax;
pub mod tyctxt;
pub const ENABLE_PRINTF_DEBUG:bool = true;
#[derive(Clone,Copy,PartialEq, Eq)]
pub enum VarDumper{
    /// Print variable hashes
    HashDumper,
    /// Print variables using standard rust formatting 
    StdVarDumper,
    /// Print variables using the c `printf` function 
    PrintfVarDumper,
}