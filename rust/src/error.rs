//! Error and trap conditions for MicroVeriVM.

/// Conditions that stop VM execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    /// A stack push would exceed [`crate::constants::STACK_SIZE`].
    StackOverflow,
    /// A stack pop would read from an empty stack.
    StackUnderflow,
    /// A memory access is outside [`crate::constants::MEMORY_SIZE`].
    MemoryOutOfBounds,
    /// The program counter does not identify a valid instruction location.
    InvalidProgramCounter,
    /// The instruction at the program counter is not valid.
    InvalidInstruction,
}
