//! MicroVeriVM instruction definitions.

/// The ten instructions supported by MicroVeriVM Phase 2.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Instruction {
    /// Push a constant word.
    CONST(u32),
    /// Add the top two stack words.
    ADD,
    /// Subtract the top stack word from the next stack word.
    SUB,
    /// Duplicate the top stack word.
    DUP,
    /// Drop the top stack word.
    DROP,
    /// Load a word from an address.
    LOAD(u32),
    /// Store a word at an address.
    STORE(u32),
    /// Jump to a target.
    JMP(u32),
    /// Jump to a target when the condition is zero.
    JZ(u32),
    /// Halt execution.
    HALT,
}
