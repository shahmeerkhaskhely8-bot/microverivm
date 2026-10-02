//! MicroVeriVM machine state.

use crate::memory::Memory;
use crate::stack::Stack;

/// Current machine execution status.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Status {
    /// The machine has not halted.
    Running,
    /// The machine has halted.
    Halted,
}

/// Borrowed, allocation-free observation of a machine state.
///
/// `stack_data[..stack_depth]` is the active stack storage in bottom-to-top
/// order; `memory_data` exposes the complete fixed-size memory.
#[cfg(test)]
pub(crate) struct StateView<'a> {
    pub(crate) pc: u32,
    pub(crate) stack_data: &'a [u32; crate::constants::STACK_SIZE],
    pub(crate) stack_depth: usize,
    pub(crate) memory_data: &'a [u32; crate::constants::MEMORY_SIZE],
    pub(crate) status: Status,
}

/// Complete MicroVeriVM machine state without execution logic.
pub struct State {
    pc: u32,
    stack: Stack,
    memory: Memory,
    status: Status,
}

impl State {
    /// Creates the initial machine state.
    pub const fn new() -> Self {
        Self {
            pc: 0,
            stack: Stack::new(),
            memory: Memory::new(),
            status: Status::Running,
        }
    }

    /// Returns the current program counter.
    pub const fn pc(&self) -> u32 {
        self.pc
    }

    /// Sets the current program counter.
    pub const fn set_pc(&mut self, pc: u32) {
        self.pc = pc;
    }

    /// Returns an immutable reference to the stack.
    pub const fn stack(&self) -> &Stack {
        &self.stack
    }

    /// Returns a mutable reference to the stack.
    pub const fn stack_mut(&mut self) -> &mut Stack {
        &mut self.stack
    }

    /// Returns an immutable reference to memory.
    pub const fn memory(&self) -> &Memory {
        &self.memory
    }

    /// Returns a mutable reference to memory.
    pub const fn memory_mut(&mut self) -> &mut Memory {
        &mut self.memory
    }

    /// Returns the current machine status.
    pub const fn status(&self) -> Status {
        self.status
    }

    /// Returns a mutable reference to the machine status.
    pub const fn status_mut(&mut self) -> &mut Status {
        &mut self.status
    }

    #[cfg(test)]
    pub(crate) const fn view(&self) -> StateView<'_> {
        StateView {
            pc: self.pc,
            stack_data: self.stack.storage(),
            stack_depth: self.stack.len(),
            memory_data: self.memory.storage(),
            status: self.status,
        }
    }
}

impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}
