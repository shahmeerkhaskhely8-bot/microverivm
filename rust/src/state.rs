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
}

impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}
