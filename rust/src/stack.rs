//! Bounded operand stack for MicroVeriVM.

use crate::constants::STACK_SIZE;
use crate::error::Error;

/// A fixed-capacity stack of 32-bit words.
pub struct Stack {
    data: [u32; STACK_SIZE],
    depth: usize,
}

impl Stack {
    /// Creates an empty stack.
    pub const fn new() -> Self {
        Self {
            data: [0; STACK_SIZE],
            depth: 0,
        }
    }

    /// Pushes a word onto the stack.
    pub fn push(&mut self, value: u32) -> Result<(), Error> {
        if self.is_full() {
            return Err(Error::StackOverflow);
        }

        self.data[self.depth] = value;
        self.depth += 1;
        Ok(())
    }

    /// Removes and returns the top word.
    pub fn pop(&mut self) -> Result<u32, Error> {
        if self.is_empty() {
            return Err(Error::StackUnderflow);
        }

        self.depth -= 1;
        Ok(self.data[self.depth])
    }

    /// Returns the top word without removing it.
    pub fn peek(&self) -> Result<u32, Error> {
        if self.is_empty() {
            return Err(Error::StackUnderflow);
        }

        Ok(self.data[self.depth - 1])
    }

    /// Returns the current number of words.
    pub const fn len(&self) -> usize {
        self.depth
    }

    /// Returns whether the stack contains no words.
    pub const fn is_empty(&self) -> bool {
        self.depth == 0
    }

    /// Returns whether the stack is at capacity.
    pub const fn is_full(&self) -> bool {
        self.depth == STACK_SIZE
    }
}

impl Default for Stack {
    fn default() -> Self {
        Self::new()
    }
}
