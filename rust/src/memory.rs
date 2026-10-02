//! Bounded word-addressed memory for MicroVeriVM.

use crate::constants::MEMORY_SIZE;
use crate::error::Error;

/// Fixed-capacity memory containing 32-bit words.
pub struct Memory {
    data: [u32; MEMORY_SIZE],
}

impl Memory {
    /// Creates zero-initialized memory.
    pub const fn new() -> Self {
        Self {
            data: [0; MEMORY_SIZE],
        }
    }

    /// Loads a word from a checked address.
    pub fn load(&self, address: usize) -> Result<u32, Error> {
        if address >= MEMORY_SIZE {
            return Err(Error::MemoryOutOfBounds);
        }

        Ok(self.data[address])
    }

    /// Stores a word at a checked address.
    pub fn store(&mut self, address: usize, value: u32) -> Result<(), Error> {
        if address >= MEMORY_SIZE {
            return Err(Error::MemoryOutOfBounds);
        }

        self.data[address] = value;
        Ok(())
    }

    #[cfg(test)]
    pub(crate) const fn storage(&self) -> &[u32; MEMORY_SIZE] {
        &self.data
    }
}

impl Default for Memory {
    fn default() -> Self {
        Self::new()
    }
}
