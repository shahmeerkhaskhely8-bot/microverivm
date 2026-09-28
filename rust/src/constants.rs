//! Architectural constants for MicroVeriVM.

/// The modulus for 32-bit machine words.
pub const WORD_MODULUS: u64 = 4_294_967_296;

/// Maximum number of words in the VM stack.
pub const STACK_SIZE: usize = 256;

/// Number of addressable words in VM memory.
pub const MEMORY_SIZE: usize = 1024;
