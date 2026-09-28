#![no_std]
#![forbid(unsafe_code)]

//! MicroVeriVM Phase 1.
//!
//! This crate contains only architectural constants and execution trap types.

pub mod constants;
pub mod error;
pub mod execute;
pub mod instruction;
pub mod memory;
pub mod stack;
pub mod state;
