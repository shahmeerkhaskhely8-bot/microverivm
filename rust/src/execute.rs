//! Single-step execution for MicroVeriVM.

use crate::constants::MEMORY_SIZE;
use crate::error::Error;
use crate::instruction::Instruction;
use crate::state::{State, Status};

/// Executes the instruction at the state's current program counter.
pub fn step(state: &mut State, code: &[Instruction]) -> Result<(), Error> {
    if state.status() == Status::Halted {
        return Ok(());
    }

    let pc = usize::try_from(state.pc()).map_err(|_| Error::InvalidProgramCounter)?;
    if pc >= code.len() {
        return Err(Error::InvalidProgramCounter);
    }

    let instruction = code[pc];
    match instruction {
        Instruction::CONST(value) => {
            state.stack_mut().push(value)?;
            advance_pc(state)
        }
        Instruction::ADD => {
            let right = state.stack_mut().pop()?;
            let left = state.stack_mut().pop()?;
            let result = left.wrapping_add(right);
            state.stack_mut().push(result)?;
            advance_pc(state)
        }
        Instruction::SUB => {
            let right = state.stack_mut().pop()?;
            let left = state.stack_mut().pop()?;
            let result = left.wrapping_sub(right);
            state.stack_mut().push(result)?;
            advance_pc(state)
        }
        Instruction::DUP => {
            let value = state.stack().peek()?;
            state.stack_mut().push(value)?;
            advance_pc(state)
        }
        Instruction::DROP => {
            state.stack_mut().pop()?;
            advance_pc(state)
        }
        Instruction::LOAD(address) => {
            let address = usize::try_from(address).map_err(|_| Error::MemoryOutOfBounds)?;
            let value = state.memory().load(address)?;
            state.stack_mut().push(value)?;
            advance_pc(state)
        }
        Instruction::STORE(address) => {
            let address = usize::try_from(address).map_err(|_| Error::MemoryOutOfBounds)?;
            if address >= MEMORY_SIZE {
                return Err(Error::MemoryOutOfBounds);
            }
            let value = state.stack_mut().pop()?;
            state.memory_mut().store(address, value)?;
            advance_pc(state)
        }
        Instruction::JMP(target) => {
            validate_target(target, code.len())?;
            state.set_pc(target);
            Ok(())
        }
        Instruction::JZ(target) => {
            let condition = state.stack_mut().pop()?;
            if condition == 0 {
                validate_target(target, code.len())?;
                state.set_pc(target);
            } else {
                advance_pc(state)?;
            }
            Ok(())
        }
        Instruction::HALT => {
            *state.status_mut() = Status::Halted;
            Ok(())
        }
    }
}

fn advance_pc(state: &mut State) -> Result<(), Error> {
    state.set_pc(state.pc().wrapping_add(1));
    Ok(())
}

fn validate_target(target: u32, code_len: usize) -> Result<(), Error> {
    match usize::try_from(target) {
        Ok(target_index) if target_index < code_len => Ok(()),
        _ => Err(Error::InvalidProgramCounter),
    }
}

#[cfg(test)]
mod tests {
    use super::advance_pc;
    use super::step;
    use super::validate_target;
    use crate::error::Error;
    use crate::instruction::Instruction;
    use crate::state::State;

    #[test]
    fn program_counter_wraps_at_u32_max() {
        let mut state = State::new();
        state.set_pc(u32::MAX);

        assert_eq!(advance_pc(&mut state), Ok(()));
        assert_eq!(state.pc(), 0);
    }

    #[test]
    fn oversized_jump_target_is_rejected() {
        assert_eq!(
            validate_target(u32::MAX, 1),
            Err(Error::InvalidProgramCounter)
        );
    }

    #[test]
    fn maximum_program_counter_is_rejected_for_short_program() {
        let mut state = State::new();
        state.set_pc(u32::MAX);

        assert_eq!(
            step(&mut state, &[Instruction::HALT]),
            Err(Error::InvalidProgramCounter)
        );
    }
}
