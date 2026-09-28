use microverivm::constants::{MEMORY_SIZE, WORD_MODULUS};
use microverivm::error::Error;
use microverivm::execute::step;
use microverivm::instruction::Instruction;
use microverivm::state::{State, Status};

fn run_until_halt(state: &mut State, code: &[Instruction]) -> Result<(), Error> {
    let mut steps = 0;
    while state.status() == Status::Running && steps < 128 {
        step(state, code)?;
        steps += 1;
    }

    assert_eq!(state.status(), Status::Halted, "program did not halt");
    Ok(())
}

#[test]
fn executes_all_ten_instructions_end_to_end() {
    let code = [
        Instruction::CONST(7),  // 0
        Instruction::CONST(5),  // 1
        Instruction::ADD,       // 2: 12
        Instruction::DUP,       // 3: 12, 12
        Instruction::DROP,      // 4: 12
        Instruction::STORE(0),  // 5: memory[0] = 12
        Instruction::LOAD(0),   // 6: 12
        Instruction::CONST(12), // 7
        Instruction::SUB,       // 8: 0
        Instruction::JZ(11),    // 9: jump to HALT
        Instruction::JMP(10),   // 10: not taken
        Instruction::HALT,      // 11
    ];
    let mut state = State::new();

    assert_eq!(run_until_halt(&mut state, &code), Ok(()));
    assert_eq!(state.status(), Status::Halted);
    assert_eq!(state.pc(), 11);
    assert_eq!(state.stack().len(), 0);
    assert_eq!(state.memory().load(0), Ok(12));
}

#[test]
fn arithmetic_wraps_at_word_modulus() {
    let code = [
        Instruction::CONST(u32::MAX),
        Instruction::CONST(1),
        Instruction::ADD,
        Instruction::CONST(1),
        Instruction::SUB,
        Instruction::HALT,
    ];
    let mut state = State::new();

    assert_eq!(run_until_halt(&mut state, &code), Ok(()));
    assert_eq!(state.stack().peek(), Ok(u32::MAX));
    assert_eq!(WORD_MODULUS, 4_294_967_296);
}

#[test]
fn arithmetic_boundary_matches_u32_wrapping() {
    let add_code = [
        Instruction::CONST(u32::MAX),
        Instruction::CONST(1),
        Instruction::ADD,
    ];
    let mut add_state = State::new();
    for _ in 0..add_code.len() {
        assert_eq!(step(&mut add_state, &add_code), Ok(()));
    }
    assert_eq!(add_state.stack().peek(), Ok(0));

    let sub_code = [
        Instruction::CONST(0),
        Instruction::CONST(1),
        Instruction::SUB,
    ];
    let mut sub_state = State::new();
    for _ in 0..sub_code.len() {
        assert_eq!(step(&mut sub_state, &sub_code), Ok(()));
    }
    assert_eq!(sub_state.stack().peek(), Ok(u32::MAX));
}

#[test]
fn jz_nonzero_increments_pc_and_jmp_sets_pc() {
    let jz_code = [
        Instruction::CONST(1),
        Instruction::JZ(4),
        Instruction::JMP(4),
        Instruction::CONST(99),
        Instruction::HALT,
    ];
    let mut jz_state = State::new();
    assert_eq!(step(&mut jz_state, &jz_code), Ok(()));
    assert_eq!(jz_state.pc(), 1);
    assert_eq!(step(&mut jz_state, &jz_code), Ok(()));
    assert_eq!(jz_state.pc(), 2);
    assert_eq!(step(&mut jz_state, &jz_code), Ok(()));
    assert_eq!(jz_state.pc(), 4);

    let jmp_code = [
        Instruction::JMP(2),
        Instruction::CONST(99),
        Instruction::HALT,
    ];
    let mut jmp_state = State::new();
    assert_eq!(step(&mut jmp_state, &jmp_code), Ok(()));
    assert_eq!(jmp_state.pc(), 2);
}

#[test]
fn traps_stack_and_memory_bounds() {
    let mut empty = State::new();
    assert_eq!(
        step(&mut empty, &[Instruction::ADD]),
        Err(Error::StackUnderflow)
    );

    let mut full = State::new();
    for value in 0..256 {
        assert_eq!(full.stack_mut().push(value), Ok(()));
    }
    assert_eq!(
        step(&mut full, &[Instruction::CONST(256)]),
        Err(Error::StackOverflow)
    );

    let mut load_oob = State::new();
    assert_eq!(
        step(&mut load_oob, &[Instruction::LOAD(MEMORY_SIZE as u32)]),
        Err(Error::MemoryOutOfBounds)
    );

    let mut load_max_address = State::new();
    assert_eq!(
        step(&mut load_max_address, &[Instruction::LOAD(u32::MAX)]),
        Err(Error::MemoryOutOfBounds)
    );

    let mut store_oob = State::new();
    assert_eq!(store_oob.stack_mut().push(1), Ok(()));
    assert_eq!(
        step(&mut store_oob, &[Instruction::STORE(MEMORY_SIZE as u32)]),
        Err(Error::MemoryOutOfBounds)
    );
    assert_eq!(store_oob.stack().peek(), Ok(1));

    let mut store_max_address = State::new();
    assert_eq!(store_max_address.stack_mut().push(1), Ok(()));
    assert_eq!(
        step(&mut store_max_address, &[Instruction::STORE(u32::MAX)]),
        Err(Error::MemoryOutOfBounds)
    );
    assert_eq!(store_max_address.stack().peek(), Ok(1));
}

#[test]
fn invalid_program_counter_and_halt_are_safe() {
    let mut invalid = State::new();
    invalid.set_pc(1);
    assert_eq!(
        step(&mut invalid, &[Instruction::HALT]),
        Err(Error::InvalidProgramCounter)
    );

    let mut halted = State::new();
    assert_eq!(step(&mut halted, &[Instruction::HALT]), Ok(()));
    assert_eq!(halted.status(), Status::Halted);
    assert_eq!(halted.pc(), 0);
    assert_eq!(step(&mut halted, &[Instruction::CONST(99)]), Ok(()));
    assert_eq!(halted.pc(), 0);
    assert_eq!(halted.stack().len(), 0);
}
