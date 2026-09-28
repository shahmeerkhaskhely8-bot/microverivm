use std::io::{self, Write};
use std::process::ExitCode;

use microverivm::execute::step;
use microverivm::instruction::Instruction;
use microverivm::state::{State, Status};

fn main() -> ExitCode {
    let program = [
        Instruction::CONST(40),
        Instruction::CONST(2),
        Instruction::ADD,
        Instruction::HALT,
    ];
    let mut state = State::new();

    for _ in 0..program.len() {
        if state.status() == Status::Halted {
            break;
        }

        if let Err(error) = step(&mut state, &program) {
            report_failure(&format!("MicroVeriVM demo failed: {error:?}"));
            return ExitCode::FAILURE;
        }
    }

    if state.status() != Status::Halted {
        report_failure("MicroVeriVM demo did not halt within its instruction budget");
        return ExitCode::FAILURE;
    }

    match state.stack().peek() {
        Ok(value) => match writeln!(io::stdout().lock(), "MicroVeriVM demo result: {value}") {
            Ok(()) => ExitCode::SUCCESS,
            Err(error) => {
                report_failure(&format!("Could not write demo result: {error}"));
                ExitCode::FAILURE
            }
        },
        Err(error) => {
            report_failure(&format!("MicroVeriVM demo produced no result: {error:?}"));
            ExitCode::FAILURE
        }
    }
}

fn report_failure(message: &str) {
    let _ = writeln!(io::stderr().lock(), "{message}");
}
