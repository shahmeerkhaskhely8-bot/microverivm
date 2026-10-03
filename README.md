# MicroVeriVM 🦀

MicroVeriVM is a lightweight, deterministic 32-bit stack virtual machine
implemented in safe Rust. It provides bounded stack and memory storage,
explicit execution errors, and a numeric program counter. The repository also
contains Rocq (Coq) models and machine-checked proofs for the stack VM and a
separate RV32I instruction subset.

## Why this machine

MicroVeriVM makes execution boundaries explicit: the stack and memory have
fixed capacities, invalid accesses return named errors, and arithmetic
overflow has defined wrapping behavior. These choices make the modeled
behavior easier to inspect and test than an implementation with implicit
bounds or overflow assumptions. The crate is designed for educational and
systems-programming use; the repository's formal results apply to the stated
Coq models and do not prove the Rust implementation itself.

The Rust crate is a `no_std` library that forbids unsafe code and does not
dynamically allocate VM stack or memory. Its transition behavior, capacities,
and validation limits are documented below rather than implying broader
security or reliability guarantees.

The stack VM has ten instructions, a 256-word operand stack, and 1024 words of
memory. `ADD`, `SUB`, and sequential PC advancement use modulo-\(2^{32}\)
wrapping semantics. Stack underflow/overflow, invalid addresses, and invalid
program counters are reported as named errors.

## Supported stack instructions

| Instruction | Behavior |
| --- | --- |
| `CONST(value)` | Push a 32-bit value. |
| `ADD` | Pop two values and push their wrapping sum. |
| `SUB` | Pop two values and push the wrapping difference (left minus right). |
| `DUP` | Duplicate the top value. |
| `DROP` | Remove the top value. |
| `LOAD(address)` | Load a word from memory and push it. |
| `STORE(address)` | Pop a word and store it at the checked address. |
| `JMP(target)` | Set the PC to a valid numeric instruction index. |
| `JZ(target)` | Pop a condition; jump when zero, otherwise advance. |
| `HALT` | Halt without changing the remaining machine state. |

Labels are not part of the runtime instruction language. If programs are
assembled from symbolic labels, an external assembler must resolve them to
numeric PC targets before execution. That assembler is outside the v1 formal
verification boundary.

## Installation and getting started

Install stable Rust and Cargo, then clone the repository:

```sh
git clone https://github.com/shahmeerkhaskhely8-bot/microverivm.git
cd microverivm
```

The crate exposes a Rust library; it does **not** currently provide a
standalone command-line executable. From the repository root, compile all
targets and run the unit and integration tests:

```sh
cargo check --locked --all-targets
cargo test --locked --all-targets
```

To build all configured targets:

```sh
cargo build --locked --all-targets
```

Example library use:

```rust
use microverivm::{
    error::Error,
    execute::step,
    instruction::Instruction,
    state::{State, Status},
};

fn run_example() -> Result<u32, Error> {
    let program = [
        Instruction::CONST(20),
        Instruction::CONST(22),
        Instruction::ADD,
        Instruction::HALT,
    ];
    let mut state = State::new();

    while state.status() == Status::Running {
        step(&mut state, &program)?;
    }

    state.stack().peek()
}
```

The public stepping API executes one instruction per call. A client can drive
execution by calling `step` until the status becomes `Halted` or an `Error` is
returned.

## Formal models and verification scope

There are two separate formal developments in this repository:

1. The legacy stack-machine Coq development defines a target semantics,
   RustLite evaluator, representation relation, and successful-step/trace
   forward simulation from the target model to RustLite.
2. The RV32I development under [`coq/RiscV/`](coq/RiscV/) defines a 32-bit
   word model, x0-safe register file, aligned PC, a typed decoder and selected
   instruction semantics, memory and execution invariants, trap and interrupt
   extensions, retirement/event traces, and application-level safety results.

The RV32I model accepts word-sized text and data segments from an external
loader; it does not parse ELF files or verify byte-level loading. It is not the
Rust stack VM. The `BisimulationRefinement.v` results concern a Rust-shaped
Coq model and its separate Rocq semantics. They do not prove that the Rust
source or compiled binary refines either formal model, and they do not relate
RV32I execution to the stack-machine instruction set.

The project gate checks for `Admitted`, `admit`, `Axiom`, and `Abort` tokens,
compiles 30 configured Coq modules, and validates their proof objects with
`coqchk`. The formal claims are limited to their stated definitions and
premises; kernel checking is not a proof of the Rust compiler, external
loader, or execution platform.

For details, see the [architecture guide](docs/ARCHITECTURE.md), the
[research paper](docs/WHITE-PAPER.md), and the [RV32I phase guides](docs/).

## Development and verification

Requirements:

- Stable Rust toolchain with Cargo.
- Rocq/Coq with `coqc` and `coqchk` available. The PowerShell gate checks
  common Windows install locations if `coqc` is not on `PATH`.
- PowerShell to run the repository's Coq scripts.

Rust checks:

```sh
cargo fmt --all -- --check
cargo check --locked --all-targets
cargo build --locked --all-targets
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked --all-targets
```

Run the complete local pipeline (sequential Coq compilation, placeholder
scan, `coqchk`, and Rust quality gates) from PowerShell:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\run-pipeline.ps1
```

To run only the Coq compile and kernel-validation gate:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\check-coq.ps1
```

On Windows, if a test executable cannot start because an MSVC runtime DLL is
missing, install the matching Visual C++ runtime. Alternatively, set
`RUSTFLAGS="-C target-feature=+crt-static"` for the test invocation; this is a
host linking option, not a change to VM memory management.

## Repository layout

```text
.
|-- rust/src/                 # no_std Rust stack VM library
|-- tests/                    # Rust integration tests
|-- coq/                      # stack VM models, proofs, and bridge
|   |-- RiscV/                # separate RV32I formal development
|   `-- Bridge/               # RustLite and target simulation proofs
|-- scripts/                  # PowerShell verification gates
|-- .github/workflows/        # Rust and Rocq CI workflows
|-- docs/                     # architecture, research, and phase documents
|-- Cargo.toml
|-- _CoqProject
`-- LICENSE-APACHE
```

## Contributing

Keep implementation, formal definitions, and tests aligned when behavior
changes. Add tests for boundary and error cases, close all Coq proofs without
admitted placeholders or project axioms, and run the Rust checks and Coq gate
before submitting changes.

## License

MicroVeriVM is distributed under the [Apache License, Version 2.0](LICENSE-APACHE).
