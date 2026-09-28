.PHONY: phase0 check test clean

phase0: check
	@powershell -NoProfile -ExecutionPolicy Bypass -File scripts/phase0-gate.ps1

check:
	@cargo check --locked

test:
	@cargo test --locked

clean:
	@cargo clean
