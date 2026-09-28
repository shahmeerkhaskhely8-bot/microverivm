$ErrorActionPreference = 'Stop'

Write-Host 'Phase 0 gate: checking repository structure'
$required = @(
    'Cargo.toml',
    'rust/src/lib.rs',
    'coq',
    'tests',
    'scripts',
    'docs',
    'Makefile'
)
foreach ($path in $required) {
    if (-not (Test-Path $path)) {
        throw "Missing required Phase 0 path: $path"
    }
}

Write-Host 'Phase 0 gate: checking Rust constraints'
$lib = Get-Content 'rust/src/lib.rs' -Raw
if ($lib -notmatch '(?m)^#!\[no_std\]') { throw 'Missing #![no_std]' }
if ($lib -notmatch '(?m)^#!\[forbid\(unsafe_code\)\]') { throw 'Missing #![forbid(unsafe_code)]' }

$body = ($lib -split "`r?`n" | Where-Object {
    $_ -notmatch '^\s*#!' -and $_ -notmatch '^\s*//!?' -and $_ -notmatch '^\s*$'
}) -join "`n"
if ($body -match '\b(unsafe|alloc|Vec|Box|String|HashMap)\b') { throw 'Heap or unsafe-related token found in library body' }

Write-Host 'Phase 0 gate: checking absence of VM logic'
if ($body -match '(?i)interpreter|opcode|instruction|execute|virtual machine|vm state') {
    throw 'VM logic marker found in Phase 0 library'
}

Write-Host 'Phase 0 gate: cargo check'
cargo check --locked

Write-Host 'PHASE 0 GATE: PASS'
