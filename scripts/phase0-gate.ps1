$ErrorActionPreference = 'Stop'
$root = Split-Path $PSScriptRoot -Parent
$library = Join-Path $root 'rust\src\lib.rs'

if (-not (Test-Path -LiteralPath $library)) {
    throw "Missing Rust library root: $library"
}

$source = Get-Content -LiteralPath $library -Raw
if ($source -notmatch '(?m)^#!\[no_std\]') {
    throw 'The Rust library must declare #![no_std].'
}
if ($source -notmatch '(?m)^#!\[forbid\(unsafe_code\)\]') {
    throw 'The Rust library must declare #![forbid(unsafe_code)].'
}

Push-Location $root
try {
    & cargo check --locked --all-targets
    if ($LASTEXITCODE -ne 0) {
        throw "cargo check failed with exit code $LASTEXITCODE"
    }
} finally {
    Pop-Location
}

Write-Host 'PHASE 0 GATE: PASS'
