#!/usr/bin/env powershell
# MicroVeriVM High-Assurance Verification Pipeline
# This script performs a clean, end-to-end verification of all components.

param(
    [string]$Root = "C:\Users\HARRY POTTER\Microverivm",
    [string]$Coqc = "C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe"
)

$ErrorActionPreference = "Stop"
$statusPath = Join-Path $Root "pipeline-status.txt"
$success = $true

# Remove old status
Remove-Item $statusPath -ErrorAction SilentlyContinue

# Step 1: Clean all stale artifacts
Add-Content $statusPath "=== STEP 1: Clean stale artifacts ==="
$voFiles = Get-ChildItem (Join-Path $Root "coq") -Filter "*.vo" -ErrorAction SilentlyContinue
$globFiles = Get-ChildItem (Join-Path $Root "coq") -Filter "*.glob" -ErrorAction SilentlyContinue
$totalCleaned = 0
foreach ($f in $voFiles) { Remove-Item $f.FullName -ErrorAction SilentlyContinue; $totalCleaned++ }
foreach ($f in $globFiles) { Remove-Item $f.FullName -ErrorAction SilentlyContinue; $totalCleaned++ }
Add-Content $statusPath "Cleaned $totalCleaned artifacts"

# Step 2: Compile Coq files sequentially
$coqFiles = @("Syntax", "Semantics", "Proofs", "Equivalence", "Soundness", "Extraction")
foreach ($name in $coqFiles) {
    Add-Content $statusPath "Compiling $name.v..."
    $voPath = Join-Path $Root "coq\$name.vo"
    Remove-Item $voPath -ErrorAction SilentlyContinue
    & $Coqc -q -w @all -R . MicroVeriVM (Join-Path $Root "coq\$name.v") 2>&1 | Out-File (Join-Path $Root "coq\$name-coqc.log") -Append
    $exitCode = $LASTEXITCODE
    Add-Content $statusPath "$name exit=$exitCode"
    if ($exitCode -ne 0) {
        Add-Content $statusPath "FAILED: $name.v"
        $success = $false
        break
    }
    if (-not (Test-Path $voPath)) {
        Add-Content $statusPath "FAILED: $name.v produced no .vo"
        $success = $false
        break
    }
}

# Step 3: Verify extraction artifact
Add-Content $statusPath "=== Checking extraction artifact ==="
$mlPath = Join-Path $Root "microverivm.ml"
if (Test-Path $mlPath) {
    Add-Content $statusPath "microverivm.ml exists"
    $mlSize = (Get-Item $mlPath).Length
    Add-Content $statusPath "microverivm.ml size=$mlSize bytes"
} else {
    Add-Content $statusPath "WARNING: microverivm.ml not found"
}

# Step 4: Rust verification
Add-Content $statusPath "=== Rust verification ==="
Set-Location $Root
$cargoClean = & cargo clean 2>&1
Add-Content $statusPath "cargo clean exit=$LASTEXITCODE"
$cargoTest = & cargo test --all-targets 2>&1
Add-Content $statusPath "cargo test exit=$LASTEXITCODE"
if ($LASTEXITCODE -ne 0) {
    Add-Content $statusPath "FAILED: cargo test"
    $success = $false
}

# Step 5: Final status
Add-Content $statusPath "=== FINAL STATUS ==="
if ($success) {
    Add-Content $statusPath "PASS: All verification steps completed successfully"
    Add-Content $statusPath "EXIT=0"
} else {
    Add-Content $statusPath "FAIL: Some verification steps failed"
    Add-Content $statusPath "EXIT=1"
}

Write-Output "Pipeline complete. See $statusPath for details."