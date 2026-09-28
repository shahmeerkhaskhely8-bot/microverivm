param(
    [string]$Compiler = 'coqc',
    [int]$TimeoutSeconds = 180
)

$ErrorActionPreference = 'Stop'
$root = Split-Path $PSScriptRoot -Parent
$logDir = Join-Path $root 'coq\build-check'
New-Item -ItemType Directory -Force -Path $logDir | Out-Null
$statusPath = Join-Path $logDir 'status.txt'
Set-Content -Path $statusPath -Value 'RUNNING' -Encoding UTF8

try {
    $compilerPath = (Get-Command $Compiler -ErrorAction Stop).Source
    Add-Content $statusPath "compiler=$compilerPath"
    $files = @('RustModel', 'Invariants', 'Syntax', 'Semantics', 'Proofs', 'Equivalence', 'Soundness', 'Extraction')
    foreach ($name in $files) {
        $stdout = Join-Path $logDir "$name.stdout.log"
        $stderr = Join-Path $logDir "$name.stderr.log"
        Add-Content $statusPath "START $name"
        $process = Start-Process -FilePath $compilerPath -WorkingDirectory $root `
            -ArgumentList @('-q', '-w', '+default', '-Q', 'coq', 'MicroVeriVM', "coq/$name.v") `
            -RedirectStandardOutput $stdout -RedirectStandardError $stderr -PassThru
        $processHandle = $process.Handle
        if (-not $process.WaitForExit($TimeoutSeconds * 1000)) {
            $process.Kill()
            $process.WaitForExit()
            throw "$name timed out after $TimeoutSeconds seconds"
        }
        $process.WaitForExit()
        $exitCode = $process.ExitCode
        Add-Content $statusPath "$name exit=$exitCode"
        if ($exitCode -ne 0) {
            throw "$name failed; see $stderr"
        }
        if ((Get-Item $stdout).Length -ne 0 -or (Get-Item $stderr).Length -ne 0) {
            throw "$name emitted diagnostics; inspect its logs"
        }
        $artifact = Join-Path $root "coq\$name.vo"
        if (-not (Test-Path -LiteralPath $artifact)) {
            throw "$name did not produce a .vo file"
        }
    }
    foreach ($artifact in @('microverivm.ml', 'microverivm.mli')) {
        if (-not (Test-Path -LiteralPath (Join-Path $root $artifact))) {
            throw "Missing extracted artifact: $artifact"
        }
    }
    Add-Content $statusPath 'PASS: all eight files compiled sequentially with empty diagnostic logs'
    Get-Content $statusPath
    exit 0
} catch {
    Add-Content $statusPath "FAIL: $($_.Exception.Message)"
    Write-Error $_
    exit 1
}