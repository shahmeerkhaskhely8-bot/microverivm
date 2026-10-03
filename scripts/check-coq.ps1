param(
    [string]$Compiler = 'coqc',
    [int]$TimeoutSeconds = 600
)

$ErrorActionPreference = 'Stop'
$root = Split-Path $PSScriptRoot -Parent
$logDir = Join-Path $root 'coq\build-check'
New-Item -ItemType Directory -Force -Path $logDir | Out-Null
$statusPath = Join-Path $logDir 'status.txt'
Set-Content -Path $statusPath -Value 'RUNNING' -Encoding UTF8

try {
    $compilerCandidates = @($Compiler)
    if ($Compiler -eq 'coqc') {
        $compilerCandidates += @(
            'C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe',
            'C:\Rocq-Platform\bin\coqc.exe',
            'C:\Program Files\Rocq\bin\coqc.exe',
            'C:\Program Files (x86)\Rocq\bin\coqc.exe'
        )
    }
    $compilerPath = $null
    foreach ($candidate in $compilerCandidates) {
        try {
            $compilerPath = (Get-Command $candidate -ErrorAction Stop).Source
            break
        } catch {
            if (Test-Path -LiteralPath $candidate) {
                $compilerPath = $candidate
                break
            }
        }
    }
    if (-not $compilerPath) {
        throw "Unable to locate coqc; pass -Compiler <path-to-coqc> or install Rocq."
    }
    $compilerDirectory = Split-Path -Parent $compilerPath
    $env:PATH = "$compilerDirectory;$env:PATH"
    Add-Content $statusPath "compiler=$compilerPath"
    $sourceFiles = Get-ChildItem -Path (Join-Path $root 'coq') -Filter '*.v' -Recurse
    $placeholderMatches = Select-String -Path $sourceFiles.FullName `
        -Pattern '\b(Admitted|admit|Axiom|Abort)\b'
    if ($placeholderMatches) {
        throw "Proof placeholders found: $($placeholderMatches -join '; ')"
    }
    Add-Content $statusPath 'PASS: no Admitted/admit/Axiom/Abort tokens found in Coq sources'
    $files = @('RustModel', 'RiscV/Word', 'RiscV/RegisterFile', 'RiscV/Machine', 'RiscV/Instruction', 'RiscV/Decoder', 'RiscV/Semantics', 'RiscV/MemorySafety', 'RiscV/Execution', 'RiscV/TrapHandling', 'RiscV/SystemIntegration', 'RiscV/PrivilegedCSR', 'RiscV/Interrupts', 'RiscV/RetirementTrace', 'RiscV/ApplicationExecution', 'Invariants', 'Correspondence', 'Syntax', 'Semantics', 'Proofs', 'Equivalence', 'Soundness', 'CanonicalAST', 'TargetAST', 'Bridge/RustLite', 'Bridge/Simulation', 'Bridge/TraceEquiv', 'Extraction', 'RiscV/BisimulationRefinement', 'RiscV/SystemInvariants')
    foreach ($name in $files) {
        $logName = $name -replace '[/\\]', '-'
        $stdout = Join-Path $logDir "$logName.stdout.log"
        $stderr = Join-Path $logDir "$logName.stderr.log"
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
    $checkerPath = Join-Path $compilerDirectory 'coqchk.exe'
    if (-not (Test-Path -LiteralPath $checkerPath)) {
        throw "Missing kernel checker: $checkerPath"
    }
    $checkerStdout = Join-Path $logDir 'coqchk.stdout.log'
    $checkerStderr = Join-Path $logDir 'coqchk.stderr.log'
    $checkerModules = @(
        'MicroVeriVM.RustModel',
        'MicroVeriVM.RiscV.Word',
        'MicroVeriVM.RiscV.RegisterFile',
        'MicroVeriVM.RiscV.Machine',
        'MicroVeriVM.RiscV.Instruction',
        'MicroVeriVM.RiscV.Decoder',
        'MicroVeriVM.RiscV.Semantics',
        'MicroVeriVM.RiscV.MemorySafety',
        'MicroVeriVM.RiscV.Execution',
        'MicroVeriVM.RiscV.TrapHandling',
        'MicroVeriVM.RiscV.SystemIntegration',
        'MicroVeriVM.RiscV.PrivilegedCSR',
        'MicroVeriVM.RiscV.Interrupts',
        'MicroVeriVM.RiscV.RetirementTrace',
        'MicroVeriVM.RiscV.ApplicationExecution',
        'MicroVeriVM.Invariants',
        'MicroVeriVM.Correspondence',
        'MicroVeriVM.Syntax',
        'MicroVeriVM.Semantics',
        'MicroVeriVM.Proofs',
        'MicroVeriVM.Equivalence',
        'MicroVeriVM.Soundness',
        'MicroVeriVM.CanonicalAST',
        'MicroVeriVM.TargetAST',
        'MicroVeriVM.Bridge.RustLite',
        'MicroVeriVM.Bridge.Simulation',
        'MicroVeriVM.Bridge.TraceEquiv',
        'MicroVeriVM.Extraction',
        'MicroVeriVM.RiscV.BisimulationRefinement',
        'MicroVeriVM.RiscV.SystemInvariants'
    )
    $checker = Start-Process -FilePath $checkerPath -WorkingDirectory $root `
        -ArgumentList (@('-Q', 'coq', 'MicroVeriVM') + $checkerModules) `
        -RedirectStandardOutput $checkerStdout -RedirectStandardError $checkerStderr -PassThru
    $checkerHandle = $checker.Handle
    if (-not $checker.WaitForExit($TimeoutSeconds * 1000)) {
        $checker.Kill()
        $checker.WaitForExit()
        throw "coqchk timed out after $TimeoutSeconds seconds"
    }
    $checker.WaitForExit()
    if ($checker.ExitCode -ne 0) {
        throw "coqchk failed; see $checkerStderr"
    }
    $checkerSucceeded = Select-String -Path $checkerStdout, $checkerStderr `
        -Pattern 'Modules were successfully checked' -Quiet
    if (-not $checkerSucceeded) {
        throw 'coqchk exited successfully without reporting that modules were checked'
    }
    Add-Content $statusPath 'PASS: all thirty files compiled sequentially; coqchk validated all thirty modules'
    Get-Content $statusPath
    exit 0
} catch {
    Add-Content $statusPath "FAIL: $($_.Exception.Message)"
    Write-Error $_
    exit 1
}