param(
    [string]$Coqc = 'C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe',
    [string]$Root = 'C:\Users\HARRY POTTER\Microverivm'
)

$ErrorActionPreference = 'Stop'
$files = @('RustModel', 'Invariants', 'Correspondence', 'Syntax', 'Semantics', 'Proofs', 'Equivalence', 'Soundness', 'Extraction')
$statusPath = Join-Path $Root 'coq\compile-status.log'
$overallExit = 0

Set-Content -Path $statusPath -Value "BUILD_START $(Get-Date)" -Encoding UTF8

foreach ($name in $files) {
    $vo = Join-Path $Root "coq\$name.vo"
    $log = Join-Path $Root "coq\$name.compile.log"
    $stdoutLog = Join-Path $Root "coq\$name.stdout.log"
    $stderrLog = Join-Path $Root "coq\$name.stderr.log"
    Remove-Item $vo -ErrorAction SilentlyContinue
    Remove-Item $log -ErrorAction SilentlyContinue
    Remove-Item $stdoutLog -ErrorAction SilentlyContinue
    Remove-Item $stderrLog -ErrorAction SilentlyContinue

    $proc = Start-Process -FilePath $Coqc -WorkingDirectory $Root `
        -ArgumentList @('-q', '-w', '-@all', '-R', 'coq', 'MicroVeriVM', "coq\$name.v") `
        -RedirectStandardOutput $stdoutLog -RedirectStandardError $stderrLog -PassThru
    $proc.WaitForExit()
    $code = $proc.ExitCode
    Add-Content $statusPath "$name exit=$code"
    Add-Content $log "EXIT=$code"

    if ($code -ne 0) {
        $overallExit = 1
        Add-Content $statusPath "FAIL at $name"
        break
    }
    if (-not (Test-Path $vo)) {
        $overallExit = 1
        Add-Content $statusPath "FAIL: $name produced no .vo"
        break
    }
    if ((Get-Item $stdoutLog).Length -gt 0 -or (Get-Item $stderrLog).Length -gt 0) {
        $overallExit = 1
        Add-Content $statusPath "FAIL: $name emitted diagnostics"
        break
    }
}

Add-Content $statusPath "BUILD_EXIT=$overallExit"
Write-Output "OVERALL_EXIT=$overallExit"
exit $overallExit