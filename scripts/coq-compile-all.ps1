param(
    [string]$Compiler = 'coqc',
    [int]$TimeoutSeconds = 180
)

$ErrorActionPreference = 'Stop'
$gate = Join-Path $PSScriptRoot 'check-coq.ps1'
$arguments = @(
    '-NoProfile',
    '-ExecutionPolicy', 'Bypass',
    '-File', "`"$gate`"",
    '-Compiler', "`"$Compiler`"",
    '-TimeoutSeconds', "$TimeoutSeconds"
)
$process = Start-Process -FilePath 'powershell.exe' -ArgumentList $arguments `
    -NoNewWindow -Wait -PassThru
if ($process.ExitCode -ne 0) {
    exit $process.ExitCode
}
