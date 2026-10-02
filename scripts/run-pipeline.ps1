param(
    [string]$Compiler = 'coqc',
    [int]$TimeoutSeconds = 180
)

$ErrorActionPreference = 'Stop'
$root = Split-Path $PSScriptRoot -Parent
$gate = Join-Path $PSScriptRoot 'check-coq.ps1'
$gateArguments = @(
    '-NoProfile',
    '-ExecutionPolicy', 'Bypass',
    '-File', "`"$gate`"",
    '-Compiler', "`"$Compiler`"",
    '-TimeoutSeconds', "$TimeoutSeconds"
)

Write-Host 'Running Coq compile and kernel-check gate'
$coq = Start-Process -FilePath 'powershell.exe' -ArgumentList $gateArguments `
    -NoNewWindow -Wait -PassThru
if ($coq.ExitCode -ne 0) {
    throw "Coq verification failed with exit code $($coq.ExitCode)"
}

Push-Location $root
try {
    $commands = @(
        @{ Name = 'cargo fmt'; Args = @('fmt', '--all', '--', '--check') },
        @{ Name = 'cargo check'; Args = @('check', '--locked', '--all-targets') },
        @{ Name = 'cargo test'; Args = @('test', '--locked', '--all-targets') },
        @{ Name = 'cargo clippy'; Args = @('clippy', '--locked', '--all-targets', '--', '-D', 'warnings') }
    )
    foreach ($command in $commands) {
        Write-Host "Running $($command.Name)"
        $cargoArgs = $command.Args
        & cargo @cargoArgs
        if ($LASTEXITCODE -ne 0) {
            throw "$($command.Name) failed with exit code $LASTEXITCODE"
        }
    }
} finally {
    Pop-Location
}

Write-Host 'VERIFICATION PIPELINE: PASS'
