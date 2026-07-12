# Setup WSL Jupyter kernel for SmartContracts notebooks
# Run this in PowerShell on Windows AFTER running setup_wsl_smartcontracts.sh in WSL

$ErrorActionPreference = "Stop"

Write-Host "============================================================" -ForegroundColor Cyan
Write-Host "SmartContracts WSL Kernel Registration"
Write-Host "============================================================"
Write-Host ""

# Get WSL username
$wslUser = (wsl -d Ubuntu -- whoami).Trim()
Write-Host "WSL user: $wslUser"

# Verify wrapper exists
$wrapperCheck = wsl -d Ubuntu -- test -f "/home/$wslUser/.smartcontracts-kernel-wrapper.sh" "&&" echo "ok"
if ($wrapperCheck.Trim() -ne "ok") {
    Write-Host "ERROR: Wrapper script not found in WSL." -ForegroundColor Red
    Write-Host "Run setup_wsl_smartcontracts.sh in WSL first:"
    Write-Host "  wsl -d Ubuntu -- bash $(wsl -d Ubuntu -- wslpath -a '$PSScriptRoot/setup_wsl_smartcontracts.sh')"
    exit 1
}
Write-Host "Wrapper script found." -ForegroundColor Green

# Verify Foundry
$forgeCheck = wsl -d Ubuntu -- bash -c "source /home/$wslUser/.bashrc 2>/dev/null; /home/$wslUser/.foundry/bin/forge --version 2>/dev/null || echo MISSING"
if ($forgeCheck -match "MISSING") {
    Write-Host "WARNING: Foundry (forge) not found in WSL." -ForegroundColor Yellow
    Write-Host "Foundry may need to be installed separately."
} else {
    Write-Host "Foundry: $($forgeCheck.Trim())" -ForegroundColor Green
}

# Create kernel directory
$kernelPath = Join-Path $env:APPDATA "jupyter\kernels\smartcontracts-wsl"
if (-not (Test-Path $kernelPath)) {
    New-Item -ItemType Directory -Force -Path $kernelPath | Out-Null
}

# Create kernel.json
$kernelJson = @{
    argv = @(
        "wsl.exe", "-d", "Ubuntu", "--",
        "bash", "/home/$wslUser/.smartcontracts-kernel-wrapper.sh",
        "-f", "{connection_file}"
    )
    display_name = "Python (SmartContracts WSL + Foundry)"
    language = "python"
    metadata = @{
        debugger = $false
    }
} | ConvertTo-Json -Depth 3

# Write without BOM (critical for JSON)
$kernelJsonPath = Join-Path $kernelPath "kernel.json"
[System.IO.File]::WriteAllText($kernelJsonPath, $kernelJson, [System.Text.UTF8Encoding]::new($false))

Write-Host ""
Write-Host "Kernel registered at: $kernelJsonPath" -ForegroundColor Green
Write-Host ""
Write-Host "Content:"
Get-Content $kernelJsonPath
Write-Host ""

# Verify kernel is listed
Write-Host "Verifying kernel registration..."
$kernels = jupyter kernelspec list 2>&1
if ($kernels -match "smartcontracts-wsl") {
    Write-Host "Kernel 'smartcontracts-wsl' registered successfully!" -ForegroundColor Green
} else {
    Write-Host "WARNING: Kernel may not be visible. Check: jupyter kernelspec list" -ForegroundColor Yellow
}

Write-Host ""
Write-Host "============================================================"
Write-Host "Done! You can now use the kernel:"
Write-Host "  1. Open a SmartContracts notebook in VS Code"
Write-Host "  2. Select kernel: 'Python (SmartContracts WSL + Foundry)'"
Write-Host "  3. Anvil will be available via WSL"
Write-Host ""
Write-Host "To start anvil separately:"
Write-Host "  wsl -d Ubuntu -- bash -c '/home/$wslUser/.foundry/bin/anvil'"
Write-Host "============================================================"
