# PowerShell script to register WSL OpenSpiel kernel for Jupyter
# Run this after setup_wsl_openspiel.sh in WSL

$ErrorActionPreference = "Stop"

Write-Host "=== WSL Kernel Registration for Windows ===" -ForegroundColor Cyan
Write-Host ""

# Check WSL is available
Write-Host "[1/4] Checking WSL..." -ForegroundColor Yellow
$wslStatus = wsl -l -v 2>$null
if (-not $?) {
    Write-Host "ERROR: WSL is not installed or not running" -ForegroundColor Red
    exit 1
}

# Get WSL username
Write-Host "[2/4] Getting WSL username..." -ForegroundColor Yellow
$wslUser = (wsl -d Ubuntu whoami).Trim()
Write-Host "  WSL user: $wslUser"

# Verify wrapper exists in WSL
Write-Host "[3/4] Verifying WSL setup..." -ForegroundColor Yellow
$wrapperCheck = wsl -d Ubuntu -- bash -c "test -f /home/$wslUser/.gametheory-kernel-wrapper.sh && echo OK"
if ($wrapperCheck -ne "OK") {
    Write-Host "ERROR: Wrapper script not found. Run setup_wsl_openspiel.sh in WSL first." -ForegroundColor Red
    exit 1
}

# Verify OpenSpiel
$openspielCheck = wsl -d Ubuntu -- bash -c "source ~/.gametheory-venv/bin/activate && python3 -c 'import pyspiel; print(len(pyspiel.registered_names()))' 2>/dev/null"
Write-Host "  OpenSpiel games available: $openspielCheck"

# Create kernel directory
Write-Host "[4/4] Creating kernel configuration..." -ForegroundColor Yellow
$kernelPath = "$env:APPDATA\jupyter\kernels\gametheory-wsl"
New-Item -ItemType Directory -Force -Path $kernelPath | Out-Null

# Create kernel.json
$kernelJson = @"
{
  "argv": [
    "wsl.exe", "-d", "Ubuntu", "--",
    "bash", "/home/$wslUser/.gametheory-kernel-wrapper.sh",
    "-f", "{connection_file}"
  ],
  "display_name": "Python (GameTheory WSL + OpenSpiel)",
  "language": "python"
}
"@

$kernelJson | Out-File -Encoding utf8 "$kernelPath\kernel.json"
Write-Host "  Created: $kernelPath\kernel.json"

# Verify installation
Write-Host ""
Write-Host "=== Installation Complete ===" -ForegroundColor Green
Write-Host ""
Write-Host "Installed kernels:"
jupyter kernelspec list

Write-Host ""
Write-Host "Next steps:" -ForegroundColor Cyan
Write-Host "  1. Restart VSCode completely"
Write-Host "  2. Open a GameTheory notebook (7, 12, or 15)"
Write-Host "  3. Select kernel: 'Python (GameTheory WSL + OpenSpiel)'"
Write-Host ""
