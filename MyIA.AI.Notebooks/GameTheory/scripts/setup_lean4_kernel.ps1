# PowerShell script to create the Lean 4 WSL kernel for Jupyter
# Run this AFTER running setup_wsl_lean4.sh in WSL
#
# Usage: .\setup_lean4_kernel.ps1

Write-Host "=============================================="
Write-Host "   CONFIGURATION DU KERNEL LEAN 4 (WSL)"
Write-Host "=============================================="
Write-Host ""

# Get WSL username
$wslUser = (wsl -d Ubuntu whoami).Trim()
Write-Host "[INFO] Utilisateur WSL: $wslUser"

# Check if Lean is available in WSL
Write-Host "[INFO] Verification de Lean dans WSL..."
$leanVersion = wsl -d Ubuntu -- bash -c "source ~/.elan/env && lean --version 2>/dev/null"
if ($LASTEXITCODE -ne 0) {
    Write-Host "[ERROR] Lean n'est pas installe dans WSL." -ForegroundColor Red
    Write-Host "        Executez d'abord dans WSL:"
    Write-Host "        cd /mnt/c/dev/CoursIA/MyIA.AI.Notebooks/GameTheory/scripts"
    Write-Host "        bash setup_wsl_lean4.sh"
    exit 1
}
Write-Host "[OK] $leanVersion" -ForegroundColor Green

# Check if wrapper exists
Write-Host "[INFO] Verification du wrapper..."
$wrapperExists = wsl -d Ubuntu -- test -f "/home/$wslUser/.lean4-kernel-wrapper.py" `&`& echo "OK"
if ($wrapperExists -ne "OK") {
    Write-Host "[ERROR] Wrapper non trouve. Executez setup_wsl_lean4.sh dans WSL." -ForegroundColor Red
    exit 1
}
Write-Host "[OK] Wrapper trouve" -ForegroundColor Green

# Create kernel directory
$kernelPath = "$env:APPDATA\jupyter\kernels\lean4-wsl"
Write-Host "[INFO] Creation du repertoire: $kernelPath"
New-Item -ItemType Directory -Force -Path $kernelPath | Out-Null

# Create kernel.json
$kernelJson = @"
{
  "argv": [
    "wsl.exe", "-d", "Ubuntu", "--",
    "/home/$wslUser/.lean4-venv/bin/python3",
    "/home/$wslUser/.lean4-kernel-wrapper.py",
    "-f", "{connection_file}"
  ],
  "display_name": "Lean 4 (WSL)",
  "language": "lean4"
}
"@

$kernelFile = "$kernelPath\kernel.json"
$kernelJson | Out-File -Encoding utf8 $kernelFile
Write-Host "[OK] Kernel cree: $kernelFile" -ForegroundColor Green

# Verify kernel registration
Write-Host ""
Write-Host "[INFO] Verification de l'enregistrement..."
jupyter kernelspec list | Select-String -Pattern "lean4"

Write-Host ""
Write-Host "=============================================="
Write-Host "   CONFIGURATION TERMINEE !" -ForegroundColor Green
Write-Host "=============================================="
Write-Host ""
Write-Host "Etapes suivantes:"
Write-Host "  1. Redemarrez completement VSCode"
Write-Host "  2. Ouvrez un notebook Lean (GameTheory-16, 19)"
Write-Host "  3. Selectionnez le kernel 'Lean 4 (WSL)'"
Write-Host ""
Write-Host "En cas de probleme, verifiez les logs:"
Write-Host "  wsl -d Ubuntu -- cat ~/.lean4-wrapper.log"
Write-Host ""
