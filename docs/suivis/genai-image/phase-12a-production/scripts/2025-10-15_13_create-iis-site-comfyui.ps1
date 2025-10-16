# Script de création du site IIS pour ComfyUI + Qwen
# Doit être exécuté avec des privilèges Administrateur
# Date: 2025-10-15

$siteName = "qwen-image-edit.myia.io"
$physicalPath = "D:\Production\qwen-image-edit.myia.io"
$hostHeader = "qwen-image-edit.myia.io"

Write-Host "=== Création du site IIS pour ComfyUI + Qwen ===" -ForegroundColor Cyan

# Vérifier les privilèges administrateur
$isAdmin = ([Security.Principal.WindowsPrincipal] [Security.Principal.WindowsIdentity]::GetCurrent()).IsInRole([Security.Principal.WindowsBuiltInRole]::Administrator)
if (-not $isAdmin) {
    Write-Host "ERREUR: Ce script nécessite des privilèges administrateur!" -ForegroundColor Red
    Write-Host "Relancez PowerShell en tant qu'administrateur" -ForegroundColor Yellow
    exit 1
}

# Importer le module WebAdministration
Import-Module WebAdministration -ErrorAction Stop

# Vérifier si le site existe déjà
if (Get-Website -Name $siteName -ErrorAction SilentlyContinue) {
    Write-Host "Le site '$siteName' existe déjà" -ForegroundColor Yellow
    Write-Host "Suppression du site existant..." -ForegroundColor Yellow
    Remove-Website -Name $siteName
}

# Créer le site IIS
Write-Host "Création du site IIS: $siteName" -ForegroundColor Green
New-Website -Name $siteName `
    -PhysicalPath $physicalPath `
    -HostHeader $hostHeader `
    -Port 80 `
    -Force

# Ajouter le binding HTTPS (port 443) sans certificat pour l'instant
Write-Host "Ajout du binding HTTPS (port 443)..." -ForegroundColor Green
New-WebBinding -Name $siteName `
    -Protocol https `
    -Port 443 `
    -HostHeader $hostHeader `
    -SslFlags 1

# Démarrer le site
Write-Host "Démarrage du site..." -ForegroundColor Green
Start-Website -Name $siteName

# Afficher l'état du site
Write-Host "`n=== État du site ===" -ForegroundColor Cyan
Get-Website -Name $siteName | Format-List Name, State, PhysicalPath, Bindings

Write-Host "`n✓ Site IIS créé avec succès!" -ForegroundColor Green
Write-Host "  - HTTP:  http://$hostHeader (port 80)" -ForegroundColor White
Write-Host "  - HTTPS: https://$hostHeader (port 443, certificat à configurer)" -ForegroundColor White
Write-Host "`nProchaine étape: Configurer le certificat SSL avec win-acme" -ForegroundColor Yellow