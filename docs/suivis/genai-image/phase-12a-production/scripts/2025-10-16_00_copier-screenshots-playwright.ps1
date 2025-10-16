# Script de copie des screenshots Playwright vers docs
# Date: 2025-10-16
# Objectif: Archiver les screenshots générés par les tests automatisés

Write-Host "=== Copie des Screenshots Playwright ===" -ForegroundColor Cyan

# Répertoires source et destination
$sourceDir = "D:\Production\playwright-tests\results"
$destDir = "docs\genai-suivis\screenshots"

# Vérifier que le répertoire source existe
if (-not (Test-Path $sourceDir)) {
    Write-Host "✗ Répertoire source introuvable: $sourceDir" -ForegroundColor Red
    exit 1
}

# Créer le répertoire de destination si nécessaire
if (-not (Test-Path $destDir)) {
    New-Item -ItemType Directory -Path $destDir -Force | Out-Null
    Write-Host "✓ Répertoire de destination créé: $destDir" -ForegroundColor Green
} else {
    Write-Host "✓ Répertoire de destination existe: $destDir" -ForegroundColor Green
}

# Copier les fichiers PNG
$files = Get-ChildItem -Path $sourceDir -Filter "*.png"
if ($files.Count -eq 0) {
    Write-Host "⚠ Aucun fichier PNG trouvé dans $sourceDir" -ForegroundColor Yellow
    exit 0
}

Write-Host "`nCopie de $($files.Count) fichier(s)..." -ForegroundColor Yellow
foreach ($file in $files) {
    Copy-Item -Path $file.FullName -Destination $destDir -Force
    $sizeKB = [math]::Round($file.Length / 1KB, 2)
    Write-Host "  ✓ $($file.Name) ($sizeKB KB)" -ForegroundColor Green
}

# Afficher le contenu final
Write-Host "`n=== Screenshots archivés dans: $destDir ===" -ForegroundColor Cyan
Get-ChildItem -Path $destDir -Filter "*.png" | 
    Select-Object Name, @{Name='Taille (KB)';Expression={[math]::Round($_.Length/1KB,2)}}, LastWriteTime |
    Format-Table -AutoSize

Write-Host "✅ Copie terminée avec succès" -ForegroundColor Green