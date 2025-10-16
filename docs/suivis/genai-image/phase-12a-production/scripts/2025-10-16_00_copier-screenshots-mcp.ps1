# Script de copie des screenshots MCP Playwright vers docs
# Date: 2025-10-16
# Objectif: Récupérer les screenshots générés par MCP Playwright depuis le dossier temporaire

Write-Host "=== Copie des Screenshots MCP Playwright ===" -ForegroundColor Cyan

# Répertoire source (dossier temporaire MCP)
$tempBase = "$env:LOCALAPPDATA\Temp\playwright-mcp-output"
$destDir = "docs\genai-suivis\screenshots"

# Vérifier que le répertoire source existe
if (-not (Test-Path $tempBase)) {
    Write-Host "✗ Répertoire temporaire MCP introuvable: $tempBase" -ForegroundColor Red
    exit 1
}

# Créer le répertoire de destination si nécessaire
if (-not (Test-Path $destDir)) {
    New-Item -ItemType Directory -Path $destDir -Force | Out-Null
    Write-Host "✓ Répertoire de destination créé: $destDir" -ForegroundColor Green
} else {
    Write-Host "✓ Répertoire de destination existe: $destDir" -ForegroundColor Green
}

# Chercher tous les PNG dans les sous-dossiers temporaires MCP
$files = Get-ChildItem -Path $tempBase -Recurse -Filter "*.png" -File
if ($files.Count -eq 0) {
    Write-Host "⚠ Aucun fichier PNG trouvé dans $tempBase" -ForegroundColor Yellow
    exit 0
}

Write-Host "`nCopie de $($files.Count) fichier(s) MCP..." -ForegroundColor Yellow
foreach ($file in $files) {
    # Extraire le nom de fichier d'origine depuis le chemin
    $filename = $file.Name
    $destPath = Join-Path $destDir $filename
    
    Copy-Item -Path $file.FullName -Destination $destPath -Force
    $sizeKB = [math]::Round($file.Length / 1KB, 2)
    Write-Host "  ✓ $filename ($sizeKB KB)" -ForegroundColor Green
}

# Afficher le contenu final
Write-Host "`n=== Screenshots MCP archivés dans: $destDir ===" -ForegroundColor Cyan
Get-ChildItem -Path $destDir -Filter "*-mcp.png" | 
    Select-Object Name, @{Name='Taille (KB)';Expression={[math]::Round($_.Length/1KB,2)}}, LastWriteTime |
    Format-Table -AutoSize

Write-Host "✅ Copie MCP terminée avec succès" -ForegroundColor Green