#!/usr/bin/env powershell
# Script de déplacement et renommage des screenshots Playwright
# Auteur: Roo Code Assistant
# Date: 2025-09-08

Write-Host "=== SCRIPT DE DÉPLACEMENT DES SCREENSHOTS ===" -ForegroundColor Green
Write-Host ""

# Définir le répertoire de destination
$destDir = "screenshots\"

# Vérifier que le répertoire de destination existe
if (-not (Test-Path $destDir)) {
    Write-Host "Création du répertoire de destination..." -ForegroundColor Yellow
    New-Item -ItemType Directory -Path $destDir -Force
}

# Définir les mappings de fichiers source vers destination
$fileMappings = @{
    "C:\Users\jsboi\AppData\Local\Temp\playwright-mcp-output\2025-09-08T20-18-23.897Z\01-hero-desktop.png" = "01-hero-desktop.png"
    "C:\Users\jsboi\AppData\Local\Temp\playwright-mcp-output\2025-09-08T20-26-36.218Z\02-services-desktop.png" = "02-services-desktop.png"
    "C:\Users\jsboi\AppData\Local\Temp\playwright-mcp-output\2025-09-08T20-56-02.328Z\ateliers-demo-roo-code-workspaces-test-user-4-creation-contenu-demo-1-web-screenshots-03-expertise-desktop.png" = "03-expertise-desktop.png"
    "C:\Users\jsboi\AppData\Local\Temp\playwright-mcp-output\2025-09-08T20-46-47.703Z\ateliers-demo-roo-code-workspaces-test-user-4-creation-contenu-demo-1-web-screenshots-04-apropos-desktop.png" = "04-apropos-desktop.png"
    "C:\Users\jsboi\AppData\Local\Temp\playwright-mcp-output\2025-09-08T20-47-24.025Z\ateliers-demo-roo-code-workspaces-test-user-4-creation-contenu-demo-1-web-screenshots-05-contact-desktop.png" = "05-contact-desktop.png"
    "C:\Users\jsboi\AppData\Local\Temp\playwright-mcp-output\2025-09-08T20-48-10.105Z\ateliers-demo-roo-code-workspaces-test-user-4-creation-contenu-demo-1-web-screenshots-06-hero-mobile.png" = "06-hero-mobile.png"
    "C:\Users\jsboi\AppData\Local\Temp\playwright-mcp-output\2025-09-08T20-48-53.126Z\ateliers-demo-roo-code-workspaces-test-user-4-creation-contenu-demo-1-web-screenshots-07-services-mobile.png" = "07-services-mobile.png"
    "C:\Users\jsboi\AppData\Local\Temp\playwright-mcp-output\2025-09-08T20-49-33.809Z\ateliers-demo-roo-code-workspaces-test-user-4-creation-contenu-demo-1-web-screenshots-08-contact-mobile.png" = "08-contact-mobile.png"
    "C:\Users\jsboi\AppData\Local\Temp\playwright-mcp-output\2025-09-08T20-50-28.162Z\ateliers-demo-roo-code-workspaces-test-user-4-creation-contenu-demo-1-web-screenshots-09-tablet.png" = "09-tablet.png"
}

Write-Host "Début de la copie des screenshots..." -ForegroundColor Cyan
Write-Host ""

$successCount = 0
$errorCount = 0

foreach ($mapping in $fileMappings.GetEnumerator()) {
    $sourceFile = $mapping.Key
    $destFileName = $mapping.Value
    $destFile = Join-Path $destDir $destFileName
    
    Write-Host "Traitement: $destFileName" -ForegroundColor White
    
    if (Test-Path $sourceFile) {
        try {
            Copy-Item -Path $sourceFile -Destination $destFile -Force
            Write-Host "  ✓ Copié avec succès" -ForegroundColor Green
            $successCount++
        }
        catch {
            Write-Host "  ✗ Erreur lors de la copie: $($_.Exception.Message)" -ForegroundColor Red
            $errorCount++
        }
    } else {
        Write-Host "  ✗ Fichier source introuvable" -ForegroundColor Red
        $errorCount++
    }
    Write-Host ""
}

Write-Host "=== RÉSUMÉ ===" -ForegroundColor Green
Write-Host "Fichiers copiés avec succès: $successCount" -ForegroundColor Green
Write-Host "Erreurs: $errorCount" -ForegroundColor $(if ($errorCount -gt 0) { "Red" } else { "Green" })
Write-Host ""

Write-Host "Vérification du contenu du dossier screenshots:" -ForegroundColor Cyan
if (Test-Path $destDir) {
    $files = Get-ChildItem -Path $destDir | Sort-Object Name
    foreach ($file in $files) {
        $sizeKB = [math]::Round($file.Length / 1KB, 2)
        Write-Host "  📷 $($file.Name) ($sizeKB KB)" -ForegroundColor White
    }
    Write-Host ""
    Write-Host "Total: $($files.Count) fichiers dans le dossier screenshots" -ForegroundColor Green
} else {
    Write-Host "  ✗ Répertoire de destination non trouvé" -ForegroundColor Red
}

Write-Host ""
Write-Host "=== SCRIPT TERMINÉ ===" -ForegroundColor Green