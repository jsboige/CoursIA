# Script de création de la structure docs/suivis/genai-image/
# Créé le: 2025-10-16

Write-Host "Création de la structure docs/suivis/genai-image/" -ForegroundColor Cyan

$directories = @(
    "docs/suivis/genai-image/phase-01-08-docker/rapports",
    "docs/suivis/genai-image/phase-01-08-docker/scripts",
    "docs/suivis/genai-image/phase-09-10-investigation/rapports",
    "docs/suivis/genai-image/phase-09-10-investigation/scripts",
    "docs/suivis/genai-image/phase-09-10-investigation/screenshots",
    "docs/suivis/genai-image/phase-11-deployment/rapports",
    "docs/suivis/genai-image/phase-11-deployment/scripts",
    "docs/suivis/genai-image/phase-12a-production/rapports",
    "docs/suivis/genai-image/phase-12a-production/scripts",
    "docs/suivis/genai-image/phase-12a-production/screenshots",
    "docs/suivis/genai-image/phase-12b-tests/rapports",
    "docs/suivis/genai-image/phase-12b-tests/scripts",
    "docs/suivis/genai-image/phase-12c-architecture/rapports",
    "docs/suivis/genai-image/phase-13a-bridge/rapports"
)

foreach ($dir in $directories) {
    if (!(Test-Path $dir)) {
        New-Item -ItemType Directory -Path $dir -Force | Out-Null
        Write-Host "✓ Créé: $dir" -ForegroundColor Green
    } else {
        Write-Host "○ Existe déjà: $dir" -ForegroundColor Yellow
    }
}

Write-Host "`nStructure créée avec succès!" -ForegroundColor Green