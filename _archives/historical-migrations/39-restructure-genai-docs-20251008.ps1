<#
.SYNOPSIS
Restructure la documentation GenAI - Séparation suivis/docs de référence

.DESCRIPTION
Script de restructuration de la documentation GenAI pour:
- Déplacer les fichiers de référence vers docs/genai/
- Déplacer et renommer les suivis vers docs/genai-suivis/
- Supprimer les fichiers obsolètes
- Utiliser git mv pour préserver l'historique

.NOTES
Date: 2025-10-08
Auteur: Roo Code Mode
Phase: Restructuration Documentation GenAI
#>

[CmdletBinding()]
param()

$ErrorActionPreference = "Stop"

Write-Host "🔄 RESTRUCTURATION DOCUMENTATION GENAI" -ForegroundColor Cyan
Write-Host "======================================`n" -ForegroundColor Cyan

# Vérification du répertoire de travail
if (-not (Test-Path "docs")) {
    Write-Host "❌ Erreur: Le script doit être exécuté depuis la racine du projet" -ForegroundColor Red
    exit 1
}

# Vérification des répertoires cibles
if (-not (Test-Path "docs/genai")) {
    Write-Host "❌ Erreur: Le répertoire docs/genai n'existe pas" -ForegroundColor Red
    exit 1
}

if (-not (Test-Path "docs/genai-suivis")) {
    Write-Host "❌ Erreur: Le répertoire docs/genai-suivis n'existe pas" -ForegroundColor Red
    exit 1
}

# ==============================================================================
# PHASE 1: DÉPLACEMENT FICHIERS DE RÉFÉRENCE VERS docs/genai/
# ==============================================================================

Write-Host "📁 Phase 1: Déplacement fichiers de référence" -ForegroundColor Yellow

$referenceFiles = @(
    @{Old="docs/genai-deployment-guide.md"; New="docs/genai/deployment-guide.md"}
    @{Old="docs/genai-docker-lifecycle-management.md"; New="docs/genai/docker-lifecycle-management.md"}
    @{Old="docs/genai-docker-orchestration.md"; New="docs/genai/docker-orchestration.md"}
    @{Old="docs/genai-docker-specs.md"; New="docs/genai/docker-specs.md"}
    @{Old="docs/genai-environment-configurations.md"; New="docs/genai/environment-configurations.md"}
    @{Old="docs/genai-image-architecture.md"; New="docs/genai/architecture.md"}
    @{Old="docs/genai-images-development-standards.md"; New="docs/genai/development-standards.md"}
    @{Old="docs/genai-images-ecosystem-readme.md"; New="docs/genai/ecosystem-readme.md"}
    @{Old="docs/genai-images-user-guide.md"; New="docs/genai/user-guide.md"}
    @{Old="docs/genai-infrastructure-tests.md"; New="docs/genai/infrastructure-tests.md"}
    @{Old="docs/genai-integration-procedures.md"; New="docs/genai/integration-procedures.md"}
    @{Old="docs/genai-phase2-templates.md"; New="docs/genai/phase2-templates.md"}
    @{Old="docs/genai-powershell-scripts.md"; New="docs/genai/powershell-scripts.md"}
    @{Old="docs/genai-troubleshooting-guide.md"; New="docs/genai/troubleshooting.md"}
)

$movedCount = 0
foreach ($file in $referenceFiles) {
    if (Test-Path $file.Old) {
        Write-Host "  → Déplacement: $($file.Old) → $($file.New)" -ForegroundColor Gray
        git mv $file.Old $file.New
        if ($LASTEXITCODE -eq 0) {
            $movedCount++
            Write-Host "    ✅ OK" -ForegroundColor Green
        } else {
            Write-Host "    ❌ ERREUR" -ForegroundColor Red
        }
    } else {
        Write-Host "  ⚠️  Fichier non trouvé: $($file.Old)" -ForegroundColor Yellow
    }
}

Write-Host "`n✅ Phase 1 terminée: $movedCount fichiers de référence déplacés`n" -ForegroundColor Green

# ==============================================================================
# PHASE 2: DÉPLACEMENT ET RENOMMAGE SUIVIS VERS docs/genai-suivis/
# ==============================================================================

Write-Host "📋 Phase 2: Déplacement et renommage suivis de mission" -ForegroundColor Yellow

$suiviFiles = @(
    @{Old="docs/genai-images-mission-report.md"; New="docs/genai-suivis/2025-10-07_01_phase1-2-architecture.md"}
    @{Old="docs/genai-phase2-1-mission-report-final.md"; New="docs/genai-suivis/2025-10-08_02_phase2-1-final.md"}
    @{Old="docs/genai-deployment-production-ready.md"; New="docs/genai-suivis/2025-10-08_03_phase1-3-production-ready.md"}
)

$suiviCount = 0
foreach ($file in $suiviFiles) {
    if (Test-Path $file.Old) {
        Write-Host "  → Déplacement: $($file.Old) → $($file.New)" -ForegroundColor Gray
        git mv $file.Old $file.New
        if ($LASTEXITCODE -eq 0) {
            $suiviCount++
            Write-Host "    ✅ OK" -ForegroundColor Green
        } else {
            Write-Host "    ❌ ERREUR" -ForegroundColor Red
        }
    } else {
        Write-Host "  ⚠️  Fichier non trouvé: $($file.Old)" -ForegroundColor Yellow
    }
}

Write-Host "`n✅ Phase 2 terminée: $suiviCount suivis déplacés et renommés`n" -ForegroundColor Green

# ==============================================================================
# PHASE 3: SUPPRESSION FICHIER OBSOLÈTE
# ==============================================================================

Write-Host "🗑️  Phase 3: Suppression fichier obsolète" -ForegroundColor Yellow

$obsoleteFile = "docs/genai-env-setup-procedure.md"
if (Test-Path $obsoleteFile) {
    Write-Host "  → Suppression: $obsoleteFile" -ForegroundColor Gray
    git rm $obsoleteFile
    if ($LASTEXITCODE -eq 0) {
        Write-Host "    ✅ OK" -ForegroundColor Green
    } else {
        Write-Host "    ❌ ERREUR" -ForegroundColor Red
    }
} else {
    Write-Host "  ⚠️  Fichier déjà supprimé ou non trouvé" -ForegroundColor Yellow
}

Write-Host "`n✅ Phase 3 terminée`n" -ForegroundColor Green

# ==============================================================================
# RÉCAPITULATIF
# ==============================================================================

Write-Host "📊 RÉCAPITULATIF" -ForegroundColor Cyan
Write-Host "===============" -ForegroundColor Cyan
Write-Host "  • Fichiers de référence déplacés: $movedCount/14" -ForegroundColor White
Write-Host "  • Suivis déplacés et renommés: $suiviCount/3" -ForegroundColor White
Write-Host "  • Fichiers obsolètes supprimés: 1" -ForegroundColor White
Write-Host "`n✅ Restructuration terminée avec succès!" -ForegroundColor Green
Write-Host "`n⚠️  PROCHAINE ÉTAPE: Créer les fichiers README d'index" -ForegroundColor Yellow