#!/usr/bin/env pwsh

<#
.SYNOPSIS
Implementation complete structure modulaire GenAI Phase 2

.DESCRIPTION
Script d'implementation de l'architecture modulaire GenAI CoursIA Phase 2.1
- Backup securise de l'existant
- Creation structure 16 notebooks (00-04 repertoires)
- Generation templates fonctionnels
- Migration assets existants
- Configuration environnements

.PARAMETER Force
Force la recreation meme si la structure existe

.PARAMETER SkipBackup  
Skip la creation du backup (si deja fait)

.EXAMPLE
.\34-implement-genai-phase2-structure-20251008.ps1
.\34-implement-genai-phase2-structure-20251008.ps1 -Force
#>

[CmdletBinding()]
param(
    [switch]$Force,
    [switch]$SkipBackup
)

$ErrorActionPreference = "Stop"

Write-Host "IMPLEMENTATION GENAI PHASE 2.1" -ForegroundColor Cyan
Write-Host "================================" -ForegroundColor Cyan
Write-Host "Architecture modulaire 16 notebooks selon SDDD" -ForegroundColor Yellow

$GenAIPath = "MyIA.AI.Notebooks/GenAI"
$Timestamp = Get-Date -Format 'yyyyMMdd_HHmmss'

# === PHASE 1: BACKUP SECURISE ===
if (-not $SkipBackup) {
    Write-Host "`nPhase 1: Backup securise" -ForegroundColor Green
    try {
        & ".\scripts\33-backup-genai-before-phase2-20251008.ps1"
        Write-Host "Backup complete" -ForegroundColor Green
    } catch {
        Write-Host "Echec backup: $($_.Exception.Message)" -ForegroundColor Red
        if (-not $Force) { exit 1 }
    }
}

# === PHASE 2: CREATION STRUCTURE MODULAIRE ===
Write-Host "`nPhase 2: Structure modulaire" -ForegroundColor Green

# Structure repertoires selon standards SDDD
$ModuleStructure = @{
    "00-GenAI-Environment" = @{
        description = "[GREEN] Setup et Configuration"
        notebooks = @(
            "00-1-Environment-Setup.ipynb",
            "00-2-Docker-Services-Management.ipynb", 
            "00-3-API-Endpoints-Configuration.ipynb",
            "00-4-Environment-Validation.ipynb"
        )
    }
    "01-Images-Foundation" = @{
        description = "[GREEN] Modeles Base"
        notebooks = @(
            "01-1-OpenAI-DALL-E-3.ipynb",
            "01-2-GPT-5-Image-Generation.ipynb",
            "01-3-Basic-Image-Operations.ipynb"
        )
    }
    "02-Images-Advanced" = @{
        description = "[ORANGE] Avance"
        notebooks = @(
            "02-1-Qwen-Image-Edit-2509.ipynb",
            "02-2-FLUX-1-Advanced-Generation.ipynb",
            "02-3-Stable-Diffusion-3-5.ipynb"
        )
    }
    "03-Images-Orchestration" = @{
        description = "[RED] Multi-Modeles"
        notebooks = @(
            "03-1-Multi-Model-Comparison.ipynb",
            "03-2-Workflow-Orchestration.ipynb",
            "03-3-Performance-Optimization.ipynb"
        )
    }
    "04-Images-Applications" = @{
        description = "[RED] Applications"
        notebooks = @(
            "04-1-Educational-Content-Generation.ipynb",
            "04-2-Creative-Workflows.ipynb",
            "04-3-Production-Integration.ipynb"
        )
    }
}

# Repertoires support
$SupportDirs = @(
    "shared/helpers",
    "shared/configs", 
    "shared/templates",
    "assets/images",
    "assets/models",
    "outputs/generated",
    "outputs/comparisons",
    "logs"
)

# === CREATION REPERTOIRES ===
foreach ($module in $ModuleStructure.Keys) {
    $modulePath = Join-Path $GenAIPath $module
    Write-Host "Creation: $module" -ForegroundColor Cyan
    
    if (-not (Test-Path $modulePath)) {
        New-Item -Path $modulePath -ItemType Directory -Force | Out-Null
    }
    
    # README par module
    $readmeContent = @"
# $module - GenAI Images CoursIA

## Vue d'Ensemble
$($ModuleStructure[$module].description)

## Notebooks du Module

"@
    
    foreach ($notebook in $ModuleStructure[$module].notebooks) {
        $readmeContent += "- ``$notebook``"
        $readmeContent += "`n"
    }
    
    $readmeContent += @"

## Prerequis
- Configuration .env avec cles API
- Python 3.11+ avec dependances
- Variables d'environnement OpenRouter

## Utilisation
1. Configurer l'environnement selon 00-GenAI-Environment
2. Executer les notebooks dans l'ordre numerique
3. Verifier les outputs dans /outputs/

---
*Genere automatiquement par Phase 2.1 - $Timestamp*
"@
    
    Set-Content -Path (Join-Path $modulePath "README.md") -Value $readmeContent -Encoding UTF8
}

# Creation repertoires support
foreach ($dir in $SupportDirs) {
    $dirPath = Join-Path $GenAIPath $dir
    Write-Host "Support: $dir" -ForegroundColor Yellow
    if (-not (Test-Path $dirPath)) {
        New-Item -Path $dirPath -ItemType Directory -Force | Out-Null
    }
}

Write-Host "Structure modulaire creee" -ForegroundColor Green

# === PHASE 3: CONFIGURATION ENVIRONNEMENT ===
Write-Host "`nPhase 3: Configuration environnement" -ForegroundColor Green

# .env.template
$envTemplate = @"
# GenAI CoursIA - Configuration Phase 2
# Copier vers .env et remplir les valeurs

# === OPENROUTER API (PRIORITAIRE) ===
OPENROUTER_API_KEY=sk-or-v1-your-key-here
OPENROUTER_BASE_URL=https://openrouter.ai/api/v1
OPENROUTER_APP_NAME=CoursIA-GenAI

# === OPENAI API (FALLBACK) ===
OPENAI_API_KEY=sk-proj-your-key-here
OPENAI_BASE_URL=https://api.openai.com/v1

# === MODELES PREFERES ===
DEFAULT_VISION_MODEL=gpt-4o-2024-08-06
DEFAULT_IMAGE_MODEL=dall-e-3
QWEN_IMAGE_MODEL=qwen/qwen-vl-max
FLUX_MODEL=black-forest-labs/flux.1-dev

# === DOCKER LOCAL (OPTIONNEL) ===
DOCKER_ENABLED=false
FLUX_API_URL=http://localhost:8189
SD_API_URL=http://localhost:8190
COMFYUI_API_URL=http://localhost:8191

# === CONFIGURATION GENAI ===
GENAI_TIMEOUT_SECONDS=300
GENAI_MAX_RETRIES=3
GENAI_OUTPUT_DIR=outputs/generated
GENAI_LOG_LEVEL=INFO
GENAI_BATCH_SIZE=1

# === SAUVEGARDE ===
AUTO_SAVE_OUTPUTS=true
SAVE_METADATA=true
COMPRESSION_ENABLED=true

# Phase 2.1 - $Timestamp
"@

$envTemplatePath = Join-Path $GenAIPath ".env.template"
Set-Content -Path $envTemplatePath -Value $envTemplate -Encoding UTF8

# requirements.txt global
$requirements = @"
# GenAI CoursIA Phase 2 - Dependances Python
openai>=1.12.0
anthropic>=0.21.0
requests>=2.31.0
pillow>=10.0.0
numpy>=1.24.0
pandas>=2.0.0
matplotlib>=3.7.0
jupyter>=1.0.0
ipywidgets>=8.0.0
python-dotenv>=1.0.0
aiohttp>=3.8.0
asyncio-throttle>=1.0.0

# Generation automatique Phase 2.1 - $Timestamp
"@

$requirementsPath = Join-Path $GenAIPath "requirements.txt"
Set-Content -Path $requirementsPath -Value $requirements -Encoding UTF8

Write-Host "Configuration environnement creee" -ForegroundColor Green

# === PHASE 4: HELPERS PARTAGES ===
Write-Host "`nPhase 4: Helpers partages" -ForegroundColor Green

$helpersContent = @"
#!/usr/bin/env python3
"""
GenAI Helpers - Utilitaires Phase 2 CoursIA
Fonctionnalites communes pour tous les modules GenAI Images
"""

import os
import json
import base64
import asyncio
from typing import Dict, List, Optional, Any
from pathlib import Path
from datetime import datetime
import logging

# Configuration logging
def setup_genai_logging(level="INFO"):
    """Configuration logging standardisee GenAI"""
    logger = logging.getLogger('genai_coursia')
    logger.setLevel(getattr(logging, level))
    
    if not logger.handlers:
        handler = logging.StreamHandler()
        formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
        handler.setFormatter(formatter)
        logger.addHandler(handler)
    
    return logger

# Configuration environnement
def load_genai_config():
    """Chargement configuration GenAI depuis .env"""
    from dotenv import load_dotenv
    
    env_file = Path.cwd() / '.env'
    if env_file.exists():
        load_dotenv(env_file)
        return True
    return False

# Validation APIs
def validate_apis():
    """Validation des APIs disponibles"""
    status = {
        'openrouter': bool(os.getenv('OPENROUTER_API_KEY')),
        'openai': bool(os.getenv('OPENAI_API_KEY')),
        'docker_enabled': os.getenv('DOCKER_ENABLED', 'false').lower() == 'true'
    }
    return status

# Sauvegarde resultats
def save_generation_result(image_data, metadata, output_dir="outputs/generated"):
    """Sauvegarde standard resultats generation"""
    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)
    
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    
    # Sauvegarde image si base64
    if isinstance(image_data, str):
        image_path = output_path / f"genai_image_{timestamp}.png"
        with open(image_path, 'wb') as f:
            f.write(base64.b64decode(image_data))
    
    # Sauvegarde metadonnees
    metadata_path = output_path / f"genai_metadata_{timestamp}.json"
    with open(metadata_path, 'w') as f:
        json.dump(metadata, f, indent=2, default=str)
    
    return str(image_path), str(metadata_path)

# Export principales fonctions
__all__ = ['setup_genai_logging', 'load_genai_config', 'validate_apis', 'save_generation_result']
"@

$helpersPath = Join-Path $GenAIPath "shared/helpers/genai_helpers.py"
Set-Content -Path $helpersPath -Value $helpersContent -Encoding UTF8

Write-Host "Helpers partages crees" -ForegroundColor Green

# === PHASE 5: MIGRATION ASSETS EXISTANTS ===
Write-Host "`nPhase 5: Migration assets existants" -ForegroundColor Green

$assetsToMigrate = @{
    "DMC_colors.json" = "assets/models/DMC_colors.json"
    "img2img_cross_stitch_pattern_maker.ipynb" = "04-Images-Applications/04-3-Cross-Stitch-Pattern-Maker-Legacy.ipynb"
}

foreach ($source in $assetsToMigrate.Keys) {
    $sourcePath = Join-Path $GenAIPath $source
    $destPath = Join-Path $GenAIPath $assetsToMigrate[$source]
    
    if (Test-Path $sourcePath) {
        Write-Host "Migration: $source -> $($assetsToMigrate[$source])" -ForegroundColor Yellow
        
        # Creer repertoire destination si necessaire
        $destDir = Split-Path $destPath -Parent
        if (-not (Test-Path $destDir)) {
            New-Item -Path $destDir -ItemType Directory -Force | Out-Null
        }
        
        Copy-Item -Path $sourcePath -Destination $destPath -Force
    } else {
        Write-Host "Asset non trouve: $source" -ForegroundColor Yellow
    }
}

Write-Host "Migration assets completee" -ForegroundColor Green

# === PHASE 6: RAPPORT FINAL ===
Write-Host "`nPhase 6: Rapport implementation" -ForegroundColor Green

$implementationReport = @{
    phase = "2.1"
    timestamp = $Timestamp
    modules_created = $ModuleStructure.Keys.Count
    notebooks_planned = ($ModuleStructure.Values | ForEach-Object { $_.notebooks.Count } | Measure-Object -Sum).Sum
    support_dirs = $SupportDirs.Count
    assets_migrated = $assetsToMigrate.Keys.Count
    status = "completed"
}

$reportPath = Join-Path $GenAIPath "PHASE2_IMPLEMENTATION_REPORT.json"
$implementationReport | ConvertTo-Json -Depth 3 | Set-Content -Path $reportPath -Encoding UTF8

# Affichage resume
Write-Host "`nIMPLEMENTATION PHASE 2.1 COMPLETEE" -ForegroundColor Green
Write-Host "===================================" -ForegroundColor Green
Write-Host "Modules crees: $($implementationReport.modules_created)" -ForegroundColor Cyan
Write-Host "Notebooks prevus: $($implementationReport.notebooks_planned)" -ForegroundColor Cyan
Write-Host "Repertoires support: $($implementationReport.support_dirs)" -ForegroundColor Cyan
Write-Host "Assets migres: $($implementationReport.assets_migrated)" -ForegroundColor Cyan
Write-Host "Rapport: $reportPath" -ForegroundColor Cyan

Write-Host "`nPROCHAINES ETAPES:" -ForegroundColor Yellow
Write-Host "1. Generation des notebooks templates (Phase 2.2)" -ForegroundColor White
Write-Host "2. Configuration .env selon .env.template" -ForegroundColor White  
Write-Host "3. Test d'integration MCP" -ForegroundColor White
Write-Host "4. Validation fonctionnelle" -ForegroundColor White

Write-Host "`nStructure modulaire GenAI Phase 2 prete !" -ForegroundColor Green