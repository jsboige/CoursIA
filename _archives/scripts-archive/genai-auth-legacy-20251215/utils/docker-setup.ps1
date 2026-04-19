#Requires -Version 7.0
<#
.SYNOPSIS
    Configuration et initialisation de l'environnement Docker GenAI

.DESCRIPTION
    Script de setup pour l'infrastructure Docker locale des services GenAI.
    
    Fonctionnalités:
    - Validation des prérequis (Docker Desktop, GPU NVIDIA, espace disque)
    - Création de la structure de répertoires
    - Configuration des volumes Docker
    - Création du réseau Docker
    - Build des images personnalisées
    - Validation de la configuration
    
.PARAMETER SkipPrerequisites
    Ignore la vérification des prérequis

.PARAMETER SkipBuild
    Ignore le build des images Docker

.EXAMPLE
    .\docker-setup.ps1
    Configuration complète avec toutes les vérifications

.EXAMPLE
    .\docker-setup.ps1 -SkipBuild
    Configuration sans rebuilder les images
#>

[CmdletBinding()]
param(
    [switch]$SkipPrerequisites,
    [switch]$SkipBuild
)

$ErrorActionPreference = "Stop"
$ProgressPreference = "SilentlyContinue"

# ===== CONFIGURATION =====
$PROJECT_ROOT = Split-Path -Parent $PSScriptRoot
$DOCKER_CONFIG_DIR = Join-Path $PROJECT_ROOT "docker-configurations"
$ENV_FILE = Join-Path $PROJECT_ROOT ".env.docker"

# ===== FONCTIONS UTILITAIRES =====
function Write-Section {
    param([string]$Title)
    Write-Host ""
    Write-Host ("=" * 80) -ForegroundColor Cyan
    Write-Host "  $Title" -ForegroundColor Cyan
    Write-Host ("=" * 80) -ForegroundColor Cyan
}

function Write-Success {
    param([string]$Message)
    Write-Host "✅ $Message" -ForegroundColor Green
}

function Write-Info {
    param([string]$Message)
    Write-Host "ℹ️  $Message" -ForegroundColor Blue
}

function Write-Warning {
    param([string]$Message)
    Write-Host "⚠️  $Message" -ForegroundColor Yellow
}

function Write-Error {
    param([string]$Message)
    Write-Host "❌ $Message" -ForegroundColor Red
}

function Test-Command {
    param([string]$Command)
    try {
        Get-Command $Command -ErrorAction Stop | Out-Null
        return $true
    }
    catch {
        return $false
    }
}

# ===== VALIDATION PRÉREQUIS =====
function Test-Prerequisites {
    Write-Section "Validation des Prérequis"
    
    $allOk = $true
    
    # Docker Desktop
    Write-Info "Vérification Docker Desktop..."
    if (Test-Command "docker") {
        $dockerVersion = docker --version
        Write-Success "Docker trouvé: $dockerVersion"
        
        # Vérifier si Docker est en cours d'exécution
        try {
            docker ps | Out-Null
            Write-Success "Docker daemon est actif"
        }
        catch {
            Write-Error "Docker daemon n'est pas actif. Démarrez Docker Desktop."
            $allOk = $false
        }
    }
    else {
        Write-Error "Docker n'est pas installé. Installez Docker Desktop."
        $allOk = $false
    }
    
    # Docker Compose
    Write-Info "Vérification Docker Compose..."
    if (Test-Command "docker-compose") {
        $composeVersion = docker-compose --version
        Write-Success "Docker Compose trouvé: $composeVersion"
    }
    else {
        Write-Error "Docker Compose n'est pas installé."
        $allOk = $false
    }
    
    # NVIDIA GPU (optionnel mais recommandé)
    Write-Info "Vérification GPU NVIDIA..."
    if (Test-Command "nvidia-smi") {
        $gpuInfo = nvidia-smi --query-gpu=name,memory.total --format=csv,noheader 2>$null
        if ($gpuInfo) {
            Write-Success "GPU NVIDIA détecté: $gpuInfo"
        }
        else {
            Write-Warning "nvidia-smi trouvé mais aucun GPU détecté"
        }
    }
    else {
        Write-Warning "GPU NVIDIA non détecté. Les services GPU ne fonctionneront pas."
    }
    
    # Espace disque
    Write-Info "Vérification espace disque..."
    $drive = (Get-Item $PROJECT_ROOT).PSDrive
    $freeSpace = [math]::Round((Get-PSDrive $drive.Name).Free / 1GB, 2)
    if ($freeSpace -gt 50) {
        Write-Success "Espace disque disponible: ${freeSpace}GB"
    }
    else {
        Write-Warning "Espace disque faible: ${freeSpace}GB (minimum recommandé: 50GB)"
    }
    
    # RAM
    Write-Info "Vérification RAM..."
    $ram = [math]::Round((Get-CimInstance Win32_ComputerSystem).TotalPhysicalMemory / 1GB, 2)
    if ($ram -ge 32) {
        Write-Success "RAM disponible: ${ram}GB"
    }
    else {
        Write-Warning "RAM limitée: ${ram}GB (minimum recommandé: 32GB)"
    }
    
    return $allOk
}

# ===== CRÉATION STRUCTURE RÉPERTOIRES =====
function Initialize-DirectoryStructure {
    Write-Section "Création de la Structure de Répertoires"
    
    $directories = @(
        "$DOCKER_CONFIG_DIR\models",
        "$DOCKER_CONFIG_DIR\outputs",
        "$DOCKER_CONFIG_DIR\cache",
        "$DOCKER_CONFIG_DIR\flux-1-dev\custom_nodes",
        "$DOCKER_CONFIG_DIR\flux-1-dev\workflows",
        "$DOCKER_CONFIG_DIR\flux-1-dev\config",
        "$DOCKER_CONFIG_DIR\stable-diffusion-3.5\config",
        "$DOCKER_CONFIG_DIR\comfyui-workflows\custom_nodes",
        "$DOCKER_CONFIG_DIR\comfyui-workflows\workflows",
        "$DOCKER_CONFIG_DIR\comfyui-workflows\input",
        "$DOCKER_CONFIG_DIR\orchestrator\config"
    )
    
    foreach ($dir in $directories) {
        if (-not (Test-Path $dir)) {
            New-Item -ItemType Directory -Path $dir -Force | Out-Null
            Write-Success "Créé: $dir"
        }
        else {
            Write-Info "Existe: $dir"
        }
    }
}

# ===== CONFIGURATION RÉSEAU DOCKER =====
function Initialize-DockerNetwork {
    Write-Section "Configuration Réseau Docker"
    
    $networkName = "genai-dev-network"
    
    # Vérifier si le réseau existe
    $existingNetwork = docker network ls --filter "name=$networkName" --format "{{.Name}}" 2>$null
    
    if ($existingNetwork -eq $networkName) {
        Write-Info "Réseau '$networkName' existe déjà"
    }
    else {
        Write-Info "Création du réseau '$networkName'..."
        docker network create `
            --driver bridge `
            --subnet 172.20.0.0/16 `
            --gateway 172.20.0.1 `
            $networkName 2>$null
        
        if ($LASTEXITCODE -eq 0) {
            Write-Success "Réseau créé avec succès"
        }
        else {
            Write-Warning "Erreur lors de la création du réseau (peut déjà exister)"
        }
    }
}

# ===== BUILD IMAGES DOCKER =====
function Build-DockerImages {
    Write-Section "Build des Images Docker"
    
    Push-Location $PROJECT_ROOT
    
    try {
        Write-Info "Build de l'image orchestrator..."
        docker-compose build orchestrator
        
        if ($LASTEXITCODE -eq 0) {
            Write-Success "Image orchestrator construite"
        }
        else {
            Write-Error "Erreur lors du build de l'image orchestrator"
            return $false
        }
        
        return $true
    }
    finally {
        Pop-Location
    }
}

# ===== VALIDATION CONFIGURATION =====
function Test-Configuration {
    Write-Section "Validation de la Configuration"
    
    # Vérifier .env.docker
    if (Test-Path $ENV_FILE) {
        Write-Success "Fichier .env.docker trouvé"
    }
    else {
        Write-Error "Fichier .env.docker manquant"
        return $false
    }
    
    # Vérifier docker-compose.yml
    $composeFile = Join-Path $PROJECT_ROOT "docker-compose.yml"
    if (Test-Path $composeFile) {
        Write-Success "Fichier docker-compose.yml trouvé"
        
        # Valider la syntaxe YAML
        Write-Info "Validation de la syntaxe docker-compose..."
        Push-Location $PROJECT_ROOT
        docker-compose config 2>&1 | Out-Null
        if ($LASTEXITCODE -eq 0) {
            Write-Success "Configuration docker-compose valide"
        }
        else {
            Write-Error "Erreur de syntaxe dans docker-compose.yml"
            Pop-Location
            return $false
        }
        Pop-Location
    }
    else {
        Write-Error "Fichier docker-compose.yml manquant"
        return $false
    }
    
    return $true
}

# ===== AFFICHAGE RÉSUMÉ =====
function Show-Summary {
    Write-Section "Résumé de la Configuration"
    
    Write-Host ""
    Write-Host "📁 Répertoire projet:" -ForegroundColor Cyan
    Write-Host "   $PROJECT_ROOT"
    Write-Host ""
    Write-Host "🐳 Services Docker configurés:" -ForegroundColor Cyan
    Write-Host "   - FLUX.1-dev (ComfyUI)      : Port 8189"
    Write-Host "   - Stable Diffusion 3.5      : Port 8190"
    Write-Host "   - ComfyUI Workflows         : Port 8191"
    Write-Host "   - Orchestrator              : Port 8193"
    Write-Host ""
    Write-Host "🌐 Réseau:" -ForegroundColor Cyan
    Write-Host "   - Nom: genai-dev-network"
    Write-Host "   - Subnet: 172.20.0.0/16"
    Write-Host ""
    Write-Host "📦 Volumes:" -ForegroundColor Cyan
    Write-Host "   - Models : $DOCKER_CONFIG_DIR\models"
    Write-Host "   - Outputs: $DOCKER_CONFIG_DIR\outputs"
    Write-Host "   - Cache  : $DOCKER_CONFIG_DIR\cache"
    Write-Host ""
    Write-Host "✅ Configuration terminée!" -ForegroundColor Green
    Write-Host ""
    Write-Host "Prochaines étapes:" -ForegroundColor Yellow
    Write-Host "   1. Placez vos modèles dans: $DOCKER_CONFIG_DIR\models"
    Write-Host "   2. Démarrez les services: .\scripts\docker-start.ps1"
    Write-Host "   3. Vérifiez le statut: docker-compose ps"
    Write-Host ""
}

# ===== MAIN =====
function Main {
    Write-Host ""
    Write-Host "╔════════════════════════════════════════════════════════════════════════════╗" -ForegroundColor Magenta
    Write-Host "║                                                                            ║" -ForegroundColor Magenta
    Write-Host "║              CoursIA GenAI - Configuration Docker Locale                  ║" -ForegroundColor Magenta
    Write-Host "║                                                                            ║" -ForegroundColor Magenta
    Write-Host "╚════════════════════════════════════════════════════════════════════════════╝" -ForegroundColor Magenta
    Write-Host ""
    
    # Validation prérequis
    if (-not $SkipPrerequisites) {
        if (-not (Test-Prerequisites)) {
            Write-Error "Prérequis non satisfaits. Installation annulée."
            exit 1
        }
    }
    else {
        Write-Warning "Vérification des prérequis ignorée"
    }
    
    # Création structure
    Initialize-DirectoryStructure
    
    # Configuration réseau
    Initialize-DockerNetwork
    
    # Build images
    if (-not $SkipBuild) {
        if (-not (Build-DockerImages)) {
            Write-Error "Erreur lors du build des images"
            exit 1
        }
    }
    else {
        Write-Warning "Build des images ignoré"
    }
    
    # Validation
    if (-not (Test-Configuration)) {
        Write-Error "Validation de la configuration échouée"
        exit 1
    }
    
    # Résumé
    Show-Summary
}

# ===== EXECUTION =====
Main