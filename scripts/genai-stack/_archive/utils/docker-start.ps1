#Requires -Version 7.0
<#
.SYNOPSIS
    Démarrage des services Docker GenAI

.DESCRIPTION
    Script de démarrage pour l'infrastructure Docker locale des services GenAI.
    
    Fonctionnalités:
    - Démarrage des services Docker
    - Health checks automatiques
    - Affichage du statut des services
    - Logs en temps réel (optionnel)
    
.PARAMETER Services
    Liste des services à démarrer (par défaut: tous)

.PARAMETER Follow
    Affiche les logs en temps réel après le démarrage

.PARAMETER Build
    Rebuild les images avant de démarrer

.EXAMPLE
    .\docker-start.ps1
    Démarre tous les services

.EXAMPLE
    .\docker-start.ps1 -Services flux-1-dev,orchestrator
    Démarre uniquement FLUX et l'orchestrateur

.EXAMPLE
    .\docker-start.ps1 -Follow
    Démarre tous les services et affiche les logs
#>

[CmdletBinding()]
param(
    [string[]]$Services = @(),
    [switch]$Follow,
    [switch]$Build
)

$ErrorActionPreference = "Stop"
$ProgressPreference = "SilentlyContinue"

# ===== CONFIGURATION =====
$PROJECT_ROOT = Split-Path -Parent $PSScriptRoot
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

# ===== DÉMARRAGE SERVICES =====
function Start-DockerServices {
    Write-Section "Démarrage des Services Docker"
    
    Push-Location $PROJECT_ROOT
    
    try {
        # Charger les variables d'environnement
        if (Test-Path $ENV_FILE) {
            Write-Info "Chargement configuration depuis .env.docker"
            $env:COMPOSE_FILE = "docker-compose.yml"
            $env:COMPOSE_ENV_FILES = ".env.docker"
        }
        
        # Build si demandé
        if ($Build) {
            Write-Info "Rebuild des images..."
            docker-compose build $Services
            if ($LASTEXITCODE -ne 0) {
                Write-Error "Erreur lors du build"
                return $false
            }
            Write-Success "Images construites"
        }
        
        # Démarrer les services
        Write-Info "Démarrage des services..."
        if ($Services.Count -gt 0) {
            Write-Info "Services sélectionnés: $($Services -join ', ')"
            docker-compose up -d $Services
        }
        else {
            Write-Info "Démarrage de tous les services"
            docker-compose up -d
        }
        
        if ($LASTEXITCODE -ne 0) {
            Write-Error "Erreur lors du démarrage des services"
            return $false
        }
        
        Write-Success "Services démarrés"
        return $true
    }
    finally {
        Pop-Location
    }
}

# ===== HEALTH CHECKS =====
function Wait-ServiceHealthy {
    param(
        [string]$ServiceName,
        [string]$ContainerName,
        [int]$MaxWaitSeconds = 120
    )
    
    Write-Info "Attente santé du service $ServiceName..."
    
    $startTime = Get-Date
    $healthy = $false
    
    while (((Get-Date) - $startTime).TotalSeconds -lt $MaxWaitSeconds) {
        $status = docker inspect --format='{{.State.Health.Status}}' $ContainerName 2>$null
        
        if ($status -eq "healthy") {
            $healthy = $true
            break
        }
        elseif ($status -eq "unhealthy") {
            Write-Warning "Service $ServiceName est unhealthy"
            break
        }
        
        # Vérifier au moins si le container tourne
        $running = docker inspect --format='{{.State.Running}}' $ContainerName 2>$null
        if ($running -eq "true") {
            # Pas de healthcheck défini, considérer comme sain si running
            if ([string]::IsNullOrEmpty($status)) {
                $healthy = $true
                break
            }
        }
        
        Start-Sleep -Seconds 2
    }
    
    return $healthy
}

function Test-ServicesHealth {
    Write-Section "Vérification Santé des Services"
    
    $services = @{
        "orchestrator" = "coursia-orchestrator"
        "flux-1-dev" = "coursia-flux-1-dev"
        "stable-diffusion-35" = "coursia-sd35"
        "comfyui-workflows" = "coursia-comfyui-workflows"
    }
    
    $allHealthy = $true
    
    foreach ($service in $services.GetEnumerator()) {
        # Vérifier si le service est démarré
        $running = docker ps --filter "name=$($service.Value)" --format "{{.Names}}" 2>$null
        
        if (-not $running) {
            Write-Warning "Service $($service.Key) n'est pas démarré"
            continue
        }
        
        # Attendre que le service soit sain
        $healthy = Wait-ServiceHealthy -ServiceName $service.Key -ContainerName $service.Value
        
        if ($healthy) {
            Write-Success "Service $($service.Key) est sain"
        }
        else {
            Write-Warning "Service $($service.Key) n'est pas sain (timeout ou erreur)"
            $allHealthy = $false
        }
    }
    
    return $allHealthy
}

# ===== AFFICHAGE STATUT =====
function Show-ServicesStatus {
    Write-Section "Statut des Services"
    
    Push-Location $PROJECT_ROOT
    
    try {
        Write-Host ""
        docker-compose ps
        Write-Host ""
        
        # Afficher les URLs d'accès
        Write-Host "🌐 URLs d'Accès:" -ForegroundColor Cyan
        Write-Host ""
        Write-Host "   📊 Orchestrator API    : " -NoNewline
        Write-Host "http://localhost:8193" -ForegroundColor Yellow
        Write-Host "   🎨 FLUX.1-dev (ComfyUI): " -NoNewline
        Write-Host "http://localhost:8189" -ForegroundColor Yellow
        Write-Host "   🖼️  Stable Diffusion 3.5: " -NoNewline
        Write-Host "http://localhost:8190" -ForegroundColor Yellow
        Write-Host "   🔧 ComfyUI Workflows   : " -NoNewline
        Write-Host "http://localhost:8191" -ForegroundColor Yellow
        Write-Host ""
        
        # Afficher les commandes utiles
        Write-Host "📝 Commandes Utiles:" -ForegroundColor Cyan
        Write-Host ""
        Write-Host "   Voir les logs        : docker-compose logs -f [service]"
        Write-Host "   Arrêter les services : .\scripts\docker-stop.ps1"
        Write-Host "   Statut des services  : docker-compose ps"
        Write-Host "   Shell dans container : docker exec -it [container] /bin/bash"
        Write-Host ""
    }
    finally {
        Pop-Location
    }
}

# ===== LOGS EN TEMPS RÉEL =====
function Show-Logs {
    Write-Section "Logs en Temps Réel"
    
    Push-Location $PROJECT_ROOT
    
    try {
        Write-Info "Affichage des logs (Ctrl+C pour quitter)..."
        Write-Host ""
        
        if ($Services.Count -gt 0) {
            docker-compose logs -f $Services
        }
        else {
            docker-compose logs -f
        }
    }
    finally {
        Pop-Location
    }
}

# ===== MAIN =====
function Main {
    Write-Host ""
    Write-Host "╔════════════════════════════════════════════════════════════════════════════╗" -ForegroundColor Magenta
    Write-Host "║                                                                            ║" -ForegroundColor Magenta
    Write-Host "║              CoursIA GenAI - Démarrage Services Docker                    ║" -ForegroundColor Magenta
    Write-Host "║                                                                            ║" -ForegroundColor Magenta
    Write-Host "╚════════════════════════════════════════════════════════════════════════════╝" -ForegroundColor Magenta
    Write-Host ""
    
    # Vérifier Docker
    try {
        docker ps | Out-Null
    }
    catch {
        Write-Error "Docker daemon n'est pas actif. Démarrez Docker Desktop."
        exit 1
    }
    
    # Démarrer les services
    if (-not (Start-DockerServices)) {
        Write-Error "Échec du démarrage des services"
        exit 1
    }
    
    # Health checks
    Write-Host ""
    Write-Info "Attente de la disponibilité des services (peut prendre 1-2 minutes)..."
    Write-Host ""
    
    Start-Sleep -Seconds 5  # Laisser le temps aux containers de démarrer
    
    $allHealthy = Test-ServicesHealth
    
    if (-not $allHealthy) {
        Write-Warning "Certains services ne sont pas sains, mais ils sont démarrés"
        Write-Info "Consultez les logs pour plus de détails: docker-compose logs -f"
    }
    
    # Afficher le statut
    Show-ServicesStatus
    
    # Logs en temps réel si demandé
    if ($Follow) {
        Show-Logs
    }
    else {
        Write-Success "Services démarrés avec succès!"
        Write-Host ""
    }
}

# ===== EXECUTION =====
Main