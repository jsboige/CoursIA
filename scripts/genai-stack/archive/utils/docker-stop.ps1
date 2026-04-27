#Requires -Version 7.0
<#
.SYNOPSIS
    Arrêt des services Docker GenAI

.DESCRIPTION
    Script d'arrêt pour l'infrastructure Docker locale des services GenAI.
    
    Fonctionnalités:
    - Arrêt gracieux des services Docker
    - Nettoyage optionnel (volumes, images, réseau)
    - Sauvegarde des logs avant arrêt
    - Statistiques d'utilisation des ressources
    
.PARAMETER Services
    Liste des services à arrêter (par défaut: tous)

.PARAMETER Clean
    Supprime les volumes et images après arrêt

.PARAMETER SaveLogs
    Sauvegarde les logs avant arrêt

.PARAMETER Force
    Force l'arrêt des containers (kill au lieu de stop)

.EXAMPLE
    .\docker-stop.ps1
    Arrête tous les services proprement

.EXAMPLE
    .\docker-stop.ps1 -Services flux-1-dev
    Arrête uniquement le service FLUX

.EXAMPLE
    .\docker-stop.ps1 -Clean
    Arrête et nettoie tous les volumes/images

.EXAMPLE
    .\docker-stop.ps1 -SaveLogs
    Sauvegarde les logs avant d'arrêter
#>

[CmdletBinding()]
param(
    [string[]]$Services = @(),
    [switch]$Clean,
    [switch]$SaveLogs,
    [switch]$Force
)

$ErrorActionPreference = "Stop"
$ProgressPreference = "SilentlyContinue"

# ===== CONFIGURATION =====
$PROJECT_ROOT = Split-Path -Parent $PSScriptRoot
$LOGS_DIR = Join-Path $PROJECT_ROOT "logs"

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

# ===== SAUVEGARDE LOGS =====
function Save-ContainerLogs {
    Write-Section "Sauvegarde des Logs"
    
    # Créer le répertoire logs si nécessaire
    if (-not (Test-Path $LOGS_DIR)) {
        New-Item -ItemType Directory -Path $LOGS_DIR -Force | Out-Null
    }
    
    $timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
    $logsBackupDir = Join-Path $LOGS_DIR "backup_$timestamp"
    New-Item -ItemType Directory -Path $logsBackupDir -Force | Out-Null
    
    $containers = @(
        "coursia-orchestrator",
        "coursia-flux-1-dev",
        "coursia-sd35",
        "coursia-comfyui-workflows"
    )
    
    foreach ($container in $containers) {
        $running = docker ps -a --filter "name=$container" --format "{{.Names}}" 2>$null
        
        if ($running) {
            Write-Info "Sauvegarde logs de $container..."
            $logFile = Join-Path $logsBackupDir "$container.log"
            docker logs $container > $logFile 2>&1
            
            if (Test-Path $logFile) {
                $size = (Get-Item $logFile).Length / 1KB
                Write-Success "Logs sauvegardés: $logFile (${size}KB)"
            }
        }
    }
    
    Write-Success "Logs sauvegardés dans: $logsBackupDir"
}

# ===== STATISTIQUES RESSOURCES =====
function Show-ResourceStats {
    Write-Section "Statistiques d'Utilisation des Ressources"
    
    Write-Info "Récupération des statistiques..."
    Write-Host ""
    
    try {
        docker stats --no-stream --format "table {{.Container}}\t{{.CPUPerc}}\t{{.MemUsage}}\t{{.NetIO}}\t{{.BlockIO}}"
        Write-Host ""
    }
    catch {
        Write-Warning "Impossible de récupérer les statistiques"
    }
}

# ===== ARRÊT SERVICES =====
function Stop-DockerServices {
    param([bool]$ForceStop = $false)
    
    Write-Section "Arrêt des Services Docker"
    
    Push-Location $PROJECT_ROOT
    
    try {
        if ($ForceStop) {
            Write-Warning "Arrêt forcé des services (kill)..."
            if ($Services.Count -gt 0) {
                docker-compose kill $Services
            }
            else {
                docker-compose kill
            }
        }
        else {
            Write-Info "Arrêt gracieux des services..."
            if ($Services.Count -gt 0) {
                Write-Info "Services sélectionnés: $($Services -join ', ')"
                docker-compose stop $Services
            }
            else {
                Write-Info "Arrêt de tous les services"
                docker-compose stop
            }
        }
        
        if ($LASTEXITCODE -eq 0) {
            Write-Success "Services arrêtés"
            return $true
        }
        else {
            Write-Error "Erreur lors de l'arrêt des services"
            return $false
        }
    }
    finally {
        Pop-Location
    }
}

# ===== SUPPRESSION CONTAINERS =====
function Remove-DockerContainers {
    Write-Section "Suppression des Containers"
    
    Push-Location $PROJECT_ROOT
    
    try {
        Write-Info "Suppression des containers arrêtés..."
        
        if ($Services.Count -gt 0) {
            docker-compose rm -f $Services
        }
        else {
            docker-compose rm -f
        }
        
        if ($LASTEXITCODE -eq 0) {
            Write-Success "Containers supprimés"
            return $true
        }
        else {
            Write-Warning "Erreur lors de la suppression des containers"
            return $false
        }
    }
    finally {
        Pop-Location
    }
}

# ===== NETTOYAGE =====
function Clear-DockerResources {
    Write-Section "Nettoyage des Ressources Docker"
    
    # Confirmation
    Write-Warning "ATTENTION: Cette opération va supprimer:"
    Write-Host "  - Les volumes Docker GenAI"
    Write-Host "  - Les images Docker locales"
    Write-Host "  - Le réseau Docker GenAI"
    Write-Host ""
    
    $confirm = Read-Host "Confirmer le nettoyage? (oui/non)"
    if ($confirm -ne "oui") {
        Write-Info "Nettoyage annulé"
        return
    }
    
    Push-Location $PROJECT_ROOT
    
    try {
        # Supprimer les volumes
        Write-Info "Suppression des volumes..."
        docker-compose down -v 2>$null
        
        # Supprimer les images locales
        Write-Info "Suppression des images locales..."
        $images = docker images "coursia/*" -q 2>$null
        if ($images) {
            docker rmi $images 2>$null
        }
        
        # Supprimer le réseau
        Write-Info "Suppression du réseau..."
        docker network rm genai-dev-network 2>$null
        
        # Prune général
        Write-Info "Nettoyage général Docker..."
        docker system prune -f 2>$null
        
        Write-Success "Nettoyage terminé"
    }
    finally {
        Pop-Location
    }
}

# ===== AFFICHAGE STATUT FINAL =====
function Show-FinalStatus {
    Write-Section "Statut Final"
    
    Push-Location $PROJECT_ROOT
    
    try {
        $runningContainers = docker-compose ps --services --filter "status=running" 2>$null
        
        if ($runningContainers) {
            Write-Warning "Services encore en cours d'exécution:"
            docker-compose ps
        }
        else {
            Write-Success "Tous les services sont arrêtés"
        }
        
        Write-Host ""
        Write-Host "📝 Commandes Utiles:" -ForegroundColor Cyan
        Write-Host ""
        Write-Host "   Redémarrer services    : .\scripts\docker-start.ps1"
        Write-Host "   Vérifier configuration : .\scripts\docker-setup.ps1"
        Write-Host "   Voir les logs          : docker-compose logs [service]"
        Write-Host "   Nettoyer complètement  : .\scripts\docker-stop.ps1 -Clean"
        Write-Host ""
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
    Write-Host "║               CoursIA GenAI - Arrêt Services Docker                       ║" -ForegroundColor Magenta
    Write-Host "║                                                                            ║" -ForegroundColor Magenta
    Write-Host "╚════════════════════════════════════════════════════════════════════════════╝" -ForegroundColor Magenta
    Write-Host ""
    
    # Vérifier Docker
    try {
        docker ps | Out-Null
    }
    catch {
        Write-Error "Docker daemon n'est pas actif."
        exit 1
    }
    
    # Afficher les statistiques avant arrêt
    Show-ResourceStats
    
    # Sauvegarder les logs si demandé
    if ($SaveLogs) {
        Save-ContainerLogs
    }
    
    # Arrêter les services
    $stopped = Stop-DockerServices -ForceStop $Force
    
    if (-not $stopped) {
        Write-Error "Échec de l'arrêt des services"
        exit 1
    }
    
    # Supprimer les containers
    Remove-DockerContainers | Out-Null
    
    # Nettoyage si demandé
    if ($Clean) {
        Clear-DockerResources
    }
    
    # Afficher le statut final
    Show-FinalStatus
    
    Write-Success "Arrêt terminé avec succès!"
    Write-Host ""
}

# ===== EXECUTION =====
Main