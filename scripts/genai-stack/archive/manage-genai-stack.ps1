# ==============================================================================
# GESTIONNAIRE UNIFIÉ DE LA STACK GENAI (PHASE 43)
# Orchestrateur : ComfyUI-Qwen (GPU 0) + Forge-Turbo (GPU 1)
# ==============================================================================

param (
    [Parameter(Mandatory=$false)]
    [ValidateSet("start", "stop", "restart", "status")]
    [string]$Action = "status"
)

# Configuration des chemins relatifs (depuis scripts/genai-stack/)
$RepoRoot = Resolve-Path "$PSScriptRoot/../.."
$ComfyPath = "$RepoRoot/docker-configurations/services/comfyui-qwen/docker-compose.yml"
$ForgePath = "$RepoRoot/docker-configurations/services/forge-turbo/docker-compose.yml"
$VramScript = "$PSScriptRoot/check_vram.py"

# Activation de l'environnement Python pour check_vram.py si nécessaire
# (On suppose ici que python est dans le PATH, sinon ajuster)
$PythonCmd = "python"

function Write-Header {
    param ([string]$Title)
    Write-Host ""
    Write-Host ("=" * 50) -ForegroundColor Cyan
    Write-Host " $Title" -ForegroundColor Cyan
    Write-Host ("=" * 50) -ForegroundColor Cyan
}

function Show-VRAM-Status {
    Write-Header "ÉTAT DES GPUs (VRAM)"
    if (Test-Path $VramScript) {
        & $PythonCmd $VramScript
    } else {
        Write-Warning "Le script check_vram.py est introuvable à : $VramScript"
    }
}

function Get-Container-Status {
    Write-Header "ÉTAT DES CONTENEURS"
    
    $comfyRunning = (docker ps --filter "name=comfyui-qwen" --format "{{.Status}}")
    $forgeRunning = (docker ps --filter "name=forge-turbo" --format "{{.Status}}")

    Write-Host "ComfyUI-Qwen (Port 8188 - GPU 0) : " -NoNewline
    if ($comfyRunning) { Write-Host "🟢 RUNNING ($comfyRunning)" -ForegroundColor Green }
    else { Write-Host "🔴 STOPPED" -ForegroundColor Red }

    Write-Host "Forge-Turbo  (Port 17861 - GPU 1): " -NoNewline
    if ($forgeRunning) { Write-Host "🟢 RUNNING ($forgeRunning)" -ForegroundColor Green }
    else { Write-Host "🔴 STOPPED" -ForegroundColor Red }
}

function Test-Endpoints {
    Write-Header "TEST DE CONNECTIVITÉ"
    
    $endpoints = @(
        @{ Name="ComfyUI"; Url="http://localhost:8188/" },
        @{ Name="ForgeUI"; Url="http://localhost:17861/" }
    )

    foreach ($ep in $endpoints) {
        Write-Host "Ping $($ep.Name)... " -NoNewline
        try {
            $response = Invoke-WebRequest -Uri $ep.Url -Method Head -TimeoutSec 2 -ErrorAction Stop
            if ($response.StatusCode -eq 200) {
                Write-Host "OK (200)" -ForegroundColor Green
            } else {
                Write-Host "WARN ($($response.StatusCode))" -ForegroundColor Yellow
            }
        } catch {
            Write-Host "FAIL (Inaccessible)" -ForegroundColor Red
        }
    }
}

function Start-Stack {
    Write-Header "DÉMARRAGE DE LA STACK GENAI"
    
    Write-Host ">> Démarrage de ComfyUI-Qwen (GPU 0)..." -ForegroundColor Yellow
    docker compose -f $ComfyPath up -d
    
    Write-Host ">> Démarrage de Forge-Turbo (GPU 1)..." -ForegroundColor Yellow
    docker compose -f $ForgePath up -d
    
    Write-Host ">> Démarrage terminé." -ForegroundColor Green
    
    # Attente brève avant vérification
    Start-Sleep -Seconds 5
    Get-Container-Status
}

function Stop-Stack {
    Write-Header "ARRÊT DE LA STACK GENAI"
    
    Write-Host ">> Arrêt de Forge-Turbo..." -ForegroundColor Yellow
    docker compose -f $ForgePath down
    
    Write-Host ">> Arrêt de ComfyUI-Qwen..." -ForegroundColor Yellow
    docker compose -f $ComfyPath down
    
    Write-Host ">> Stack arrêtée." -ForegroundColor Green
}

# --- Main Logic ---

switch ($Action) {
    "start" {
        Start-Stack
        Show-VRAM-Status
        Test-Endpoints
    }
    "stop" {
        Stop-Stack
        Show-VRAM-Status
    }
    "restart" {
        Stop-Stack
        Start-Sleep -Seconds 2
        Start-Stack
        Show-VRAM-Status
        Test-Endpoints
    }
    "status" {
        Get-Container-Status
        Show-VRAM-Status
        Test-Endpoints
    }
}