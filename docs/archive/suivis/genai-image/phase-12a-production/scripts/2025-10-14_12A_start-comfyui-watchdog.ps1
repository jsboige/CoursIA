# ComfyUI Startup Script avec Monitoring
# Phase 12A: Production ComfyUI + Qwen Image-Edit
# Date: 2025-10-14

# === CONFIGURATION ===
$WORKSPACE = "\\wsl.localhost\Ubuntu\home\jesse\SD\workspace\comfyui-qwen\ComfyUI"
$PORT = 8188
$LOG_DIR = ".\logs\comfyui-production"
$MAX_RETRIES = 5

# Créer répertoire logs (relatif au dépôt)
if (-not (Test-Path $LOG_DIR)) {
    New-Item -ItemType Directory -Path $LOG_DIR -Force | Out-Null
}

# === FONCTIONS ===

function Write-Log {
    param($Message)
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logFile = "$LOG_DIR\startup-$(Get-Date -Format 'yyyy-MM-dd').log"
    "$timestamp - $Message" | Tee-Object -FilePath $logFile -Append
    Write-Host $Message
}

function Test-ComfyUIRunning {
    try {
        $response = Invoke-WebRequest -Uri "http://localhost:$PORT/system_stats" -UseBasicParsing -TimeoutSec 5
        return $response.StatusCode -eq 200
    }
    catch {
        return $false
    }
}

function Start-ComfyUI {
    Write-Log "🚀 Démarrage ComfyUI sur GPU RTX 3090..."
    
    $wslCommand = @"
cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI && \
source venv/bin/activate && \
CUDA_VISIBLE_DEVICES=0 nohup python main.py \
  --listen 0.0.0.0 \
  --port 8188 \
  --preview-method auto \
  --use-split-cross-attention \
  > /home/jesse/SD/workspace/comfyui-qwen/comfyui.log 2>&1 &
"@

    wsl bash -c $wslCommand
    
    Write-Log "⏳ Commande lancée, attente démarrage (60s)..."
    Start-Sleep -Seconds 60
    
    if (Test-ComfyUIRunning) {
        Write-Log "✅ ComfyUI démarré avec succès sur port $PORT"
        return $true
    }
    else {
        Write-Log "❌ Échec démarrage ComfyUI"
        return $false
    }
}

function Stop-ComfyUI {
    Write-Log "⏹️ Arrêt ComfyUI..."
    wsl bash -c "pkill -f 'python main.py.*8188'"
    Start-Sleep -Seconds 5
}

# Fonction monitoring continue
function Start-Monitoring {
    Write-Log "📊 Démarrage monitoring continu..."
    
    while ($true) {
        if (-not (Test-ComfyUIRunning)) {
            Write-Log "⚠️ ComfyUI non accessible, redémarrage automatique..."
            Stop-ComfyUI
            Start-Sleep -Seconds 10
            
            $retry = 0
            $started = $false
            
            while ($retry -lt $MAX_RETRIES -and -not $started) {
                $started = Start-ComfyUI
                if (-not $started) {
                    $retry++
                    Write-Log "❌ Tentative $retry/$MAX_RETRIES échouée, pause 30s..."
                    Start-Sleep -Seconds 30
                }
            }
            
            if (-not $started) {
                Write-Log "🚨 CRITIQUE: Échec redémarrage après $MAX_RETRIES tentatives"
                # TODO: Envoyer alerte (email, webhook, Teams, etc.)
            }
        }
        else {
            # Service OK, log périodique
            Write-Log "✅ ComfyUI opérationnel sur port $PORT"
        }
        
        # Vérifier toutes les 2 minutes
        Start-Sleep -Seconds 120
    }
}

# === MAIN ===

Write-Log "╔════════════════════════════════════════════════════════╗"
Write-Log "║    ComfyUI Watchdog Script - Phase 12A Production      ║"
Write-Log "╚════════════════════════════════════════════════════════╝"

# Vérifier si déjà en cours
if (Test-ComfyUIRunning) {
    Write-Log "ℹ️ ComfyUI déjà en cours sur port $PORT"
}
else {
    # Premier démarrage
    Write-Log "🔄 Premier démarrage de ComfyUI..."
    if (Start-ComfyUI) {
        Write-Log "✅ Premier démarrage réussi"
    }
    else {
        Write-Log "❌ Échec premier démarrage"
        exit 1
    }
}

# Lancer monitoring si demandé
if ($args[0] -eq "-monitor") {
    Start-Monitoring
}
else {
    Write-Log "✅ Mode démarrage uniquement (pas de monitoring continu)"
    Write-Log "💡 Pour monitoring continu: .\2025-10-14_12A_start-comfyui-watchdog.ps1 -monitor"
}

Write-Log "═══════════════════════════════════════════════════════"