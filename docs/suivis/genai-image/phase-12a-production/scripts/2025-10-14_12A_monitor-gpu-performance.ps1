# Script de Monitoring GPU Performance pour ComfyUI
# Phase 12A: Production ComfyUI + Qwen Image-Edit
# Date: 2025-10-14

$LOG_DIR = ".\logs\comfyui-production"
$LOG_FILE = "$LOG_DIR\gpu-monitoring-$(Get-Date -Format 'yyyy-MM-dd').csv"
$ALERT_VRAM_THRESHOLD = 90  # Pourcentage
$ALERT_TEMP_THRESHOLD = 80  # Degrés Celsius
$CHECK_INTERVAL = 30        # Secondes

# Créer répertoire logs si nécessaire
if (-not (Test-Path $LOG_DIR)) {
    New-Item -ItemType Directory -Path $LOG_DIR -Force | Out-Null
}

# Créer header CSV si nouveau fichier
if (-not (Test-Path $LOG_FILE)) {
    "Timestamp,GPU,MemoryUsed_MB,MemoryTotal_MB,MemoryPercent,Temperature_C,Utilization_Percent,PowerDraw_W,Status" | 
        Out-File -FilePath $LOG_FILE -Encoding UTF8
}

function Write-ColorLog {
    param(
        [string]$Message,
        [string]$Color = "White"
    )
    Write-Host $Message -ForegroundColor $Color
}

function Get-GPUStats {
    try {
        # GPU 1 = RTX 3090 (PyTorch index 0)
        $gpu1Raw = wsl nvidia-smi --query-gpu=memory.used,memory.total,temperature.gpu,utilization.gpu,power.draw `
            --format=csv,noheader,nounits -i 1
        
        if ($gpu1Raw) {
            $parts = $gpu1Raw -split ','
            
            $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
            $memUsed = [int]$parts[0].Trim()
            $memTotal = [int]$parts[1].Trim()
            $memPercent = [math]::Round(($memUsed / $memTotal) * 100, 2)
            $temp = [int]$parts[2].Trim()
            $util = [int]$parts[3].Trim()
            $power = [decimal]$parts[4].Trim()
            
            # Déterminer statut
            $status = "OK"
            if ($memPercent -gt $ALERT_VRAM_THRESHOLD) {
                $status = "ALERT_VRAM"
            }
            if ($temp -gt $ALERT_TEMP_THRESHOLD) {
                $status = "ALERT_TEMP"
            }
            if ($memPercent -gt $ALERT_VRAM_THRESHOLD -and $temp -gt $ALERT_TEMP_THRESHOLD) {
                $status = "CRITICAL"
            }
            
            # Log CSV
            "$timestamp,RTX_3090,$memUsed,$memTotal,$memPercent,$temp,$util,$power,$status" | 
                Out-File -FilePath $LOG_FILE -Append -Encoding UTF8
            
            # Display avec couleurs
            $displayColor = "Green"
            $icon = "✅"
            
            if ($status -eq "ALERT_VRAM") {
                $displayColor = "Yellow"
                $icon = "⚠️"
            }
            elseif ($status -eq "ALERT_TEMP") {
                $displayColor = "Yellow"
                $icon = "🌡️"
            }
            elseif ($status -eq "CRITICAL") {
                $displayColor = "Red"
                $icon = "🚨"
            }
            
            Write-ColorLog "$icon [$timestamp] GPU RTX 3090" $displayColor
            Write-Host "   VRAM: $memUsed/$memTotal MB ($memPercent%)" -ForegroundColor White
            Write-Host "   Temp: $temp°C | Util: $util% | Power: $power W" -ForegroundColor White
            
            # Alertes spécifiques
            if ($memPercent -gt $ALERT_VRAM_THRESHOLD) {
                Write-ColorLog "   ⚠️ ALERTE: VRAM > $ALERT_VRAM_THRESHOLD% ($memPercent%)" "Yellow"
            }
            if ($temp -gt $ALERT_TEMP_THRESHOLD) {
                Write-ColorLog "   🌡️ ALERTE: Température > $ALERT_TEMP_THRESHOLD°C ($temp°C)" "Red"
            }
            
            Write-Host ""
            
            return @{
                MemoryPercent = $memPercent
                Temperature = $temp
                Status = $status
            }
        }
        else {
            Write-ColorLog "❌ Erreur: nvidia-smi n'a pas retourné de données" "Red"
            return $null
        }
    }
    catch {
        Write-ColorLog "❌ Erreur lors de la lecture GPU: $_" "Red"
        return $null
    }
}

function Test-ComfyUIRunning {
    try {
        $response = Invoke-WebRequest -Uri "http://localhost:8188/system_stats" -UseBasicParsing -TimeoutSec 5
        return $response.StatusCode -eq 200
    }
    catch {
        return $false
    }
}

# === MAIN ===

Write-Host ""
Write-Host "╔════════════════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║     GPU Performance Monitoring - Phase 12A            ║" -ForegroundColor Cyan
Write-Host "╚════════════════════════════════════════════════════════╝" -ForegroundColor Cyan
Write-Host ""
Write-ColorLog "🎮 GPU Target: RTX 3090 (24GB VRAM)" "Cyan"
Write-ColorLog "📊 Logs: $LOG_FILE" "Cyan"
Write-ColorLog "⏱️ Intervalle: $CHECK_INTERVAL secondes" "Cyan"
Write-ColorLog "⚠️ Seuils: VRAM > $ALERT_VRAM_THRESHOLD%, Temp > $ALERT_TEMP_THRESHOLD°C" "Yellow"
Write-Host ""
Write-ColorLog "Appuyez sur Ctrl+C pour arrêter" "Gray"
Write-Host ""
Write-Host "═══════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host ""

$iteration = 0
while ($true) {
    $iteration++
    
    # Vérifier statut ComfyUI
    $comfyRunning = Test-ComfyUIRunning
    if ($comfyRunning) {
        Write-ColorLog "✅ ComfyUI: Opérationnel" "Green"
    }
    else {
        Write-ColorLog "⚠️ ComfyUI: Non accessible" "Yellow"
    }
    
    # Récupérer stats GPU
    $stats = Get-GPUStats
    
    # Stats périodiques (toutes les 10 itérations = ~5 min)
    if ($iteration % 10 -eq 0) {
        Write-Host "─────────────────────────────────────────────────────" -ForegroundColor DarkGray
        Write-ColorLog "📈 Monitoring actif depuis $($iteration * $CHECK_INTERVAL / 60) minutes" "Cyan"
        Write-ColorLog "📂 Logs disponibles: $LOG_FILE" "Gray"
        Write-Host "─────────────────────────────────────────────────────" -ForegroundColor DarkGray
        Write-Host ""
    }
    
    # Pause
    Start-Sleep -Seconds $CHECK_INTERVAL
}