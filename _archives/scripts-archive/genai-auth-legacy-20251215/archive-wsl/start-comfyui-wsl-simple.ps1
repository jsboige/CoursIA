# Script PowerShell simplifié pour démarrer ComfyUI via WSL
# Résout le problème de permissions Docker en utilisant WSL natif

Write-Host "🚀 Démarrage ComfyUI via WSL standalone..." -ForegroundColor Green

# Lire le token directement depuis le fichier .env
try {
    $envContent = Get-Content "docker-configurations/comfyui-qwen/.env" -Raw -ErrorAction Stop
    $tokenLine = $envContent | Where-Object { $_ -match "QWEN_API_TOKEN=" }
    
    if ($tokenLine) {
        $token = ($tokenLine -split "=")[1]
        if ($token.Length -gt 10) {
            Write-Host "✅ Token Qwen trouvé: $($token.Substring(0,10))..." -ForegroundColor Green
        } else {
            Write-Host "✅ Token Qwen trouvé: $token" -ForegroundColor Green
        }
    } else {
        Write-Host "❌ Erreur: Token QWEN_API_TOKEN non trouvé dans .env" -ForegroundColor Red
        exit 1
    }
} catch {
    Write-Host "❌ Erreur lors de la lecture du fichier .env: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}

# Vérifier si WSL est disponible
try {
    $wslVersion = wsl --version
    Write-Host "✅ WSL détecté: $wslVersion" -ForegroundColor Green
} catch {
    Write-Host "❌ Erreur: WSL n'est pas disponible" -ForegroundColor Red
    exit 1
}

# Lancement du script WSL avec le token
Write-Host "🚀 Lancement du script WSL ComfyUI..." -ForegroundColor Green

try {
    $wslCommand = @"
export QWEN_API_TOKEN="$token"
export CUDA_VISIBLE_DEVICES=0
export NVIDIA_VISIBLE_DEVICES=0
export COMFYUI_PORT=8188
export COMFYUI_LISTEN=0.0.0.0
export COMFYUI_LOGIN_ENABLED=true
cd /mnt/d/Dev/CoursIA/docker-configurations/comfyui-qwen/ComfyUI
bash /mnt/d/Dev/CoursIA/scripts/comfyui-wsl-startup.sh
"@
    
    $result = wsl bash -c "$wslCommand"
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✅ ComfyUI démarré avec succès via WSL!" -ForegroundColor Green
        Write-Host "🌐 Interface web disponible sur: http://localhost:8188" -ForegroundColor Cyan
        Write-Host "🔑 Authentification activée avec token Qwen" -ForegroundColor Green
    } else {
        Write-Host "❌ Erreur lors du démarrage de ComfyUI (code: $LASTEXITCODE)" -ForegroundColor Red
    }
    
} catch {
    Write-Host "❌ Erreur critique lors du lancement WSL: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}

Write-Host "📋 Script terminé" -ForegroundColor Gray