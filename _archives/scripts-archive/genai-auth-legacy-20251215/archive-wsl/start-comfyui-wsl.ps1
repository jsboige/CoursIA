# Script PowerShell pour démarrer ComfyUI via WSL
# Résout le problème de permissions Docker en utilisant WSL natif

param(
    [string]$QwenApiToken = $env:QWEN_API_TOKEN
)

Write-Host "🚀 Démarrage ComfyUI via WSL standalone..." -ForegroundColor Green
Write-Host "📝 Utilisation du script WSL pour contourner les problèmes Docker" -ForegroundColor Yellow

if ([string]::IsNullOrEmpty($QwenApiToken)) {
    Write-Host "❌ Erreur: La variable d'environnement QWEN_API_TOKEN n'est pas définie" -ForegroundColor Red
    Write-Host "💡 Veuillez définir la variable QWEN_API_TOKEN avec votre token d'authentification" -ForegroundColor Yellow
    exit 1
}

Write-Host "🔑 Token Qwen détecté: $($QwenApiToken.Substring(0,10))..." -ForegroundColor Green

# Vérifier si WSL est disponible
try {
    $wslVersion = wsl --version
    Write-Host "✅ WSL détecté: $wslVersion" -ForegroundColor Green
} catch {
    Write-Host "❌ Erreur: WSL n'est pas disponible" -ForegroundColor Red
    exit 1
}

# Vérifier si le répertoire ComfyUI existe
$comfyuiPath = "/mnt/d/Dev/CoursIA/docker-configurations/comfyui-qwen/ComfyUI"
Write-Host "📂 Vérification du répertoire: $comfyuiPath" -ForegroundColor Cyan

try {
    $wslCheck = wsl -e "test -d '$comfyuiPath' && echo 'EXISTS' || echo 'NOT_FOUND'"
    
    if ($wslCheck -eq "EXISTS") {
        Write-Host "✅ Répertoire ComfyUI trouvé dans WSL" -ForegroundColor Green
    } else {
        Write-Host "⚠️  Répertoire ComfyUI non trouvé, utilisation du répertoire temporaire" -ForegroundColor Yellow
    }
} catch {
    Write-Host "❌ Erreur lors de la vérification du répertoire WSL" -ForegroundColor Red
    exit 1
}

# Préparation et lancement du script WSL
Write-Host "🚀 Lancement du script WSL ComfyUI..." -ForegroundColor Green

try {
    # Exporter les variables d'environnement pour WSL
    $envScript = @"
export QWEN_API_TOKEN="$QwenApiToken"
export CUDA_VISIBLE_DEVICES=0
export NVIDIA_VISIBLE_DEVICES=0
export COMFYUI_PORT=8188
export COMFYUI_LISTEN=0.0.0.0
export COMFYUI_LOGIN_ENABLED=true
"@
    
    # Écrire le script d'environnement temporaire
    $tempEnvScript = "/tmp/comfyui-env.sh"
    $envScript | Out-File -FilePath $tempEnvScript -Encoding UTF8
    
    # Copier vers WSL et exécuter
    wsl bash -c "source $tempEnvScript && cd /mnt/d/Dev/CoursIA && bash scripts/comfyui-wsl-startup.sh"
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✅ ComfyUI démarré avec succès via WSL!" -ForegroundColor Green
        Write-Host "🌐 Interface web disponible sur: http://localhost:8188" -ForegroundColor Cyan
        Write-Host "🔑 Authentification activée avec token Qwen" -ForegroundColor Green
    } else {
        Write-Host "❌ Erreur lors du démarrage de ComfyUI (code: $LASTEXITCODE)" -ForegroundColor Red
    }
    
    # Nettoyer le script temporaire
    wsl bash -c "rm -f $tempEnvScript"
    
} catch {
    Write-Host "❌ Erreur critique lors du lancement WSL: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}

Write-Host "📋 Script terminé" -ForegroundColor Gray