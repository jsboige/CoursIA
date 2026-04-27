# Script PowerShell pour exécuter le diagnostic d'authentification ComfyUI
# Utilise le script Python consolidé pour l'analyse et la correction

param(
    [switch]$AutoFix,
    [switch]$Verbose,
    [int]$Timeout = 300
)

Write-Host "🚀 DÉMARRAGE DU DIAGNOSTIC D'AUTHENTIFICATION COMFYUI" -ForegroundColor Cyan
Write-Host "=================================================" -ForegroundColor Cyan

# Vérification de l'environnement
Write-Host "🔍 Vérification de l'environnement..." -ForegroundColor Yellow

# Vérification de Python
try {
    $pythonVersion = python --version 2>&1
    Write-Host "✅ Python: $pythonVersion" -ForegroundColor Green
} catch {
    Write-Host "❌ Python non trouvé" -ForegroundColor Red
    exit 1
}

# Vérification de Docker
try {
    $dockerVersion = docker --version
    Write-Host "✅ Docker: $dockerVersion" -ForegroundColor Green
} catch {
    Write-Host "❌ Docker non trouvé" -ForegroundColor Red
    exit 1
}

# Vérification du conteneur
try {
    $containerStatus = docker ps --filter "name=comfyui-qwen" --format "table {{.Names}}\t{{.Status}}"
    if ($containerStatus -match "comfyui-qwen") {
        Write-Host "✅ Conteneur comfyui-qwen trouvé" -ForegroundColor Green
    } else {
        Write-Host "❌ Conteneur comfyui-qwen non trouvé" -ForegroundColor Red
        Write-Host "🔄 Démarrage du conteneur..." -ForegroundColor Yellow
        
        Set-Location "docker-configurations/comfyui-qwen"
        docker-compose up -d
        Set-Location "../../"
        
        Write-Host "⏳ Attente de 60s pour le démarrage complet..." -ForegroundColor Yellow
        Start-Sleep -Seconds 60
    }
} catch {
    Write-Host "❌ Erreur vérification conteneur: $_" -ForegroundColor Red
    exit 1
}

# Exécution du diagnostic Python
Write-Host "`n🔍 Exécution du diagnostic complet..." -ForegroundColor Yellow

$scriptPath = "scripts/genai-auth/core/validate_genai_ecosystem.py"
$pythonCmd = "python"

if ($Verbose) {
    $pythonCmd += " -v"
}

try {
    Set-Location $PSScriptRoot/../..
    
    Write-Host "📝 Exécution: $pythonCmd $scriptPath" -ForegroundColor Gray
    
    $process = Start-Process -FilePath $pythonCmd -ArgumentList $scriptPath -Wait -PassThru -NoNewWindow
    
    if ($process.ExitCode -eq 0) {
        Write-Host "`n🎉 DIAGNOSTIC TERMINÉ AVEC SUCCÈS" -ForegroundColor Green
        Write-Host "L'authentification ComfyUI est fonctionnelle" -ForegroundColor Green
    } else {
        Write-Host "`n⚠️ DIAGNOSTIC TERMINÉ AVEC DES PROBLÈMES" -ForegroundColor Yellow
        Write-Host "Veuillez consulter les recommandations ci-dessus" -ForegroundColor Yellow
    }
    
} catch {
    Write-Host "❌ Erreur lors de l'exécution du diagnostic: $_" -ForegroundColor Red
    exit 1
}

# Tests supplémentaires si demandé
if ($AutoFix) {
    Write-Host "`n🔧 MODE AUTO-FIX ACTIVÉ" -ForegroundColor Yellow
    Write-Host "Application des corrections automatiques..." -ForegroundColor Yellow
    
    # Test final de l'interface web
    try {
        Write-Host "🌐 Test final de l'interface web..." -ForegroundColor Yellow
        
        $response = Invoke-WebRequest -Uri "http://localhost:8188/" -TimeoutSec 10 -UseBasicParsing
        
        if ($response.Content -match "login|auth|password") {
            Write-Host "✅ Interface web protégée - Authentification requise" -ForegroundColor Green
        } else {
            Write-Host "❌ Interface web non protégée" -ForegroundColor Red
            Write-Host "🔄 Redémarrage du conteneur avec configuration complète..." -ForegroundColor Yellow
            
            Set-Location "docker-configurations/comfyui-qwen"
            docker-compose restart
            Set-Location "../../"
            
            Write-Host "⏳ Attente de 30s..." -ForegroundColor Yellow
            Start-Sleep -Seconds 30
        }
        
    } catch {
        Write-Host "❌ Erreur test interface web: $_" -ForegroundColor Red
    }
}

# Rapport de synthèse
Write-Host "`n" + "="*60 -ForegroundColor Cyan
Write-Host "📊 RAPPORT DE SYNTHÈSE" -ForegroundColor Cyan
Write-Host "="*60 -ForegroundColor Cyan

Write-Host "Script exécuté: $scriptPath" -ForegroundColor Gray
Write-Host "Mode Auto-Fix: $AutoFix" -ForegroundColor Gray
Write-Host "Mode Verbose: $Verbose" -ForegroundColor Gray
Write-Host "Timeout: $Timeout secondes" -ForegroundColor Gray

Write-Host "`n📁 Fichiers de configuration:" -ForegroundColor Yellow
Write-Host "  - docker-configurations/comfyui-qwen/docker-compose.yml" -ForegroundColor Gray
Write-Host "  - scripts/genai-auth/diagnose_comfyui_auth.py" -ForegroundColor Gray

Write-Host "`n🔍 Prochaines étapes recommandées:" -ForegroundColor Yellow
Write-Host "  1. Consulter le rapport de diagnostic ci-dessus" -ForegroundColor Gray
Write-Host "  2. Appliquer les corrections si nécessaire" -ForegroundColor Gray
Write-Host "  3. Tester l'accès à http://localhost:8188/" -ForegroundColor Gray
Write-Host "  4. Valider que l'authentification est bien demandée" -ForegroundColor Gray

Write-Host "`n✨ Diagnostic terminé!" -ForegroundColor Green