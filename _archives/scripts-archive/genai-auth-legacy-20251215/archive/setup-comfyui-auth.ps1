# Script PowerShell pour configurer l'authentification ComfyUI
# Utilise le fichier .env pour synchroniser les credentials

param(
    [switch]$Force,
    [switch]$TestOnly,
    [string]$EnvPath = "docker-configurations/services/comfyui-qwen/.env"
)

# NOTE: Utilisation directe du fichier maître, plus de liens symboliques

Write-Host "🔐 CONFIGURATION DE L'AUTHENTIFICATION COMFYUI" -ForegroundColor Cyan
Write-Host "==========================================" -ForegroundColor Cyan

# Vérification du fichier .env
if (-not (Test-Path $EnvPath)) {
    Write-Host "❌ Fichier .env non trouvé: $EnvPath" -ForegroundColor Red
    exit 1
}

Write-Host "📁 Fichier .env trouvé: $EnvPath" -ForegroundColor Green

# Lecture des credentials
try {
    $envContent = Get-Content $EnvPath
    $username = ""
    $password = ""
    
    foreach ($line in $envContent) {
        if ($line -match "^COMFYUI_USERNAME=(.*)") {
            $username = $matches[1]
        }
        elseif ($line -match "^COMFYUI_PASSWORD=(.*)") {
            $password = $matches[1]
        }
    }
    
    if (-not $username -or -not $password) {
        Write-Host "❌ Credentials non trouvés dans le .env" -ForegroundColor Red
        exit 1
    }
    
    Write-Host "📝 Configuration trouvée:" -ForegroundColor Yellow
    Write-Host "   • Username: $username" -ForegroundColor Gray
    Write-Host "   • Password: $('*' * $password.Length)" -ForegroundColor Gray
    
} catch {
    Write-Host "❌ Erreur lecture .env: $_" -ForegroundColor Red
    exit 1
}

# Vérification du conteneur
try {
    $containerStatus = docker ps --filter "name=comfyui-qwen" --format "{{.Names}} {{.Status}}"
    if ($containerStatus -match "comfyui-qwen") {
        Write-Host "✅ Conteneur comfyui-qwen trouvé" -ForegroundColor Green
    } else {
        Write-Host "❌ Conteneur comfyui-qwen non trouvé" -ForegroundColor Red
        if (-not $Force) {
            Write-Host "🚀 Démarrage du conteneur..." -ForegroundColor Yellow
            Set-Location "docker-configurations/services/comfyui-qwen"
            docker-compose up -d
            Set-Location "../../../"
            
            Write-Host "⏳ Attente de 60s pour le démarrage..." -ForegroundColor Yellow
            Start-Sleep -Seconds 60
        }
    }
} catch {
    Write-Host "❌ Erreur vérification conteneur: $_" -ForegroundColor Red
    exit 1
}

if (-not $TestOnly) {
    # Synchronisation des credentials
    Write-Host "`n🔄 Synchronisation des credentials..." -ForegroundColor Yellow
    
    try {
        $pythonScript = "scripts/genai-auth/utils/token_synchronizer.py --sync"
        $process = Start-Process -FilePath "python" -ArgumentList $pythonScript -Wait -PassThru -NoNewWindow
        
        if ($process.ExitCode -eq 0) {
            Write-Host "✅ Synchronisation réussie" -ForegroundColor Green
        } else {
            Write-Host "❌ Échec de la synchronisation" -ForegroundColor Red
            exit 1
        }
    } catch {
        Write-Host "❌ Erreur synchronisation: $_" -ForegroundColor Red
        exit 1
    }
}

# Test de l'authentification
Write-Host "`n🔍 Test de l'authentification..." -ForegroundColor Yellow

try {
    $pythonScript = "scripts/genai-auth/validate-comfyui-auth.py"
    $process = Start-Process -FilePath "python" -ArgumentList $pythonScript -Wait -PassThru -NoNewWindow
    
    if ($process.ExitCode -eq 0) {
        Write-Host "✅ Authentification validée avec succès" -ForegroundColor Green
    } else {
        Write-Host "⚠️ Authentification nécessite des ajustements" -ForegroundColor Yellow
    }
} catch {
    Write-Host "❌ Erreur test authentification: $_" -ForegroundColor Red
    exit 1
}

# Rapport final
Write-Host "`n" + "="*60 -ForegroundColor Cyan
Write-Host "📊 RAPPORT DE CONFIGURATION" -ForegroundColor Cyan
Write-Host "="*60 -ForegroundColor Cyan

Write-Host "📱 URL d'accès: http://localhost:8188/" -ForegroundColor Gray
Write-Host "👤 Username: $username" -ForegroundColor Gray
Write-Host "🔑 Password: $password" -ForegroundColor Gray

Write-Host "`n📋 INSTRUCTIONS:" -ForegroundColor Yellow
Write-Host "1. Accédez à http://localhost:8188/" -ForegroundColor Gray
Write-Host "2. Utilisez les identifiants ci-dessus pour vous connecter" -ForegroundColor Gray
Write-Host "3. L'authentification est maintenant configurée et fonctionnelle" -ForegroundColor Gray

Write-Host "`n✨ Configuration terminée!" -ForegroundColor Green