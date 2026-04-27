#!/usr/bin/env pwsh
<#
.SYNOPSIS
    Script de restauration du fichier .env pour ComfyUI-Login

.DESCRIPTION
    Ce script restaure le fichier .env complet en se basant sur la source de vérité
    et résout les problèmes d'incohérence des tokens d'authentification.

.PARAMETER Backup
    Crée une sauvegarde du fichier .env existant

.PARAMETER Validate
    Valide le fichier .env reconstruit

.PARAMETER Source
    Chemin vers le fichier de configuration source (optionnel)

.PARAMETER Restart
    Redémarre automatiquement le service ComfyUI après reconstruction

.EXAMPLE
    .\restore-env-comfyui.ps1 -Backup -Validate -Restart

.EXAMPLE
    .\restore-env-comfyui.ps1 -Source "custom-config.json"

.NOTES
    Auteur: Roo Debug Mode
    Date: 27 novembre 2025
    Version: 1.0
#>

param(
    [switch]$Backup = $false,
    [switch]$Validate = $true,
    [string]$Source = $null,
    [switch]$Restart = $false
)

# Configuration
$ErrorActionPreference = "Stop"
$ProgressPreference = "Continue"

# Couleurs pour l'affichage
$Colors = @{
    Info = "Cyan"
    Success = "Green"
    Warning = "Yellow"
    Error = "Red"
    Reconstruct = "Magenta"
    Validate = "Blue"
}

function Write-ColorMessage {
    param(
        [string]$Message,
        [string]$Level = "Info"
    )
    
    $color = $Colors[$Level]
    if ($color) {
        Write-Host $Message -ForegroundColor $color
    } else {
        Write-Host $Message
    }
}

function Test-Prerequisites {
    Write-ColorMessage "🔍 VÉRIFICATION DES PRÉREQUIS" "Info"
    
    # Vérifier Python
    try {
        $pythonVersion = python --version 2>$null
        Write-ColorMessage "✅ Python trouvé: $pythonVersion" "Success"
    } catch {
        Write-ColorMessage "❌ Python non trouvé. Veuillez installer Python 3.8+" "Error"
        return $false
    }
    
    # Vérifier les fichiers critiques
    $requiredFiles = @(
        ".secrets/comfyui_auth_tokens.conf",
        "scripts/genai-auth/utils/reconstruct_env.py",
        "docker-configurations/services/comfyui-qwen/.env"
    )
    
    foreach ($file in $requiredFiles) {
        if (Test-Path $file) {
            Write-ColorMessage "✅ Fichier trouvé: $file" "Success"
        } else {
            Write-ColorMessage "⚠️ Fichier manquant: $file" "Warning"
        }
    }
    
    return $true
}

function Backup-CurrentEnv {
    if (-not $Backup) {
        return $true
    }
    
    Write-ColorMessage "💾 CRÉATION DE SAUVEGARDE" "Info"
    
    $envPath = "docker-configurations/services/comfyui-qwen/.env"
    if (Test-Path $envPath) {
        # Créer le répertoire _backups s'il n'existe pas
        $backupDir = "_backups"
        if (-not (Test-Path $backupDir)) {
            New-Item -Path $backupDir -ItemType Directory -Force
        }
        
        $timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
        $backupPath = "$backupDir/.env.backup.$timestamp"
        
        try {
            Copy-Item $envPath $backupPath
            Write-ColorMessage "✅ Sauvegarde créée: $backupPath" "Success"
            return $true
        } catch {
            Write-ColorMessage "❌ Erreur création sauvegarde: $_" "Error"
            return $false
        }
    } else {
        Write-ColorMessage "ℹ️ Aucun fichier .env existant à sauvegarder" "Info"
        return $true
    }
}

function Reconstruct-EnvFile {
    Write-ColorMessage "🔧 RECONSTRUCTION DU FICHIER .ENV" "Reconstruct"
    
    $pythonScript = "scripts/genai-auth/utils/reconstruct_env.py"
    $arguments = @()
    
    if ($Backup) {
        $arguments += "--backup"
    }
    
    if ($Validate) {
        $arguments += "--validate"
    }
    
    if ($Source) {
        $arguments += "--source"
        $arguments += $Source
    }
    
    try {
        Write-ColorMessage "Exécution: python $pythonScript $($arguments -join ' ')" "Info"
        $result = & python $pythonScript $arguments
        $exitCode = $LASTEXITCODE
        
        if ($exitCode -eq 0) {
            Write-ColorMessage "✅ Reconstruction terminée avec succès" "Success"
            return $true
        } else {
            Write-ColorMessage "❌ Échec de la reconstruction (code: $exitCode)" "Error"
            return $false
        }
    } catch {
        Write-ColorMessage "❌ Erreur lors de la reconstruction: $_" "Error"
        return $false
    }
}

function Validate-EnvFile {
    if (-not $Validate) {
        return $true
    }
    
    Write-ColorMessage "✔️ VALIDATION DU FICHIER .ENV" "Validate"
    
    $envPath = "docker-configurations/services/comfyui-qwen/.env"
    if (-not (Test-Path $envPath)) {
        Write-ColorMessage "❌ Fichier .env introuvable pour validation" "Error"
        return $false
    }
    
    try {
        $content = Get-Content $envPath -Raw
        
        # Vérifications essentielles
        $requiredVars = @(
            "CIVITAI_TOKEN",
            "HF_TOKEN",
            "QWEN_API_TOKEN",
            "COMFYUI_BEARER_TOKEN",
            "COMFYUI_LOGIN_ENABLED",
            "COMFYUI_USERNAME",
            "COMFYUI_PASSWORD"
        )
        
        $missingVars = @()
        foreach ($var in $requiredVars) {
            if ($content -notmatch "$var=") {
                $missingVars += $var
            }
        }
        
        if ($missingVars.Count -gt 0) {
            Write-ColorMessage "❌ Variables manquantes: $($missingVars -join ', ')" "Error"
            return $false
        }
        
        # Vérifier le format du token bcrypt
        if ($content -match 'COMFYUI_BEARER_TOKEN=([^\r\n]+)') {
            $token = $matches[1]
            if ($token -notmatch '^\$2b\$12\$.{53}$') {
                Write-ColorMessage "❌ Token bcrypt invalide: $($token.Substring(0, 20))..." "Error"
                return $false
            }
            Write-ColorMessage "✅ Token bcrypt valide" "Success"
        } else {
            Write-ColorMessage "❌ Token COMFYUI_BEARER_TOKEN introuvable" "Error"
            return $false
        }
        
        Write-ColorMessage "✅ Fichier .env validé avec succès" "Success"
        return $true
        
    } catch {
        Write-ColorMessage "❌ Erreur validation fichier .env: $_" "Error"
        return $false
    }
}

function Restart-ComfyUIService {
    if (-not $Restart) {
        return $true
    }
    
    Write-ColorMessage "🔄 REDÉMARRAGE DU SERVICE COMFYUI" "Info"
    
    $serviceDir = "docker-configurations/services/comfyui-qwen"
    
    try {
        Set-Location $serviceDir
        
        Write-ColorMessage "Arrêt du service..." "Info"
        & docker-compose down
        
        Write-ColorMessage "Démarrage du service..." "Info"
        & docker-compose up -d
        
        $exitCode = $LASTEXITCODE
        if ($exitCode -eq 0) {
            Write-ColorMessage "✅ Service ComfyUI redémarré avec succès" "Success"
            
            # Attendre quelques secondes pour le démarrage
            Write-ColorMessage "Attente du démarrage du service..." "Info"
            Start-Sleep -Seconds 10
            
            # Tester la connectivité
            try {
                $response = Invoke-WebRequest -Uri "http://localhost:8188/" -TimeoutSec 30 -UseBasicParsing
                if ($response.StatusCode -eq 200) {
                    Write-ColorMessage "✅ Service ComfyUI accessible (HTTP 200)" "Success"
                } else {
                    Write-ColorMessage "⚠️ Service ComfyUI répond avec code: $($response.StatusCode)" "Warning"
                }
            } catch {
                Write-ColorMessage "⚠️ Service ComfyUI pas encore accessible (normal au démarrage)" "Warning"
            }
            
            return $true
        } else {
            Write-ColorMessage "❌ Échec du redémarrage (code: $exitCode)" "Error"
            return $false
        }
    } catch {
        Write-ColorMessage "❌ Erreur lors du redémarrage: $_" "Error"
        return $false
    }
}

function Show-NextSteps {
    Write-ColorMessage "`n🎯 PROCHAINES ÉTAPES RECOMMANDÉES" "Info"
    Write-ColorMessage "1. Tester l'authentification API:" "Info"
    Write-ColorMessage "   curl -H 'Authorization: Bearer \$COMFYUI_BEARER_TOKEN' http://localhost:8188/system_stats" "Cyan"
    Write-ColorMessage "`n2. Valider la synchronisation complète:" "Info"
    Write-ColorMessage "   python scripts/genai-auth/utils/token_synchronizer.py --validate" "Cyan"
    Write-ColorMessage "`n3. Consulter les logs du service:" "Info"
    Write-ColorMessage "   cd docker-configurations/services/comfyui-qwen" "Cyan"
    Write-ColorMessage "   docker-compose logs -f" "Cyan"
    Write-ColorMessage "`n4. Accéder à l'interface web:" "Info"
    Write-ColorMessage "   http://localhost:8188" "Cyan"
}

# Programme principal
function Main {
    Write-ColorMessage "🚀 RESTAURATION DU FICHIER .ENV POUR COMFYUI-LOGIN" "Info"
    Write-ColorMessage "Date: $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')" "Info"
    Write-ColorMessage "Version: 1.0" "Info"
    Write-ColorMessage "=" * 60 "Info"
    
    # Étape 1: Vérification des prérequis
    if (-not (Test-Prerequisites)) {
        Write-ColorMessage "❌ Échec de la vérification des prérequis" "Error"
        exit 1
    }
    
    # Étape 2: Sauvegarde du fichier existant
    if (-not (Backup-CurrentEnv)) {
        Write-ColorMessage "❌ Échec de la sauvegarde" "Error"
        exit 1
    }
    
    # Étape 3: Reconstruction du fichier .env
    if (-not (Reconstruct-EnvFile)) {
        Write-ColorMessage "❌ Échec de la reconstruction" "Error"
        exit 1
    }
    
    # Étape 4: Validation du fichier reconstruit
    if (-not (Validate-EnvFile)) {
        Write-ColorMessage "❌ Échec de la validation" "Error"
        exit 1
    }
    
    # Étape 5: Redémarrage du service (optionnel)
    if ($Restart) {
        if (-not (Restart-ComfyUIService)) {
            Write-ColorMessage "❌ Échec du redémarrage du service" "Error"
            exit 1
        }
    }
    
    # Succès
    Write-ColorMessage "`n🎉 RESTAURATION TERMINÉE AVEC SUCCÈS" "Success"
    Write-ColorMessage "Le fichier .env a été reconstruit et validé" "Success"
    
    # Afficher les prochaines étapes
    Show-NextSteps
}

# Exécution principale
try {
    Main
    exit 0
} catch {
    Write-ColorMessage "`n❌ ERREUR FATALE: $_" "Error"
    Write-ColorMessage "Stack trace:" "Error"
    Write-ColorMessage $_.ScriptStackTrace "Error"
    exit 1
}