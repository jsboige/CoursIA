<#
.SYNOPSIS
    Génère des comptes utilisateurs et des tokens Bearer pour ComfyUI-Login.

.DESCRIPTION
    Ce script PowerShell automatise la création de comptes utilisateurs pour le custom node
    ComfyUI-Login. Pour chaque utilisateur spécifié, il génère un mot de passe aléatoire et
    sécurisé, le hache en utilisant l'algorithme bcrypt, puis crée le fichier de configuration
    utilisateur (.token) attendu par ComfyUI-Login.

    Le script affiche ensuite les mots de passe en clair pour permettre leur stockage manuel
    sécurisé (par exemple, dans un gestionnaire de mots de passe) et génère un fichier .env
    prêt à l'emploi contenant les tokens.

.PARAMETER Usernames
    Une liste de noms d'utilisateur pour lesquels créer des comptes et des tokens.
    Ce paramètre est obligatoire.

.PARAMETER OutputPath
    Le chemin du répertoire où les fichiers .token et le fichier .env seront sauvegardés.
    Ce répertoire correspond généralement au dossier d'installation de ComfyUI-Login dans le volume Docker.
    La valeur par défaut est "./.secrets".

.EXAMPLE
    # Générer des tokens pour deux utilisateurs et sauvegarder dans le répertoire par défaut
    ./generate-bearer-tokens.ps1 -Usernames "qwen-api-user", "forge-api-user"

.EXAMPLE
    # Générer un token pour un utilisateur et spécifier un répertoire de sortie
    ./generate-bearer-tokens.ps1 -Usernames "prod-user" -OutputPath "D:\docker-volumes\comfyui-login-data"

.NOTES
    - Le script nécessite l'installation du module PowerShell 'Bcrypt' depuis la PowerShell Gallery.
      (Install-Module -Name Bcrypt -Scope CurrentUser)
    - Les mots de passe générés sont affichés en clair à l'écran. Assurez-vous d'exécuter ce script
      dans un environnement sécurisé.
    - Créé lors de la reconstruction post-incident (2025-10-22).
#>

[CmdletBinding()]
param(
    [Parameter(Mandatory=$true)]
    [string[]]$Usernames,

    [Parameter(Mandatory=$false)]
    [string]$OutputPath = ".\.secrets"
)

# --- Configuration ---
$ErrorActionPreference = "Stop"
$LogPrefix = "[GENERATE-TOKENS]"
$PasswordLength = 32
$BcryptWorkFactor = 12

# --- Fonctions ---

function Write-Log {
    param ([string]$Message)
    Write-Host "$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss') - $LogPrefix $Message"
}

function Install-BcryptModule {
    Write-Log "Vérification de la disponibilité du module 'Bcrypt'..."
    if (-not (Get-Module -ListAvailable -Name Bcrypt)) {
        Write-Log "ℹ️ Le module 'Bcrypt' n'est pas installé. Tentative d'installation..."
        try {
            Install-Module -Name Bcrypt -Scope CurrentUser -Repository PSGallery -Force -Confirm:$false
            Write-Log "✅ Module 'Bcrypt' installé avec succès."
        } catch {
            Write-Error "❌ ERREUR: Impossible d'installer le module 'Bcrypt' depuis la PowerShell Gallery."
            Write-Error "Veuillez l'installer manuellement: Install-Module -Name Bcrypt -Scope CurrentUser"
            exit 1
        }
    } else {
        Write-Log "✅ Module 'Bcrypt' déjà installé."
    }
    Import-Module Bcrypt
}

function Generate-SecurePassword {
    param ([int]$length)
    $charSet = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#$%^&*()_+'
    $password = -join ((0..($length - 1)) | ForEach-Object { $charSet[(Get-Random -Minimum 0 -Maximum $charSet.Length)] })
    return $password
}

# --- Script Principal ---

Write-Log "Démarrage de la génération de tokens Bearer..."

try {
    # Installer le module Bcrypt si nécessaire
    Install-BcryptModule

    # Créer le répertoire de sortie s'il n'existe pas
    if (-not (Test-Path -Path $OutputPath -PathType Container)) {
        Write-Log "ℹ️ Le répertoire de sortie '$OutputPath' n'existe pas. Création..."
        New-Item -Path $OutputPath -ItemType Directory -Force | Out-Null
    }

    $generatedCredentials = @{}
    $envFileContent = @()

    foreach ($username in $Usernames) {
        Write-Log "--- Traitement de l'utilisateur: '$username' ---"

        # Générer un mot de passe sécurisé
        $plainPassword = Generate-SecurePassword -length $PasswordLength
        Write-Log "Mot de passe généré (longueur: $PasswordLength)."

        # Hacher le mot de passe avec bcrypt
        Write-Log "Hachage du mot de passe avec bcrypt (work factor: $BcryptWorkFactor)..."
        $hashedPassword = Get-BcryptHash -Password $plainPassword -WorkFactor $BcryptWorkFactor
        
        # Créer le fichier .token
        $tokenFilePath = Join-Path -Path $OutputPath -ChildPath "$username.token"
        Write-Log "Création du fichier token à '$tokenFilePath'..."
        Set-Content -Path $tokenFilePath -Value $hashedPassword -Encoding UTF8
        
        # Stocker les informations pour l'affichage final
        $generatedCredentials[$username] = $plainPassword
        
        # Préparer la ligne pour le fichier .env
        $envVarName = ($username -replace '-', '_').ToUpper() + "_TOKEN"
        $envFileContent += "$envVarName=$plainPassword"

        Write-Log "✅ Compte pour '$username' créé avec succès."
    }

    # Écrire le fichier .env
    $envFilePath = Join-Path -Path $OutputPath -ChildPath ".env.generated"
    Write-Log "Écriture des tokens dans le fichier '$envFilePath'..."
    Set-Content -Path $envFilePath -Value $envFileContent -Encoding UTF8

    # Afficher les résultats
    Write-Host "`n" + ("="*60)
    Write-Host "🎉 GÉNÉRATION TERMINÉE AVEC SUCCÈS 🎉"
    Write-Host ("="*60)
    Write-Host "Les mots de passe suivants ont été générés. Stockez-les en lieu sûr!"
    Write-Host "Un fichier '$envFilePath' a été créé avec ces tokens."
    Write-Host ("-"*60)

    foreach ($user in $generatedCredentials.Keys) {
        Write-Host "  Utilisateur : $user"
        Write-Host "  Mot de passe: $($generatedCredentials[$user])"
        Write-Host ("-"*60)
    }
    
    Write-Log "Opération terminée."

} catch {
    Write-Error "❌ ERREUR: Une erreur critique est survenue."
    Write-Error $_.Exception.Message
    exit 1
}

exit 0