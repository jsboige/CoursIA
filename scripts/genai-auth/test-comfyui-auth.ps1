<#
.SYNOPSIS
    Teste la configuration de l'authentification Bearer Token sur une API ComfyUI.

.DESCRIPTION
    Ce script PowerShell exécute une série de tests automatisés pour valider que la solution
    d'authentification ComfyUI-Login est correctement configurée et sécurise l'accès à l'API.
    Il vérifie les scénarios suivants :
    1. Accès sans token (doit retourner 401 Unauthorized).
    2. Accès avec un token invalide (doit retourner 403 Forbidden).
    3. Accès avec un token valide (doit retourner 200 OK).

    Le script génère un rapport de résultats clair et retourne un code de sortie approprié
    en fonction du succès ou de l'échec des tests.

.PARAMETER ApiUrl
    L'URL complète de l'endpoint ComfyUI à tester (ex: 'http://localhost:8888/system_stats').
    Ce paramètre est obligatoire.

.PARAMETER ValidToken
    Le token Bearer valide pour l'authentification. Ce paramètre est obligatoire.

.EXAMPLE
    # Tester une API locale avec un token valide
    ./test-comfyui-auth.ps1 -ApiUrl "http://localhost:8888/system_stats" -ValidToken "abcd1234..."

.NOTES
    - Le script utilise `Invoke-WebRequest` pour effectuer les appels HTTP.
    - Il est conçu pour être utilisé dans un pipeline CI/CD ou pour une validation manuelle.
    - Créé lors de la reconstruction post-incident (2025-10-22).
#>

[CmdletBinding()]
param(
    [Parameter(Mandatory=$true)]
    [string]$ApiUrl,

    [Parameter(Mandatory=$true)]
    [string]$ValidToken
)

# --- Configuration ---
$ErrorActionPreference = "SilentlyContinue" # Gérer les erreurs manuellement
$LogPrefix = "[AUTH-TEST]"

# --- Fonctions ---

function Write-Log {
    param ([string]$Message)
    Write-Host "$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss') - $LogPrefix $Message"
}

function Run-Test {
    param(
        [string]$TestName,
        [scriptblock]$TestAction,
        [int]$ExpectedStatusCode
    )

    Write-Log "▶️ DÉBUT: $TestName"
    $result = @{ Success = $false; Message = "" }

    try {
        $response = Invoke-Command -ScriptBlock $TestAction
        $actualStatusCode = $response.StatusCode
    } catch {
        # Gérer les erreurs de connexion (ex: 401, 403) qui lèvent des exceptions
        if ($_.Exception.Response) {
            $actualStatusCode = [int]$_.Exception.Response.StatusCode
        } else {
            $result.Message = "Erreur inattendue: $($_.Exception.Message)"
            Write-Log "❌ ÉCHEC: $TestName"
            Write-Host "   Message: $($result.Message)"
            return $result
        }
    }

    if ($actualStatusCode -eq $ExpectedStatusCode) {
        $result.Success = $true
        $result.Message = "Statut attendu ($ExpectedStatusCode) reçu."
        Write-Log "✅ SUCCÈS: $TestName"
    } else {
        $result.Message = "Échec. Attendu: $ExpectedStatusCode, Reçu: $actualStatusCode"
        Write-Log "❌ ÉCHEC: $TestName"
    }
    
    Write-Host "   Message: $($result.Message)"
    return $result
}

# --- Script Principal ---

Write-Log "Démarrage de la suite de tests d'authentification pour l'API: $ApiUrl"
$allTestsPassed = $true
$testResults = @()

# --- Test 1: Accès sans token ---
$testResults += Run-Test -TestName "Accès sans token" -TestAction {
    Invoke-WebRequest -Uri $ApiUrl -UseBasicParsing
} -ExpectedStatusCode 401

# --- Test 2: Accès avec token invalide ---
$invalidToken = "invalid-token-" + (New-Guid).ToString()
$testResults += Run-Test -TestName "Accès avec token invalide" -TestAction {
    $headers = @{ "Authorization" = "Bearer $invalidToken" }
    Invoke-WebRequest -Uri $ApiUrl -Headers $headers -UseBasicParsing
} -ExpectedStatusCode 403

# --- Test 3: Accès avec token valide ---
$testResults += Run-Test -TestName "Accès avec token valide" -TestAction {
    $headers = @{ "Authorization" = "Bearer $ValidToken" }
    Invoke-WebRequest -Uri $ApiUrl -Headers $headers -UseBasicParsing
} -ExpectedStatusCode 200

# --- Rapport Final ---
Write-Host "`n" + ("="*50)
Write-Log "RAPPORT FINAL DES TESTS"
Write-Host ("="*50)

$testResults | ForEach-Object {
    $status = if ($_.Success) { "✅ SUCCÈS" } else { "❌ ÉCHEC" }
    Write-Host ("- " + ($_.PSObject.Properties | Where-Object { $_.Name -eq 'TestName' }).Value + ": $status")
    if (-not $_.Success) {
        $allTestsPassed = $false
    }
}

Write-Host ("="*50)

if ($allTestsPassed) {
    Write-Log "🎉 Tous les tests d'authentification ont réussi!"
    exit 0
} else {
    Write-Error "🔥 Au moins un test d'authentification a échoué."
    exit 1
}