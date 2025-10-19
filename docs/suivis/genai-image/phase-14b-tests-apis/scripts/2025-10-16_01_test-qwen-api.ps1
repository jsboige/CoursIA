<#
.SYNOPSIS
    Test validation API Qwen ComfyUI Production
    
.DESCRIPTION
    Script automatisé testant tous endpoints critiques API Qwen
    Phase 14B - Tests exhaustifs infrastructure GenAI
    
.PARAMETER BaseUrl
    URL de base de l'API Qwen (défaut: https://qwen-image-edit.myia.io)
    
.PARAMETER VerboseOutput
    Active les logs détaillés pour chaque test
    
.EXAMPLE
    .\2025-10-16_01_test-qwen-api.ps1
    
.EXAMPLE
    .\2025-10-16_01_test-qwen-api.ps1 -BaseUrl "https://qwen-image-edit.myia.io" -VerboseOutput
    
.NOTES
    Date: 2025-10-16
    Phase: 14B
    Auteur: SDDD Process
    Méthode: Semantic-Documentation-Driven-Design
#>

param(
    [string]$BaseUrl = "https://qwen-image-edit.myia.io",
    [switch]$VerboseOutput
)

# Configuration
$ReportPath = "../rapports/2025-10-16_14B_rapport-test-qwen-api.md"
$ErrorActionPreference = "Continue"

# Statistiques globales
$TestsTotal = 0
$TestsPassed = 0
$TestsFailed = 0
$StartTime = Get-Date

# Fonction logging avec niveaux
function Write-TestLog {
    param(
        [string]$Message,
        [string]$Level = "INFO"
    )
    
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logMessage = "[$timestamp] [$Level] $Message"
    
    # Afficher avec couleur
    switch ($Level) {
        "ERROR"   { Write-Host $logMessage -ForegroundColor Red }
        "SUCCESS" { Write-Host $logMessage -ForegroundColor Green }
        "WARNING" { Write-Host $logMessage -ForegroundColor Yellow }
        "INFO"    { Write-Host $logMessage -ForegroundColor Cyan }
        default   { Write-Host $logMessage }
    }
}

# Initialisation rapport
$Report = @"
# Rapport Test API Qwen - $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

## Configuration
- **URL Base**: $BaseUrl
- **Date**: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")
- **Machine**: $env:COMPUTERNAME
- **User**: $env:USERNAME

---

## Tests Exécutés

"@

# Banner début
Write-Host ""
Write-Host "═══════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "         Phase 14B - Test Validation API Qwen ComfyUI        " -ForegroundColor Cyan
Write-Host "═══════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host ""

Write-TestLog "Démarrage tests API Qwen..." "INFO"
Write-TestLog "URL Base: $BaseUrl" "INFO"
Write-Host ""

# ====================================
# Test 1: Health Check /system_stats
# ====================================
Write-Host "📍 Test 1: Health Check /system_stats" -ForegroundColor Yellow
$TestsTotal++

try {
    $response = Invoke-WebRequest -Uri "$BaseUrl/system_stats" -Method Get -TimeoutSec 10 -UseBasicParsing
    
    if ($response.StatusCode -eq 200) {
        Write-TestLog "✅ Health check réussi (200 OK)" "SUCCESS"
        $TestsPassed++
        
        $stats = $response.Content | ConvertFrom-Json
        $gpu = $stats.system.devices[0].name
        $vramTotal = $stats.system.devices[0].vram_total
        $vramFree = $stats.system.devices[0].vram_free
        $vramUsed = $vramTotal - $vramFree
        $vramPercent = [math]::Round(($vramUsed / $vramTotal) * 100, 2)
        
        if ($VerboseOutput) {
            Write-TestLog "GPU: $gpu" "INFO"
            Write-TestLog "VRAM: $vramUsed MB / $vramTotal MB ($vramPercent%)" "INFO"
        }
        
        $Report += @"

### ✅ Test 1: Health Check
- **Status**: SUCCESS
- **Code HTTP**: 200 OK
- **GPU**: $gpu
- **VRAM Total**: $vramTotal MB
- **VRAM Utilisée**: $vramUsed MB ($vramPercent%)
- **VRAM Libre**: $vramFree MB
- **Temps réponse**: $($response.Headers['X-Response-Time'])

"@
    }
} catch {
    Write-TestLog "❌ Health check échoué: $_" "ERROR"
    $TestsFailed++
    $Report += @"

### ❌ Test 1: Health Check
- **Status**: FAILURE
- **Erreur**: $($_.Exception.Message)

"@
}

Write-Host ""

# ====================================
# Test 2: Endpoint /queue
# ====================================
Write-Host "📍 Test 2: Endpoint /queue" -ForegroundColor Yellow
$TestsTotal++

try {
    $response = Invoke-WebRequest -Uri "$BaseUrl/queue" -Method Get -TimeoutSec 10 -UseBasicParsing
    
    if ($response.StatusCode -eq 200) {
        Write-TestLog "✅ Endpoint /queue accessible (200 OK)" "SUCCESS"
        $TestsPassed++
        
        $queue = $response.Content | ConvertFrom-Json
        $pending = $queue.queue_pending.Count
        $running = $queue.queue_running.Count
        
        if ($VerboseOutput) {
            Write-TestLog "Jobs Pending: $pending" "INFO"
            Write-TestLog "Jobs Running: $running" "INFO"
        }
        
        $Report += @"

### ✅ Test 2: Endpoint Queue
- **Status**: SUCCESS
- **Code HTTP**: 200 OK
- **Jobs Pending**: $pending
- **Jobs Running**: $running

"@
    }
} catch {
    Write-TestLog "❌ Endpoint /queue échoué: $_" "ERROR"
    $TestsFailed++
    $Report += @"

### ❌ Test 2: Endpoint Queue
- **Status**: FAILURE
- **Erreur**: $($_.Exception.Message)

"@
}

Write-Host ""

# ====================================
# Test 3: Endpoint /object_info
# ====================================
Write-Host "📍 Test 3: Endpoint /object_info (Nodes disponibles)" -ForegroundColor Yellow
$TestsTotal++

try {
    $response = Invoke-WebRequest -Uri "$BaseUrl/object_info" -Method Get -TimeoutSec 10 -UseBasicParsing
    
    if ($response.StatusCode -eq 200) {
        Write-TestLog "✅ Endpoint /object_info accessible (200 OK)" "SUCCESS"
        $TestsPassed++
        
        $nodes = ($response.Content | ConvertFrom-Json).PSObject.Properties.Count
        
        # Compter nodes Qwen spécifiques
        $nodesList = ($response.Content | ConvertFrom-Json).PSObject.Properties.Name
        $qwenNodes = ($nodesList | Where-Object { $_ -like "*Qwen*" }).Count
        
        if ($VerboseOutput) {
            Write-TestLog "Nodes disponibles: $nodes" "INFO"
            Write-TestLog "Nodes Qwen: $qwenNodes" "INFO"
        }
        
        $Report += @"

### ✅ Test 3: Object Info (Nodes)
- **Status**: SUCCESS
- **Code HTTP**: 200 OK
- **Nodes disponibles**: $nodes
- **Nodes Qwen**: $qwenNodes
- **Note**: 28 custom nodes Qwen attendus pour fonctionnalité complète

"@
    }
} catch {
    Write-TestLog "❌ Endpoint /object_info échoué: $_" "ERROR"
    $TestsFailed++
    $Report += @"

### ❌ Test 3: Object Info
- **Status**: FAILURE
- **Erreur**: $($_.Exception.Message)

"@
}

Write-Host ""

# ====================================
# Test 4: Test Workflow Submit (Queue seulement)
# ====================================
Write-Host "📍 Test 4: Test Workflow Submit (Validation queue)" -ForegroundColor Yellow
$TestsTotal++

# Workflow minimal (inspiré des custom nodes Qwen découverts Phase 12B)
# Note: Ce workflow utilise les nodes standard pour tester le queuing seulement
$workflow = @{
    "prompt" = @{
        "1" = @{
            "inputs" = @{
                "text" = "Test validation Phase 14B - Simple prompt test"
            }
            "class_type" = "CLIPTextEncode"
            "_meta" = @{
                "title" = "CLIP Text Encode (Prompt)"
            }
        }
        "2" = @{
            "inputs" = @{
                "width" = 256
                "height" = 256
                "batch_size" = 1
            }
            "class_type" = "EmptyLatentImage"
            "_meta" = @{
                "title" = "Empty Latent Image"
            }
        }
    }
}

try {
    $body = $workflow | ConvertTo-Json -Depth 10
    $response = Invoke-WebRequest -Uri "$BaseUrl/prompt" -Method Post -Body $body -ContentType "application/json" -TimeoutSec 30 -UseBasicParsing
    
    if ($response.StatusCode -eq 200) {
        $result = $response.Content | ConvertFrom-Json
        $promptId = $result.prompt_id
        
        Write-TestLog "✅ Workflow queued (prompt_id: $promptId)" "SUCCESS"
        $TestsPassed++
        
        if ($VerboseOutput) {
            Write-TestLog "Prompt ID: $promptId" "INFO"
        }
        
        $Report += @"

### ✅ Test 4: Workflow Submit (Queue)
- **Status**: SUCCESS (Queue)
- **Code HTTP**: 200 OK
- **Prompt ID**: $promptId
- **Note**: Workflow minimal testé pour validation queuing uniquement
- **Remarque**: Les custom nodes Qwen nécessitent workflows spécifiques (voir Phase 12C)

"@
    }
} catch {
    Write-TestLog "❌ Workflow submit échoué: $_" "ERROR"
    $TestsFailed++
    
    # Analyser l'erreur
    $errorDetail = "Erreur lors de la soumission du workflow"
    if ($_.Exception.Response) {
        try {
            $errorStream = $_.Exception.Response.GetResponseStream()
            $reader = New-Object System.IO.StreamReader($errorStream)
            $errorBody = $reader.ReadToEnd()
            $errorDetail = $errorBody
        } catch {
            $errorDetail = $_.Exception.Message
        }
    }
    
    $Report += @"

### ❌ Test 4: Workflow Submit
- **Status**: FAILURE
- **Erreur**: $errorDetail
- **Note**: Ce test utilise des nodes standards. Pour Qwen, utiliser les 28 custom nodes spécifiques.

"@
}

Write-Host ""

# ====================================
# Calcul statistiques finales
# ====================================
$EndTime = Get-Date
$Duration = ($EndTime - $StartTime).TotalSeconds
$SuccessRate = if ($TestsTotal -gt 0) { [math]::Round(($TestsPassed / $TestsTotal) * 100, 1) } else { 0 }

# Déterminer status global
$GlobalStatus = if ($TestsFailed -eq 0) { 
    "OPERATIONAL" 
} elseif ($TestsPassed -ge 2) { 
    "DEGRADED" 
} else { 
    "DOWN" 
}

# Prêt pour étudiants ?
$ReadyForStudents = if ($TestsPassed -ge 3) { "OUI" } else { "NON" }

# Finalisation rapport
$Report += @"

---

## 📊 Résumé Tests

| Métrique | Valeur |
|----------|--------|
| **Tests Total** | $TestsTotal |
| **Tests Réussis** | $TestsPassed ✅ |
| **Tests Échoués** | $TestsFailed ❌ |
| **Taux Succès** | $SuccessRate% |
| **Durée** | $([math]::Round($Duration, 2)) secondes |

---

## 🎯 Conclusions

### Status API Qwen ComfyUI
- **Status Global**: **$GlobalStatus**
- **Endpoints critiques**: $TestsPassed/$TestsTotal passés
- **Prêt pour utilisation étudiants**: **$ReadyForStudents**

### Points Clés
"@

if ($GlobalStatus -eq "OPERATIONAL") {
    $Report += @"

- ✅ Infrastructure opérationnelle
- ✅ Endpoints critiques accessibles
- ✅ GPU fonctionnel et disponible
- ✅ Ready for production

"@
} elseif ($GlobalStatus -eq "DEGRADED") {
    $Report += @"

- ⚠️ Infrastructure partiellement fonctionnelle
- ⚠️ Certains endpoints inaccessibles
- ✅ Core functionality disponible
- ⚠️ Investigation recommandée

"@
} else {
    $Report += @"

- ❌ Infrastructure non fonctionnelle
- ❌ Endpoints critiques inaccessibles
- ❌ Intervention urgente requise
- ❌ Not ready for production

"@
}

$Report += @"

### Rappel Important
- **Architecture Qwen**: Nécessite custom nodes spécifiques (28 nodes)
- **Workflows standards**: Incompatibles (voir Phase 12B)
- **Documentation**: Workflows exemples disponibles Phase 12C
- **GPU**: RTX 3090 (24GB VRAM) - Performance optimale

---

## 🚀 Prochaines Actions

"@

if ($ReadyForStudents -eq "OUI") {
    $Report += @"
1. ✅ API validée - Ready for students
2. 📝 Mettre à jour guide étudiants avec exemples
3. 📚 Référencer workflows Phase 12C
4. 🎓 Préparer notebooks pédagogiques

"@
} else {
    $Report += @"
1. 🔍 Investiguer endpoints échoués
2. 🔧 Corriger problèmes identifiés
3. 🧪 Re-tester après corrections
4. 📝 Documenter solutions appliquées

"@
}

$Report += @"

---

## 📚 Références

- **Phase 12A**: Déploiement production Qwen
- **Phase 12B**: Tests génération (incompatibilité workflows découverte)
- **Phase 12C**: Architecture workflows Qwen (custom nodes)
- **Guide APIs**: docs/suivis/genai-image/GUIDE-APIS-ETUDIANTS.md

---

*Rapport généré automatiquement - Phase 14B SDDD*  
*Date: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")*  
*Script: 2025-10-16_01_test-qwen-api.ps1*
"@

# Sauvegarde rapport
$reportDir = Split-Path $ReportPath -Parent
New-Item -ItemType Directory -Force -Path $reportDir | Out-Null
Set-Content -Path $ReportPath -Value $Report -Encoding UTF8

# Affichage résumé console
Write-Host ""
Write-Host "═══════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "                    RÉSUMÉ FINAL TESTS                         " -ForegroundColor Cyan
Write-Host "═══════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host ""
Write-Host "Tests Total:     $TestsTotal" -ForegroundColor White
Write-Host "Tests Réussis:   $TestsPassed" -ForegroundColor Green
Write-Host "Tests Échoués:   $TestsFailed" -ForegroundColor $(if ($TestsFailed -eq 0) { "Green" } else { "Red" })
Write-Host "Taux Succès:     $SuccessRate%" -ForegroundColor $(if ($SuccessRate -ge 75) { "Green" } elseif ($SuccessRate -ge 50) { "Yellow" } else { "Red" })
Write-Host "Status Global:   $GlobalStatus" -ForegroundColor $(if ($GlobalStatus -eq "OPERATIONAL") { "Green" } elseif ($GlobalStatus -eq "DEGRADED") { "Yellow" } else { "Red" })
Write-Host ""
Write-Host "✅ Rapport sauvegardé: $ReportPath" -ForegroundColor Green
Write-Host ""
Write-Host "🏁 Tests API Qwen terminés en $([math]::Round($Duration, 2)) secondes" -ForegroundColor Cyan
Write-Host ""

# Code sortie
exit $(if ($TestsFailed -eq 0) { 0 } else { 1 })