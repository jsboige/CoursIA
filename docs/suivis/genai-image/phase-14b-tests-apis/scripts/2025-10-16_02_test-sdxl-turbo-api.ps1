<#
.SYNOPSIS
    Test validation API SD XL Turbo Forge Production
    
.DESCRIPTION
    Script automatisé testant tous endpoints critiques API Forge
    Phase 14B - Tests exhaustifs infrastructure GenAI
    
.PARAMETER BaseUrl
    URL de base de l'API SD XL Turbo (défaut: https://turbo.stable-diffusion-webui-forge.myia.io)
    
.PARAMETER VerboseOutput
    Active les logs détaillés pour chaque test
    
.EXAMPLE
    .\2025-10-16_02_test-sdxl-turbo-api.ps1
    
.EXAMPLE
    .\2025-10-16_02_test-sdxl-turbo-api.ps1 -BaseUrl "https://turbo.stable-diffusion-webui-forge.myia.io" -VerboseOutput
    
.NOTES
    Date: 2025-10-16
    Phase: 14B
    Auteur: SDDD Process
    Méthode: Semantic-Documentation-Driven-Design
#>

param(
    [string]$BaseUrl = "https://turbo.stable-diffusion-webui-forge.myia.io",
    [switch]$VerboseOutput
)

# Configuration
$ReportPath = "../rapports/2025-10-16_14B_rapport-test-sdxl-turbo-api.md"
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
# Rapport Test API SD XL Turbo - $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")

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
Write-Host "       Phase 14B - Test Validation API SD XL Turbo Forge      " -ForegroundColor Cyan
Write-Host "═══════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host ""

Write-TestLog "Démarrage tests API SD XL Turbo..." "INFO"
Write-TestLog "URL Base: $BaseUrl" "INFO"
Write-Host ""

# ====================================
# Test 1: Health Check (Page d'accueil)
# ====================================
Write-Host "📍 Test 1: Health Check /" -ForegroundColor Yellow
$TestsTotal++

try {
    $response = Invoke-WebRequest -Uri $BaseUrl -Method Get -TimeoutSec 10 -UseBasicParsing
    
    if ($response.StatusCode -eq 200) {
        Write-TestLog "✅ Health check réussi (200 OK)" "SUCCESS"
        $TestsPassed++
        
        $contentLength = $response.Content.Length
        
        if ($VerboseOutput) {
            Write-TestLog "Content Length: $contentLength bytes" "INFO"
        }
        
        $Report += @"

### ✅ Test 1: Health Check
- **Status**: SUCCESS
- **Code HTTP**: 200 OK
- **Content Length**: $contentLength bytes
- **Note**: Interface Gradio accessible

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
# Test 2: API REST /sdapi/v1/sd-models
# ====================================
Write-Host "📍 Test 2: Endpoint /sdapi/v1/sd-models" -ForegroundColor Yellow
$TestsTotal++

try {
    $response = Invoke-WebRequest -Uri "$BaseUrl/sdapi/v1/sd-models" -Method Get -TimeoutSec 10 -UseBasicParsing
    
    if ($response.StatusCode -eq 200) {
        Write-TestLog "✅ Endpoint models accessible (200 OK)" "SUCCESS"
        $TestsPassed++
        
        $models = $response.Content | ConvertFrom-Json
        $modelCount = $models.Count
        
        # Chercher modèle Turbo
        $turboModel = $models | Where-Object { $_.title -like "*turbo*" -or $_.model_name -like "*turbo*" }
        $turboFound = $turboModel -ne $null
        $turboName = if ($turboFound) { $turboModel[0].title } else { "Non trouvé" }
        
        if ($VerboseOutput) {
            Write-TestLog "Modèles disponibles: $modelCount" "INFO"
            Write-TestLog "Modèle Turbo: $turboName" "INFO"
        }
        
        $Report += @"

### ✅ Test 2: Endpoint Models
- **Status**: SUCCESS
- **Code HTTP**: 200 OK
- **Modèles disponibles**: $modelCount
- **Modèle Turbo trouvé**: $(if ($turboFound) { "✅ Oui" } else { "❌ Non" })
- **Nom modèle**: $turboName

"@
    }
} catch {
    Write-TestLog "❌ Endpoint /sd-models échoué: $_" "ERROR"
    $TestsFailed++
    $Report += @"

### ❌ Test 2: Endpoint Models
- **Status**: FAILURE
- **Erreur**: $($_.Exception.Message)

"@
}

Write-Host ""

# ====================================
# Test 3: API REST /sdapi/v1/samplers
# ====================================
Write-Host "📍 Test 3: Endpoint /sdapi/v1/samplers" -ForegroundColor Yellow
$TestsTotal++

try {
    $response = Invoke-WebRequest -Uri "$BaseUrl/sdapi/v1/samplers" -Method Get -TimeoutSec 10 -UseBasicParsing
    
    if ($response.StatusCode -eq 200) {
        Write-TestLog "✅ Endpoint samplers accessible (200 OK)" "SUCCESS"
        $TestsPassed++
        
        $samplers = $response.Content | ConvertFrom-Json
        $samplerCount = $samplers.Count
        
        # Vérifier sampler recommandé pour Turbo
        $dpmSampler = $samplers | Where-Object { $_.name -like "*DPM*" }
        $dpmFound = $dpmSampler -ne $null
        
        if ($VerboseOutput) {
            Write-TestLog "Samplers disponibles: $samplerCount" "INFO"
            if ($dpmFound) {
                Write-TestLog "DPM sampler trouvé (recommandé Turbo)" "INFO"
            }
        }
        
        $Report += @"

### ✅ Test 3: Endpoint Samplers
- **Status**: SUCCESS
- **Code HTTP**: 200 OK
- **Samplers disponibles**: $samplerCount
- **DPM sampler (Turbo)**: $(if ($dpmFound) { "✅ Disponible" } else { "⚠️ Non trouvé" })

"@
    }
} catch {
    Write-TestLog "❌ Endpoint /samplers échoué: $_" "ERROR"
    $TestsFailed++
    $Report += @"

### ❌ Test 3: Endpoint Samplers
- **Status**: FAILURE
- **Erreur**: $($_.Exception.Message)

"@
}

Write-Host ""

# ====================================
# Test 4: Test Génération Image (txt2img)
# ====================================
Write-Host "📍 Test 4: Génération Image Test (txt2img)" -ForegroundColor Yellow
$TestsTotal++

# Payload optimisé pour SDXL Turbo
$payload = @{
    "prompt" = "A simple test image of a red sphere on white background, photorealistic"
    "negative_prompt" = "blurry, low quality, distorted"
    "steps" = 4  # Turbo = 4 steps optimal
    "width" = 256
    "height" = 256
    "cfg_scale" = 2.0  # Turbo = low CFG scale
    "sampler_name" = "DPM++ SDE"
    "batch_size" = 1
    "save_images" = $false
} | ConvertTo-Json

try {
    Write-TestLog "Envoi requête génération (peut prendre 10-30s)..." "INFO"
    $response = Invoke-WebRequest -Uri "$BaseUrl/sdapi/v1/txt2img" -Method Post -Body $payload -ContentType "application/json" -TimeoutSec 60 -UseBasicParsing
    
    if ($response.StatusCode -eq 200) {
        Write-TestLog "✅ Génération réussie (200 OK)" "SUCCESS"
        $TestsPassed++
        
        $result = $response.Content | ConvertFrom-Json
        $imageGenerated = $result.images.Count -gt 0
        $imageCount = $result.images.Count
        
        # Extraire info du result
        $infoJson = if ($result.info) { $result.info | ConvertFrom-Json } else { $null }
        $generationTime = if ($infoJson -and $infoJson.job_timestamp) { 
            "~$([math]::Round([decimal]$infoJson.job_timestamp, 1))s" 
        } else { 
            "N/A" 
        }
        
        if ($VerboseOutput) {
            Write-TestLog "Images générées: $imageCount" "INFO"
            Write-TestLog "Temps génération: $generationTime" "INFO"
        }
        
        $Report += @"

### ✅ Test 4: Génération Image (txt2img)
- **Status**: SUCCESS
- **Code HTTP**: 200 OK
- **Images générées**: $imageCount
- **Temps génération**: $generationTime
- **Configuration Turbo**:
  - Steps: 4
  - CFG Scale: 2.0
  - Sampler: DPM++ SDE
  - Résolution: 256x256
- **Note**: SDXL Turbo optimisé pour génération rapide (4 steps)

"@
    }
} catch {
    Write-TestLog "❌ Génération image échouée: $_" "ERROR"
    $TestsFailed++
    
    # Analyser l'erreur
    $errorDetail = "Erreur lors de la génération"
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

### ❌ Test 4: Génération Image
- **Status**: FAILURE
- **Erreur**: $errorDetail
- **Note**: Vérifier modèle chargé et configuration Turbo

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

### Status API SD XL Turbo Forge
- **Status Global**: **$GlobalStatus**
- **Endpoints critiques**: $TestsPassed/$TestsTotal passés
- **Prêt pour utilisation étudiants**: **$ReadyForStudents**

### Points Clés
"@

if ($GlobalStatus -eq "OPERATIONAL") {
    $Report += @"

- ✅ Infrastructure opérationnelle
- ✅ Endpoints critiques accessibles
- ✅ Génération images fonctionnelle
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

### Avantages SDXL Turbo
- **Vitesse**: Génération en 4 steps (vs 20-50 standard)
- **Qualité**: Comparable SDXL standard
- **Efficacité**: CFG scale faible (2.0) pour rapidité
- **Use case**: Prototypage rapide, itération design

### Comparaison avec Qwen
| Aspect | Qwen Image-Edit | SD XL Turbo |
|--------|-----------------|-------------|
| **Type** | Multimodal (VL) | Text-to-Image |
| **Édition** | ✅ Avancée | ❌ Non |
| **Vitesse** | Modérée | ⚡ Très rapide (4 steps) |
| **Qualité** | Haute fidélité | Haute qualité |
| **Use case** | Édition précise | Génération rapide |
| **Complexité** | Custom nodes | API standard |

---

## 🚀 Prochaines Actions

"@

if ($ReadyForStudents -eq "OUI") {
    $Report += @"
1. ✅ API validée - Ready for students
2. 📝 Mettre à jour guide étudiants avec exemples
3. 📚 Créer notebooks exemples txt2img
4. 🎓 Documenter cas d'usage Turbo vs Standard

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

- **Phase 14 Audit**: SD XL Turbo découvert opérationnel
- **Container**: myia-turbo-supervisor-1 (Docker)
- **Modèle**: turbovisionxlSuperFastXLBasedOnNew v4.31
- **GPU**: RTX 3090 (GPU 1) - 24GB VRAM
- **API**: Compatible Automatic1111/Forge
- **Guide APIs**: docs/suivis/genai-image/GUIDE-APIS-ETUDIANTS.md

---

## 🎓 Exemples d'Utilisation Étudiants

### Python (requests)
\`\`\`python
import requests
import base64

url = "$BaseUrl/sdapi/v1/txt2img"
payload = {
    "prompt": "Your creative prompt here",
    "negative_prompt": "blurry, low quality",
    "steps": 4,  # Turbo optimal
    "width": 512,
    "height": 512,
    "cfg_scale": 2.0,
    "sampler_name": "DPM++ SDE"
}

response = requests.post(url, json=payload)
result = response.json()

# Sauvegarder image
image_data = base64.b64decode(result['images'][0])
with open('output.png', 'wb') as f:
    f.write(image_data)
\`\`\`

### cURL
\`\`\`bash
curl -X POST "$BaseUrl/sdapi/v1/txt2img" \\
  -H "Content-Type: application/json" \\
  -d '{
    "prompt": "Beautiful landscape",
    "steps": 4,
    "cfg_scale": 2.0,
    "width": 512,
    "height": 512
  }'
\`\`\`

---

*Rapport généré automatiquement - Phase 14B SDDD*  
*Date: $(Get-Date -Format "yyyy-MM-dd HH:mm:ss")*  
*Script: 2025-10-16_02_test-sdxl-turbo-api.ps1*
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
Write-Host "🏁 Tests API SD XL Turbo terminés en $([math]::Round($Duration, 2)) secondes" -ForegroundColor Cyan
Write-Host ""

# Code sortie
exit $(if ($TestsFailed -eq 0) { 0 } else { 1 })