# Finalisation Complète Phase 12A - Script Maître
# Date: 2025-10-15 23:54 UTC
# Objectif: Orchestration complète des tests SSL, API et UI

param(
    [switch]$SkipSSL,
    [switch]$SkipAPI,
    [switch]$SkipPlaywright,
    [switch]$OpenBrowsers,
    [string]$OutputDir = "d:/Dev/CoursIA/docs/genai-suivis"
)

$ErrorActionPreference = "Continue"

Write-Host "`n╔════════════════════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║      FINALISATION COMPLÈTE PHASE 12A - Script Maître     ║" -ForegroundColor Cyan
Write-Host "║          SSL + API + Tests Visuels + Documentation       ║" -ForegroundColor Cyan
Write-Host "╚════════════════════════════════════════════════════════════╝`n" -ForegroundColor Cyan

$startTime = Get-Date
$executionLog = @{
    StartTime = $startTime.ToString("yyyy-MM-dd HH:mm:ss")
    Phases = @{}
    Results = @{}
}

# ============================================================================
# PHASE 1: Tests SSL et HTTPS
# ============================================================================

if (-not $SkipSSL) {
    Write-Host "`n╔═══════════════════════════════════════════════════════════╗" -ForegroundColor Green
    Write-Host "║  PHASE 1: Validation SSL et Tests HTTPS                  ║" -ForegroundColor Green
    Write-Host "╚═══════════════════════════════════════════════════════════╝`n" -ForegroundColor Green
    
    $phase1Start = Get-Date
    try {
        $sslScript = "$OutputDir/2025-10-15_23_validation-ssl-https.ps1"
        if (Test-Path $sslScript) {
            Write-Host "▶️ Exécution: validation-ssl-https.ps1" -ForegroundColor Cyan
            & $sslScript -OutputDir $OutputDir
            $executionLog.Phases.Phase1_SSL = @{
                Status = "Success"
                Duration = ((Get-Date) - $phase1Start).TotalSeconds
            }
            Write-Host "`n✅ Phase 1 terminée avec succès" -ForegroundColor Green
        }
        else {
            Write-Host "⚠️ Script SSL non trouvé: $sslScript" -ForegroundColor Yellow
            $executionLog.Phases.Phase1_SSL = @{ Status = "Skipped"; Reason = "Script not found" }
        }
    }
    catch {
        Write-Host "❌ Erreur Phase 1: $($_.Exception.Message)" -ForegroundColor Red
        $executionLog.Phases.Phase1_SSL = @{
            Status = "Failed"
            Error = $_.Exception.Message
            Duration = ((Get-Date) - $phase1Start).TotalSeconds
        }
    }
    
    Start-Sleep -Seconds 2
}
else {
    Write-Host "⏭️ Phase 1 (SSL) ignorée" -ForegroundColor Yellow
    $executionLog.Phases.Phase1_SSL = @{ Status = "Skipped"; Reason = "User requested" }
}

# ============================================================================
# PHASE 2: Tests API
# ============================================================================

if (-not $SkipAPI) {
    Write-Host "`n╔═══════════════════════════════════════════════════════════╗" -ForegroundColor Green
    Write-Host "║  PHASE 2: Tests API OpenAI Compatible                    ║" -ForegroundColor Green
    Write-Host "╚═══════════════════════════════════════════════════════════╝`n" -ForegroundColor Green
    
    $phase2Start = Get-Date
    try {
        $apiScript = "$OutputDir/2025-10-15_23_test-api-openai.ps1"
        if (Test-Path $apiScript) {
            Write-Host "▶️ Exécution: test-api-openai.ps1" -ForegroundColor Cyan
            & $apiScript -OutputDir $OutputDir
            $executionLog.Phases.Phase2_API = @{
                Status = "Success"
                Duration = ((Get-Date) - $phase2Start).TotalSeconds
            }
            Write-Host "`n✅ Phase 2 terminée avec succès" -ForegroundColor Green
        }
        else {
            Write-Host "⚠️ Script API non trouvé: $apiScript" -ForegroundColor Yellow
            $executionLog.Phases.Phase2_API = @{ Status = "Skipped"; Reason = "Script not found" }
        }
    }
    catch {
        Write-Host "❌ Erreur Phase 2: $($_.Exception.Message)" -ForegroundColor Red
        $executionLog.Phases.Phase2_API = @{
            Status = "Failed"
            Error = $_.Exception.Message
            Duration = ((Get-Date) - $phase2Start).TotalSeconds
        }
    }
    
    Start-Sleep -Seconds 2
}
else {
    Write-Host "⏭️ Phase 2 (API) ignorée" -ForegroundColor Yellow
    $executionLog.Phases.Phase2_API = @{ Status = "Skipped"; Reason = "User requested" }
}

# ============================================================================
# PHASE 2.5: Ouverture navigateurs pour validation visuelle
# ============================================================================

if ($OpenBrowsers) {
    Write-Host "`n╔═══════════════════════════════════════════════════════════╗" -ForegroundColor Green
    Write-Host "║  PHASE 2.5: Validation Visuelle (Navigateurs)            ║" -ForegroundColor Green
    Write-Host "╚═══════════════════════════════════════════════════════════╝`n" -ForegroundColor Green
    
    try {
        Write-Host "🌐 Ouverture ComfyUI HTTPS..." -ForegroundColor Cyan
        Start-Process "https://qwen-image-edit.myia.io"
        Start-Sleep -Seconds 2
        
        Write-Host "🌐 Ouverture Forge HTTPS..." -ForegroundColor Cyan
        Start-Process "https://turbo.stable-diffusion-webui-forge.myia.io"
        
        Write-Host "`n⏳ Temps de chargement suggéré: 30 secondes" -ForegroundColor Yellow
        Write-Host "   Vérifiez manuellement:" -ForegroundColor Gray
        Write-Host "   - ✅ Certificat SSL valide (cadenas vert)" -ForegroundColor Gray
        Write-Host "   - ✅ Interface ComfyUI complète" -ForegroundColor Gray
        Write-Host "   - ✅ Interface Forge intacte" -ForegroundColor Gray
        
        $executionLog.Phases.Phase2_5_Browsers = @{ Status = "Opened"; Note = "Manual validation required" }
    }
    catch {
        Write-Host "⚠️ Erreur ouverture navigateurs: $($_.Exception.Message)" -ForegroundColor Yellow
        $executionLog.Phases.Phase2_5_Browsers = @{ Status = "Failed"; Error = $_.Exception.Message }
    }
}

# ============================================================================
# PHASE 3: Tests Playwright (si environnement disponible)
# ============================================================================

if (-not $SkipPlaywright) {
    Write-Host "`n╔═══════════════════════════════════════════════════════════╗" -ForegroundColor Green
    Write-Host "║  PHASE 3: Tests Playwright (Automatisés)                 ║" -ForegroundColor Green
    Write-Host "╚═══════════════════════════════════════════════════════════╝`n" -ForegroundColor Green
    
    $phase3Start = Get-Date
    
    # Vérifier si environnement Playwright existe
    $playwrightPath = "D:\Production\playwright-tests"
    
    if (Test-Path "$playwrightPath\package.json") {
        Write-Host "✅ Environnement Playwright trouvé: $playwrightPath" -ForegroundColor Green
        
        try {
            Push-Location $playwrightPath
            
            Write-Host "`n📦 Mise à jour dépendances npm..." -ForegroundColor Cyan
            npm install --silent 2>&1 | Out-Null
            
            Write-Host "🧪 Exécution tests Playwright..." -ForegroundColor Cyan
            $testOutput = npm test 2>&1
            Write-Host $testOutput
            
            # Vérifier screenshots générés
            if (Test-Path "$playwrightPath\results") {
                $screenshots = Get-ChildItem "$playwrightPath\results" -Recurse -Include *.png
                
                if ($screenshots.Count -gt 0) {
                    Write-Host "`n📸 $($screenshots.Count) screenshots générés:" -ForegroundColor Green
                    $screenshots | ForEach-Object {
                        Write-Host "   - $($_.Name) ($([math]::Round($_.Length/1KB, 2)) KB)" -ForegroundColor Gray
                    }
                    
                    # Copier dans docs
                    $docsScreenshots = "$OutputDir/screenshots"
                    if (-not (Test-Path $docsScreenshots)) {
                        New-Item -ItemType Directory -Path $docsScreenshots -Force | Out-Null
                    }
                    
                    Copy-Item "$playwrightPath\results\*.png" -Destination $docsScreenshots -Force
                    Write-Host "`n✅ Screenshots copiés dans: $docsScreenshots" -ForegroundColor Green
                }
            }
            
            Pop-Location
            
            $executionLog.Phases.Phase3_Playwright = @{
                Status = "Success"
                Duration = ((Get-Date) - $phase3Start).TotalSeconds
                ScreenshotsGenerated = $screenshots.Count
            }
            
            Write-Host "`n✅ Phase 3 terminée avec succès" -ForegroundColor Green
        }
        catch {
            Pop-Location
            Write-Host "❌ Erreur Phase 3: $($_.Exception.Message)" -ForegroundColor Red
            $executionLog.Phases.Phase3_Playwright = @{
                Status = "Failed"
                Error = $_.Exception.Message
                Duration = ((Get-Date) - $phase3Start).TotalSeconds
            }
        }
    }
    else {
        Write-Host "⚠️ Environnement Playwright non trouvé: $playwrightPath" -ForegroundColor Yellow
        Write-Host "   Pour installer: Exécutez 2025-10-15_13_test-playwright-ui.ps1" -ForegroundColor Gray
        $executionLog.Phases.Phase3_Playwright = @{ Status = "Skipped"; Reason = "Environment not found" }
    }
}
else {
    Write-Host "⏭️ Phase 3 (Playwright) ignorée" -ForegroundColor Yellow
    $executionLog.Phases.Phase3_Playwright = @{ Status = "Skipped"; Reason = "User requested" }
}

# ============================================================================
# PHASE 4: Génération Documentation
# ============================================================================

Write-Host "`n╔═══════════════════════════════════════════════════════════╗" -ForegroundColor Green
Write-Host "║  PHASE 4: Compilation Résultats et Documentation         ║" -ForegroundColor Green
Write-Host "╚═══════════════════════════════════════════════════════════╝`n" -ForegroundColor Green

$endTime = Get-Date
$totalDuration = ($endTime - $startTime).TotalSeconds

$executionLog.EndTime = $endTime.ToString("yyyy-MM-dd HH:mm:ss")
$executionLog.TotalDuration = $totalDuration

# Charger résultats des tests
$resultsAvailable = @{}

if (Test-Path "$OutputDir/certificat-ssl-info.json") {
    $resultsAvailable.SSLCertificate = Get-Content "$OutputDir/certificat-ssl-info.json" | ConvertFrom-Json
}

if (Test-Path "$OutputDir/2025-10-15_23_rapport-validation-ssl-https.json") {
    $resultsAvailable.HTTPSTests = Get-Content "$OutputDir/2025-10-15_23_rapport-validation-ssl-https.json" | ConvertFrom-Json
}

if (Test-Path "$OutputDir/2025-10-15_23_rapport-test-api.json") {
    $resultsAvailable.APITests = Get-Content "$OutputDir/2025-10-15_23_rapport-test-api.json" | ConvertFrom-Json
}

$executionLog.Results = $resultsAvailable

# Sauvegarder log d'exécution
$logPath = "$OutputDir/2025-10-15_23_execution-log-final.json"
$executionLog | ConvertTo-Json -Depth 10 | Out-File $logPath -Encoding UTF8

Write-Host "✅ Log d'exécution sauvegardé: 2025-10-15_23_execution-log-final.json" -ForegroundColor Green

# ============================================================================
# RÉSUMÉ FINAL
# ============================================================================

Write-Host "`n`n╔════════════════════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║              RÉSUMÉ FINALISATION PHASE 12A                ║" -ForegroundColor Cyan
Write-Host "╚════════════════════════════════════════════════════════════╝`n" -ForegroundColor Cyan

Write-Host "⏱️ Durée totale: $([math]::Round($totalDuration, 2)) secondes" -ForegroundColor White

Write-Host "`n📊 Phases exécutées:" -ForegroundColor Yellow
foreach ($phase in $executionLog.Phases.Keys | Sort-Object) {
    $status = $executionLog.Phases[$phase].Status
    $icon = switch ($status) {
        "Success" { "✅" }
        "Failed" { "❌" }
        "Skipped" { "⏭️" }
        default { "⚠️" }
    }
    $color = switch ($status) {
        "Success" { "Green" }
        "Failed" { "Red" }
        "Skipped" { "Yellow" }
        default { "Gray" }
    }
    Write-Host "   $icon $phase : $status" -ForegroundColor $color
}

Write-Host "`n📋 Fichiers générés:" -ForegroundColor Yellow
$generatedFiles = @(
    "certificat-ssl-info.json",
    "2025-10-15_23_rapport-validation-ssl-https.json",
    "2025-10-15_23_rapport-test-api.json",
    "2025-10-15_23_execution-log-final.json"
)

foreach ($file in $generatedFiles) {
    if (Test-Path "$OutputDir/$file") {
        $size = (Get-Item "$OutputDir/$file").Length
        Write-Host "   ✅ $file ($([math]::Round($size/1KB, 2)) KB)" -ForegroundColor Green
    }
    else {
        Write-Host "   ⚠️ $file (non généré)" -ForegroundColor Yellow
    }
}

Write-Host "`n🎯 Prochaines étapes:" -ForegroundColor Cyan
Write-Host "   1. Vérifier les rapports JSON générés" -ForegroundColor Gray
Write-Host "   2. Créer la documentation API markdown" -ForegroundColor Gray
Write-Host "   3. Mettre à jour le rapport d'exécution final" -ForegroundColor Gray
Write-Host "   4. Finaliser le checkpoint sémantique" -ForegroundColor Gray

Write-Host "`n✅ Finalisation automatisée terminée`n" -ForegroundColor Green