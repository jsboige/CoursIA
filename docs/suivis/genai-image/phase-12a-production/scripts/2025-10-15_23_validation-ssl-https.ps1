# Validation SSL et HTTPS - Phase 12A Finalisation
# Date: 2025-10-15 23:50 UTC
# Objectif: Tests exhaustifs SSL + HTTPS pour ComfyUI

param(
    [string]$SiteName = "qwen-image-edit.myia.io",
    [string]$BaseUrl = "https://qwen-image-edit.myia.io",
    [string]$OutputDir = "d:/Dev/CoursIA/docs/genai-suivis"
)

Write-Host "`n╔════════════════════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║     Validation SSL et HTTPS - ComfyUI Phase 12A          ║" -ForegroundColor Cyan
Write-Host "╚════════════════════════════════════════════════════════════╝`n" -ForegroundColor Cyan

# ============================================================================
# PHASE 1.1: Vérification Binding HTTPS et Certificat
# ============================================================================

Write-Host "═══ Phase 1.1: Binding HTTPS et Certificat SSL ═══`n" -ForegroundColor Yellow

try {
    Import-Module WebAdministration -ErrorAction Stop
    
    # Récupérer binding HTTPS
    $httpsBinding = Get-WebBinding -Name $SiteName -Protocol "https"
    
    if ($httpsBinding) {
        Write-Host "✅ Binding HTTPS trouvé" -ForegroundColor Green
        Write-Host "   Protocol: $($httpsBinding.protocol)" -ForegroundColor Gray
        Write-Host "   BindingInformation: $($httpsBinding.bindingInformation)" -ForegroundColor Gray
        
        # Récupérer certificat
        $certHash = $httpsBinding.certificateHash
        if ($certHash) {
            $cert = Get-ChildItem Cert:\LocalMachine\My | Where-Object { $_.Thumbprint -eq $certHash }
            
            if ($cert) {
                Write-Host "`n📜 Certificat SSL trouvé:" -ForegroundColor Green
                Write-Host "   Subject: $($cert.Subject)" -ForegroundColor White
                Write-Host "   Issuer: $($cert.Issuer)" -ForegroundColor White
                Write-Host "   Thumbprint: $($cert.Thumbprint)" -ForegroundColor Gray
                Write-Host "   Valid From: $($cert.NotBefore)" -ForegroundColor White
                Write-Host "   Valid To: $($cert.NotAfter)" -ForegroundColor White
                
                $daysRemaining = ($cert.NotAfter - (Get-Date)).Days
                $color = if ($daysRemaining -gt 30) { "Green" } elseif ($daysRemaining -gt 7) { "Yellow" } else { "Red" }
                Write-Host "   Days Remaining: $daysRemaining jours" -ForegroundColor $color
                
                # Sauvegarder informations certificat
                $certInfo = @{
                    Subject = $cert.Subject
                    Issuer = $cert.Issuer
                    Thumbprint = $cert.Thumbprint
                    ValidFrom = $cert.NotBefore.ToString("yyyy-MM-dd HH:mm:ss")
                    ValidTo = $cert.NotAfter.ToString("yyyy-MM-dd HH:mm:ss")
                    DaysRemaining = $daysRemaining
                    Timestamp = (Get-Date).ToString("yyyy-MM-dd HH:mm:ss")
                }
                
                $certInfo | ConvertTo-Json | Out-File "$OutputDir/certificat-ssl-info.json" -Encoding UTF8
                Write-Host "`n✅ Info certificat sauvegardée: certificat-ssl-info.json" -ForegroundColor Green
            }
            else {
                Write-Host "`n⚠️ Certificat non trouvé pour thumbprint: $certHash" -ForegroundColor Yellow
                $certInfo = @{ Error = "Certificat non trouvé"; Thumbprint = $certHash }
            }
        }
        else {
            Write-Host "`n⚠️ Pas de certificat associé au binding HTTPS" -ForegroundColor Yellow
            $certInfo = @{ Error = "Pas de certificat associé" }
        }
    }
    else {
        Write-Host "❌ Binding HTTPS non trouvé pour le site $SiteName" -ForegroundColor Red
        $certInfo = @{ Error = "Binding HTTPS non trouvé" }
    }
    
    # Vérifier statut site
    Write-Host "`n🌐 Statut site IIS:" -ForegroundColor Cyan
    $site = Get-Website -Name $SiteName
    Write-Host "   État: $($site.State)" -ForegroundColor $(if ($site.State -eq "Started") {"Green"} else {"Yellow"})
    
    if ($site.State -ne "Started") {
        Write-Host "   Démarrage du site..." -ForegroundColor Yellow
        Start-Website -Name $SiteName
        Start-Sleep -Seconds 2
        $site = Get-Website -Name $SiteName
        Write-Host "   Nouvel état: $($site.State)" -ForegroundColor Green
    }
}
catch {
    Write-Host "❌ Erreur lors de la vérification IIS: $($_.Exception.Message)" -ForegroundColor Red
    $certInfo = @{ Error = $_.Exception.Message }
}

# ============================================================================
# PHASE 1.2: Tests HTTPS Exhaustifs
# ============================================================================

Write-Host "`n`n═══ Phase 1.2: Tests HTTPS Exhaustifs ═══`n" -ForegroundColor Yellow

$testResults = @{
    Timestamp = (Get-Date).ToString("yyyy-MM-dd HH:mm:ss")
    BaseUrl = $BaseUrl
    Tests = @{}
}

# Test 1: curl
Write-Host "📊 Test 1: Accessibilité via curl" -ForegroundColor Cyan
try {
    $curlResponse = curl -s "$BaseUrl/system_stats" 2>&1
    if ($LASTEXITCODE -eq 0) {
        Write-Host "   ✅ Succès" -ForegroundColor Green
        $testResults.Tests.Curl = @{ Status = "Success"; Response = $curlResponse }
    }
    else {
        Write-Host "   ❌ Échec (code: $LASTEXITCODE)" -ForegroundColor Red
        $testResults.Tests.Curl = @{ Status = "Failed"; ExitCode = $LASTEXITCODE }
    }
}
catch {
    Write-Host "   ❌ Erreur: $($_.Exception.Message)" -ForegroundColor Red
    $testResults.Tests.Curl = @{ Status = "Error"; Message = $_.Exception.Message }
}

# Test 2: Invoke-WebRequest
Write-Host "`n📊 Test 2: Invoke-WebRequest" -ForegroundColor Cyan
try {
    $response = Invoke-WebRequest -Uri "$BaseUrl/system_stats" -UseBasicParsing -ErrorAction Stop
    Write-Host "   ✅ Status Code: $($response.StatusCode)" -ForegroundColor Green
    Write-Host "   ✅ Content-Type: $($response.Headers['Content-Type'])" -ForegroundColor Green
    
    $testResults.Tests.InvokeWebRequest = @{
        Status = "Success"
        StatusCode = $response.StatusCode
        ContentType = $response.Headers['Content-Type']
        ContentLength = $response.Content.Length
    }
}
catch {
    Write-Host "   ❌ Erreur: $($_.Exception.Message)" -ForegroundColor Red
    $testResults.Tests.InvokeWebRequest = @{ Status = "Error"; Message = $_.Exception.Message }
}

# Test 3: Validation certificat SSL
Write-Host "`n📊 Test 3: Validation certificat SSL (TLS)" -ForegroundColor Cyan
try {
    $req = [System.Net.WebRequest]::Create($BaseUrl)
    $req.Timeout = 10000
    $response = $req.GetResponse()
    $response.Close()
    Write-Host "   ✅ Certificat SSL valide et accepté" -ForegroundColor Green
    $testResults.Tests.SSLValidation = @{ Status = "Success"; Message = "Certificat valide" }
}
catch {
    Write-Host "   ❌ Erreur: $($_.Exception.Message)" -ForegroundColor Red
    $testResults.Tests.SSLValidation = @{ Status = "Error"; Message = $_.Exception.Message }
}

# Test 4: Mesure de latence
Write-Host "`n📊 Test 4: Mesure latence (5 requêtes)" -ForegroundColor Cyan
$latencies = @()
for ($i = 1; $i -le 5; $i++) {
    try {
        $start = Get-Date
        Invoke-WebRequest -Uri "$BaseUrl/system_stats" -UseBasicParsing -ErrorAction Stop | Out-Null
        $end = Get-Date
        $latency = ($end - $start).TotalMilliseconds
        $latencies += $latency
        Write-Host "   Test $i : $([math]::Round($latency, 2)) ms" -ForegroundColor Gray
    }
    catch {
        Write-Host "   Test $i : ÉCHEC" -ForegroundColor Red
    }
}

if ($latencies.Count -gt 0) {
    $avgLatency = ($latencies | Measure-Object -Average).Average
    $minLatency = ($latencies | Measure-Object -Minimum).Minimum
    $maxLatency = ($latencies | Measure-Object -Maximum).Maximum
    
    Write-Host "`n   ✅ Latence moyenne: $([math]::Round($avgLatency, 2)) ms" -ForegroundColor Green
    Write-Host "   📊 Min: $([math]::Round($minLatency, 2)) ms | Max: $([math]::Round($maxLatency, 2)) ms" -ForegroundColor Gray
    
    $testResults.Tests.Latency = @{
        Status = "Success"
        Average = [math]::Round($avgLatency, 2)
        Min = [math]::Round($minLatency, 2)
        Max = [math]::Round($maxLatency, 2)
        Unit = "ms"
        Samples = $latencies.Count
    }
}
else {
    Write-Host "   ❌ Aucune mesure de latence réussie" -ForegroundColor Red
    $testResults.Tests.Latency = @{ Status = "Failed"; Message = "Aucune mesure réussie" }
}

# Test 5: Endpoints multiples
Write-Host "`n📊 Test 5: Endpoints multiples" -ForegroundColor Cyan
$endpoints = @("/system_stats", "/queue", "/history")
$endpointResults = @{}

foreach ($endpoint in $endpoints) {
    try {
        $response = Invoke-WebRequest -Uri "$BaseUrl$endpoint" -UseBasicParsing -ErrorAction Stop
        Write-Host "   ✅ $endpoint : $($response.StatusCode)" -ForegroundColor Green
        $endpointResults[$endpoint] = @{ Status = $response.StatusCode; Success = $true }
    }
    catch {
        $statusCode = $_.Exception.Response.StatusCode.value__
        if ($statusCode) {
            Write-Host "   ⚠️ $endpoint : $statusCode" -ForegroundColor Yellow
            $endpointResults[$endpoint] = @{ Status = $statusCode; Success = $false }
        }
        else {
            Write-Host "   ❌ $endpoint : Erreur" -ForegroundColor Red
            $endpointResults[$endpoint] = @{ Status = "Error"; Success = $false; Message = $_.Exception.Message }
        }
    }
}

$testResults.Tests.Endpoints = $endpointResults

# ============================================================================
# Sauvegarde Résultats
# ============================================================================

Write-Host "`n`n═══ Sauvegarde Résultats ═══`n" -ForegroundColor Yellow

# Combiner certificat et tests
$fullReport = @{
    Certificate = $certInfo
    HTTPSTests = $testResults
    Summary = @{
        AllTestsPassed = ($testResults.Tests.Values | Where-Object { $_.Status -eq "Success" }).Count -eq $testResults.Tests.Count
        TotalTests = $testResults.Tests.Count
        SuccessfulTests = ($testResults.Tests.Values | Where-Object { $_.Status -eq "Success" }).Count
    }
}

$reportPath = "$OutputDir/2025-10-15_23_rapport-validation-ssl-https.json"
$fullReport | ConvertTo-Json -Depth 10 | Out-File $reportPath -Encoding UTF8

Write-Host "✅ Rapport complet sauvegardé: 2025-10-15_23_rapport-validation-ssl-https.json" -ForegroundColor Green

# Résumé
Write-Host "`n`n╔════════════════════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║                    RÉSUMÉ VALIDATION                      ║" -ForegroundColor Cyan
Write-Host "╚════════════════════════════════════════════════════════════╝`n" -ForegroundColor Cyan

if ($fullReport.Summary.AllTestsPassed) {
    Write-Host "🎉 TOUS LES TESTS RÉUSSIS ($($fullReport.Summary.SuccessfulTests)/$($fullReport.Summary.TotalTests))" -ForegroundColor Green
}
else {
    Write-Host "⚠️ Tests réussis: $($fullReport.Summary.SuccessfulTests)/$($fullReport.Summary.TotalTests)" -ForegroundColor Yellow
}

Write-Host "`n📋 Fichiers générés:" -ForegroundColor Cyan
Write-Host "   - certificat-ssl-info.json" -ForegroundColor Gray
Write-Host "   - 2025-10-15_23_rapport-validation-ssl-https.json" -ForegroundColor Gray

Write-Host "`n✅ Validation SSL/HTTPS terminée`n" -ForegroundColor Green