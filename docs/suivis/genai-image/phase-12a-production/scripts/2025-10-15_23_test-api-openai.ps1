# Test API OpenAI Compatible - ComfyUI + Forge
# Date: 2025-10-15 23:53 UTC
# Objectif: Vérifier et documenter les APIs disponibles

param(
    [string]$ComfyUIBaseUrl = "https://qwen-image-edit.myia.io",
    [string]$ForgeBaseUrl = "https://turbo.stable-diffusion-webui-forge.myia.io",
    [string]$OutputDir = "d:/Dev/CoursIA/docs/genai-suivis"
)

Write-Host "`n╔════════════════════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║      Test API OpenAI Compatible - Phase 12A              ║" -ForegroundColor Cyan
Write-Host "╚════════════════════════════════════════════════════════════╝`n" -ForegroundColor Cyan

$apiReport = @{
    Timestamp = (Get-Date).ToString("yyyy-MM-dd HH:mm:ss")
    ComfyUI = @{
        BaseUrl = $ComfyUIBaseUrl
        Endpoints = @{}
    }
    Forge = @{
        BaseUrl = $ForgeBaseUrl
        Endpoints = @{}
    }
}

# ============================================================================
# PHASE 2.2: Vérification Endpoints ComfyUI
# ============================================================================

Write-Host "═══ Phase 2.2: Endpoints API ComfyUI ═══`n" -ForegroundColor Yellow

$comfyEndpoints = @(
    @{ Path = "/system_stats"; Method = "GET"; Description = "Statistiques système" }
    @{ Path = "/queue"; Method = "GET"; Description = "État de la queue" }
    @{ Path = "/history"; Method = "GET"; Description = "Historique des prompts" }
    @{ Path = "/prompt"; Method = "POST"; Description = "Soumettre un prompt" }
    @{ Path = "/object_info"; Method = "GET"; Description = "Info objets ComfyUI" }
    @{ Path = "/extensions"; Method = "GET"; Description = "Extensions installées" }
    @{ Path = "/v1/completions"; Method = "POST"; Description = "OpenAI completions (si disponible)" }
    @{ Path = "/v1/chat/completions"; Method = "POST"; Description = "OpenAI chat completions (si disponible)" }
    @{ Path = "/api/v1/completions"; Method = "POST"; Description = "API completions (si disponible)" }
)

foreach ($endpoint in $comfyEndpoints) {
    Write-Host "📊 Test: $($endpoint.Path) [$($endpoint.Method)]" -ForegroundColor Cyan
    Write-Host "   Description: $($endpoint.Description)" -ForegroundColor Gray
    
    try {
        if ($endpoint.Method -eq "GET") {
            $response = Invoke-WebRequest -Uri "$ComfyUIBaseUrl$($endpoint.Path)" `
                -Method Get `
                -UseBasicParsing `
                -TimeoutSec 10 `
                -ErrorAction Stop
            
            Write-Host "   ✅ Accessible - Status: $($response.StatusCode)" -ForegroundColor Green
            
            $apiReport.ComfyUI.Endpoints[$endpoint.Path] = @{
                Method = $endpoint.Method
                Status = "Available"
                StatusCode = $response.StatusCode
                ContentType = $response.Headers['Content-Type']
                Description = $endpoint.Description
            }
        }
        elseif ($endpoint.Method -eq "POST") {
            # Pour POST, on teste juste si l'endpoint répond (même avec erreur 400)
            $response = Invoke-WebRequest -Uri "$ComfyUIBaseUrl$($endpoint.Path)" `
                -Method Post `
                -Body "{}" `
                -ContentType "application/json" `
                -UseBasicParsing `
                -TimeoutSec 10 `
                -ErrorAction SilentlyContinue
            
            if ($response) {
                Write-Host "   ✅ Endpoint répond - Status: $($response.StatusCode)" -ForegroundColor Green
                $apiReport.ComfyUI.Endpoints[$endpoint.Path] = @{
                    Method = $endpoint.Method
                    Status = "Available"
                    StatusCode = $response.StatusCode
                    Description = $endpoint.Description
                }
            }
        }
    }
    catch {
        $statusCode = $_.Exception.Response.StatusCode.value__
        
        if ($statusCode -eq 405) {
            Write-Host "   ⚠️ Méthode $($endpoint.Method) non supportée" -ForegroundColor Yellow
            $apiReport.ComfyUI.Endpoints[$endpoint.Path] = @{
                Method = $endpoint.Method
                Status = "MethodNotAllowed"
                StatusCode = 405
                Description = $endpoint.Description
            }
        }
        elseif ($statusCode -eq 404) {
            Write-Host "   ❌ Non trouvé (404)" -ForegroundColor Red
            $apiReport.ComfyUI.Endpoints[$endpoint.Path] = @{
                Method = $endpoint.Method
                Status = "NotFound"
                StatusCode = 404
                Description = $endpoint.Description
            }
        }
        elseif ($statusCode -eq 400) {
            Write-Host "   ⚠️ Endpoint existe mais requête invalide (400)" -ForegroundColor Yellow
            $apiReport.ComfyUI.Endpoints[$endpoint.Path] = @{
                Method = $endpoint.Method
                Status = "RequiresValidRequest"
                StatusCode = 400
                Description = $endpoint.Description
            }
        }
        else {
            Write-Host "   ⚠️ Erreur: $($_.Exception.Message)" -ForegroundColor Yellow
            $apiReport.ComfyUI.Endpoints[$endpoint.Path] = @{
                Method = $endpoint.Method
                Status = "Error"
                Message = $_.Exception.Message
                Description = $endpoint.Description
            }
        }
    }
    
    Start-Sleep -Milliseconds 200
}

# ============================================================================
# PHASE 2.3: Vérification API Forge
# ============================================================================

Write-Host "`n`n═══ Phase 2.3: API Forge ═══`n" -ForegroundColor Yellow

$forgeEndpoints = @(
    @{ Path = "/docs"; Method = "GET"; Description = "Documentation API Swagger" }
    @{ Path = "/sdapi/v1/txt2img"; Method = "POST"; Description = "Génération text-to-image" }
    @{ Path = "/sdapi/v1/img2img"; Method = "POST"; Description = "Génération image-to-image" }
    @{ Path = "/sdapi/v1/options"; Method = "GET"; Description = "Options de configuration" }
    @{ Path = "/sdapi/v1/sd-models"; Method = "GET"; Description = "Modèles disponibles" }
    @{ Path = "/sdapi/v1/samplers"; Method = "GET"; Description = "Samplers disponibles" }
)

foreach ($endpoint in $forgeEndpoints) {
    Write-Host "📊 Test: $($endpoint.Path) [$($endpoint.Method)]" -ForegroundColor Cyan
    Write-Host "   Description: $($endpoint.Description)" -ForegroundColor Gray
    
    try {
        if ($endpoint.Method -eq "GET") {
            $response = Invoke-WebRequest -Uri "$ForgeBaseUrl$($endpoint.Path)" `
                -Method Get `
                -UseBasicParsing `
                -TimeoutSec 10 `
                -ErrorAction Stop
            
            Write-Host "   ✅ Accessible - Status: $($response.StatusCode)" -ForegroundColor Green
            
            $apiReport.Forge.Endpoints[$endpoint.Path] = @{
                Method = $endpoint.Method
                Status = "Available"
                StatusCode = $response.StatusCode
                ContentType = $response.Headers['Content-Type']
                Description = $endpoint.Description
            }
        }
        elseif ($endpoint.Method -eq "POST") {
            # Test minimal pour txt2img
            if ($endpoint.Path -eq "/sdapi/v1/txt2img") {
                $testBody = @{
                    prompt = "test"
                    steps = 1
                    width = 512
                    height = 512
                } | ConvertTo-Json
                
                $response = Invoke-WebRequest -Uri "$ForgeBaseUrl$($endpoint.Path)" `
                    -Method Post `
                    -Body $testBody `
                    -ContentType "application/json" `
                    -UseBasicParsing `
                    -TimeoutSec 30 `
                    -ErrorAction SilentlyContinue
                
                if ($response) {
                    Write-Host "   ✅ API génération fonctionnelle - Status: $($response.StatusCode)" -ForegroundColor Green
                    $apiReport.Forge.Endpoints[$endpoint.Path] = @{
                        Method = $endpoint.Method
                        Status = "Functional"
                        StatusCode = $response.StatusCode
                        Description = $endpoint.Description
                        Note = "Testé avec requête minimale"
                    }
                }
            }
            else {
                # Pour les autres POST, on teste juste la présence
                Write-Host "   ⚠️ Endpoint POST non testé en détail" -ForegroundColor Yellow
                $apiReport.Forge.Endpoints[$endpoint.Path] = @{
                    Method = $endpoint.Method
                    Status = "NotTested"
                    Description = $endpoint.Description
                }
            }
        }
    }
    catch {
        $statusCode = $_.Exception.Response.StatusCode.value__
        
        if ($statusCode -eq 404) {
            Write-Host "   ❌ Non trouvé (404)" -ForegroundColor Red
            $apiReport.Forge.Endpoints[$endpoint.Path] = @{
                Method = $endpoint.Method
                Status = "NotFound"
                StatusCode = 404
                Description = $endpoint.Description
            }
        }
        elseif ($statusCode -eq 400 -or $statusCode -eq 422) {
            Write-Host "   ⚠️ Endpoint existe mais requête invalide ($statusCode)" -ForegroundColor Yellow
            $apiReport.Forge.Endpoints[$endpoint.Path] = @{
                Method = $endpoint.Method
                Status = "RequiresValidRequest"
                StatusCode = $statusCode
                Description = $endpoint.Description
            }
        }
        else {
            Write-Host "   ⚠️ Erreur: $($_.Exception.Message)" -ForegroundColor Yellow
            $apiReport.Forge.Endpoints[$endpoint.Path] = @{
                Method = $endpoint.Method
                Status = "Error"
                Message = $_.Exception.Message
                Description = $endpoint.Description
            }
        }
    }
    
    Start-Sleep -Milliseconds 200
}

# ============================================================================
# Sauvegarde et Résumé
# ============================================================================

Write-Host "`n`n═══ Sauvegarde Résultats API ═══`n" -ForegroundColor Yellow

$reportPath = "$OutputDir/2025-10-15_23_rapport-test-api.json"
$apiReport | ConvertTo-Json -Depth 10 | Out-File $reportPath -Encoding UTF8

Write-Host "✅ Rapport API sauvegardé: 2025-10-15_23_rapport-test-api.json" -ForegroundColor Green

# Statistiques
$comfyAvailable = ($apiReport.ComfyUI.Endpoints.Values | Where-Object { $_.Status -eq "Available" }).Count
$comfyTotal = $apiReport.ComfyUI.Endpoints.Count
$forgeAvailable = ($apiReport.Forge.Endpoints.Values | Where-Object { $_.Status -eq "Available" -or $_.Status -eq "Functional" }).Count
$forgeTotal = $apiReport.Forge.Endpoints.Count

Write-Host "`n`n╔════════════════════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║                    RÉSUMÉ TESTS API                       ║" -ForegroundColor Cyan
Write-Host "╚════════════════════════════════════════════════════════════╝`n" -ForegroundColor Cyan

Write-Host "📊 ComfyUI API:" -ForegroundColor Yellow
Write-Host "   Endpoints disponibles: $comfyAvailable / $comfyTotal" -ForegroundColor White

Write-Host "`n📊 Forge API:" -ForegroundColor Yellow
Write-Host "   Endpoints disponibles: $forgeAvailable / $forgeTotal" -ForegroundColor White

Write-Host "`n✅ Test des APIs terminé`n" -ForegroundColor Green