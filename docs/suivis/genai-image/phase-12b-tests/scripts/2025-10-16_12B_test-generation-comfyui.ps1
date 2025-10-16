# Tests End-to-End ComfyUI + Qwen avec Mesures Performance
# Phase 12B - Validation Génération Images Production
# Date: 2025-10-16

param(
    [string]$ComfyUIUrl = "https://qwen-image-edit.myia.io",
    [switch]$SkipTest2,
    [switch]$SkipTest3,
    [switch]$VerboseOutput
)

# Configuration
$SCREENSHOTS_DIR = "docs/genai-suivis/screenshots/phase12b"
$LOGS_DIR = "docs/genai-suivis/logs/phase12b"
$OUTPUTS_DIR = "docs/genai-suivis/outputs/phase12b"

# Créer répertoires
New-Item -ItemType Directory -Path $SCREENSHOTS_DIR -Force | Out-Null
New-Item -ItemType Directory -Path $LOGS_DIR -Force | Out-Null
New-Item -ItemType Directory -Path $OUTPUTS_DIR -Force | Out-Null

# Fonction logging avec niveaux
function Write-TestLog {
    param(
        [string]$Message,
        [string]$Level = "INFO"
    )
    
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $logMessage = "[$timestamp] [$Level] $Message"
    
    # Sauvegarder dans fichier
    $logMessage | Add-Content -Path "$LOGS_DIR/tests-$(Get-Date -Format 'yyyy-MM-dd').log"
    
    # Afficher avec couleur
    switch ($Level) {
        "ERROR"   { Write-Host $logMessage -ForegroundColor Red }
        "SUCCESS" { Write-Host $logMessage -ForegroundColor Green }
        "WARNING" { Write-Host $logMessage -ForegroundColor Yellow }
        "INFO"    { Write-Host $logMessage -ForegroundColor Cyan }
        default   { Write-Host $logMessage }
    }
}

# Fonction stats GPU
function Get-GPUStats {
    try {
        $stats = wsl nvidia-smi --query-gpu=index,name,memory.used,memory.total,temperature.gpu,utilization.gpu --format=csv,noheader,nounits -i 1
        
        if ($stats) {
            $parts = $stats -split ','
            return @{
                GPU = "RTX_3090"
                Index = [int]$parts[0].Trim()
                Name = $parts[1].Trim()
                MemoryUsed = [int]$parts[2].Trim()
                MemoryTotal = [int]$parts[3].Trim()
                MemoryPercent = [math]::Round(([int]$parts[2].Trim() / [int]$parts[3].Trim()) * 100, 2)
                Temperature = [int]$parts[4].Trim()
                Utilization = [int]$parts[5].Trim()
            }
        }
    }
    catch {
        Write-TestLog "Erreur lecture stats GPU: $_" "WARNING"
        return $null
    }
    return $null
}

# Fonction attente génération avec timeout
function Wait-Generation {
    param(
        [string]$PromptId,
        [int]$TimeoutSeconds = 120
    )
    
    $waited = 0
    $completed = $false
    $checkInterval = 5
    
    Write-TestLog "Attente génération (timeout: $TimeoutSeconds secondes)..."
    
    while ($waited -lt $TimeoutSeconds -and -not $completed) {
        Start-Sleep -Seconds $checkInterval
        $waited += $checkInterval
        
        try {
            $history = Invoke-RestMethod -Uri "$ComfyUIUrl/history/$PromptId" -UseBasicParsing -ErrorAction Stop
            
            if ($history.$PromptId.status.completed -eq $true) {
                $completed = $true
                Write-TestLog "✅ Génération complétée en $waited secondes" "SUCCESS"
                return @{
                    Success = $true
                    Duration = $waited
                    History = $history.$PromptId
                }
            }
            
            if ($VerboseOutput) {
                Write-TestLog "Attente... ($waited / $TimeoutSeconds secondes)"
            }
        }
        catch {
            if ($VerboseOutput) {
                Write-TestLog "Polling génération... ($waited s)" "INFO"
            }
        }
    }
    
    if (-not $completed) {
        Write-TestLog "⚠️ TIMEOUT: Génération non complétée après $TimeoutSeconds secondes" "WARNING"
        return @{
            Success = $false
            Duration = $waited
            Timeout = $true
        }
    }
}

# Banner début
Write-Host "`n" -NoNewline
Write-Host "═══════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "   Phase 12B - Tests End-to-End Génération Images ComfyUI    " -ForegroundColor Cyan
Write-Host "═══════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host ""

Write-TestLog "Démarrage tests Phase 12B" "SUCCESS"
Write-TestLog "URL ComfyUI: $ComfyUIUrl"
Write-TestLog "Logs: $LOGS_DIR"
Write-TestLog "Outputs: $OUTPUTS_DIR"
Write-Host ""

# Test préliminaire: Vérifier ComfyUI accessible
Write-TestLog "Test préliminaire: Vérification accessibilité ComfyUI..."

try {
    $response = Invoke-WebRequest -Uri "$ComfyUIUrl/system_stats" -UseBasicParsing -ErrorAction Stop
    Write-TestLog "✅ ComfyUI accessible (HTTP $($response.StatusCode))" "SUCCESS"
}
catch {
    Write-TestLog "❌ ERREUR CRITIQUE: ComfyUI non accessible" "ERROR"
    Write-TestLog "Détails: $_" "ERROR"
    Write-TestLog "Vérifiez que le service ComfyUI est démarré: wsl ps aux | grep ComfyUI" "ERROR"
    exit 1
}

# Stats GPU initiales
Write-Host ""
Write-TestLog "Capture stats GPU initiales..."
$gpuStart = Get-GPUStats

if ($gpuStart) {
    Write-TestLog "GPU État Initial:" "INFO"
    Write-TestLog "  - Nom: $($gpuStart.Name)" "INFO"
    Write-TestLog "  - VRAM: $($gpuStart.MemoryUsed) MB / $($gpuStart.MemoryTotal) MB ($($gpuStart.MemoryPercent)%)" "INFO"
    Write-TestLog "  - Température: $($gpuStart.Temperature)°C" "INFO"
    Write-TestLog "  - Utilisation: $($gpuStart.Utilization)%" "INFO"
} else {
    Write-TestLog "⚠️ Impossible de lire stats GPU (nvidia-smi non disponible)" "WARNING"
}

Write-Host ""
Write-Host "─────────────────────────────────────────────────────────────" -ForegroundColor Gray
Write-Host ""

# ============================================
# TEST 1: Génération Image Simple (Workflow Par Défaut)
# ============================================

Write-Host "╔═══════════════════════════════════════════════════════════╗" -ForegroundColor Green
Write-Host "║  TEST 1: Génération Image Simple (Text-to-Image)         ║" -ForegroundColor Green
Write-Host "╚═══════════════════════════════════════════════════════════╝" -ForegroundColor Green
Write-Host ""

$test1Start = Get-Date
$test1Result = @{
    Name = "Test1_Generation_Simple"
    Status = "PENDING"
    Duration = 0
    VRAMUsed = 0
    Temperature = 0
    PromptId = $null
    Error = $null
}

# Workflow JSON simplifié pour génération basique
$workflowSimple = @{
    prompt = @{
        "3" = @{
            inputs = @{
                seed = 42
                steps = 20
                cfg = 7.0
                sampler_name = "euler"
                scheduler = "normal"
                denoise = 1.0
                model = @("4", 0)
                positive = @("6", 0)
                negative = @("7", 0)
                latent_image = @("5", 0)
            }
            class_type = "KSampler"
        }
        "4" = @{
            inputs = @{
                ckpt_name = "Qwen-Image-Edit-2509-FP8/diffusion_pytorch_model.safetensors"
            }
            class_type = "CheckpointLoaderSimple"
        }
        "5" = @{
            inputs = @{
                width = 512
                height = 512
                batch_size = 1
            }
            class_type = "EmptyLatentImage"
        }
        "6" = @{
            inputs = @{
                text = "A beautiful mountain landscape at sunset with vibrant colors, photorealistic, highly detailed"
                clip = @("4", 1)
            }
            class_type = "CLIPTextEncode"
        }
        "7" = @{
            inputs = @{
                text = "blurry, low quality, watermark, text, signature"
                clip = @("4", 1)
            }
            class_type = "CLIPTextEncode"
        }
        "8" = @{
            inputs = @{
                samples = @("3", 0)
                vae = @("4", 2)
            }
            class_type = "VAEDecode"
        }
        "9" = @{
            inputs = @{
                filename_prefix = "ComfyUI_Phase12B_Test1"
                images = @("8", 0)
            }
            class_type = "SaveImage"
        }
    }
} | ConvertTo-Json -Depth 10 -Compress

try {
    Write-TestLog "📤 Envoi workflow génération simple..."
    Write-TestLog "  - Résolution: 512x512"
    Write-TestLog "  - Steps: 20"
    Write-TestLog "  - Prompt: 'A beautiful mountain landscape at sunset...'"
    
    $response = Invoke-RestMethod -Uri "$ComfyUIUrl/prompt" `
        -Method POST `
        -Body $workflowSimple `
        -ContentType "application/json" `
        -ErrorAction Stop
    
    $promptId = $response.prompt_id
    $test1Result.PromptId = $promptId
    
    Write-TestLog "✅ Workflow soumis avec succès" "SUCCESS"
    Write-TestLog "  - Prompt ID: $promptId"
    
    # Attendre génération
    $genResult = Wait-Generation -PromptId $promptId -TimeoutSeconds 120
    
    if ($genResult.Success) {
        $test1Result.Status = "SUCCESS"
        $test1Result.Duration = $genResult.Duration
        
        # Stats GPU après génération
        $gpuAfter = Get-GPUStats
        
        if ($gpuAfter) {
            $test1Result.VRAMUsed = $gpuAfter.MemoryUsed - $gpuStart.MemoryUsed
            $test1Result.Temperature = $gpuAfter.Temperature
            
            Write-TestLog ""
            Write-TestLog "📊 Métriques Test 1:" "SUCCESS"
            Write-TestLog "  - Durée génération: $($test1Result.Duration) secondes"
            Write-TestLog "  - VRAM finale: $($gpuAfter.MemoryUsed) MB / $($gpuAfter.MemoryTotal) MB ($($gpuAfter.MemoryPercent)%)"
            Write-TestLog "  - VRAM augmentation: +$($test1Result.VRAMUsed) MB"
            Write-TestLog "  - Température finale: $($test1Result.Temperature)°C"
            Write-TestLog "  - Utilisation GPU: $($gpuAfter.Utilization)%"
        }
        
        Write-Host ""
        Write-TestLog "✅ TEST 1 RÉUSSI" "SUCCESS"
    }
    else {
        $test1Result.Status = "TIMEOUT"
        $test1Result.Duration = $genResult.Duration
        $test1Result.Error = "Timeout après $($genResult.Duration) secondes"
        
        Write-TestLog "⚠️ TEST 1 TIMEOUT (mais workflow peut être en cours)" "WARNING"
    }
}
catch {
    $test1Result.Status = "ERROR"
    $test1Result.Error = $_.Exception.Message
    
    Write-TestLog "❌ ERREUR Test 1: $_" "ERROR"
}

$test1End = Get-Date
$test1TotalDuration = ($test1End - $test1Start).TotalSeconds

Write-Host ""
Write-Host "─────────────────────────────────────────────────────────────" -ForegroundColor Gray
Write-Host ""

# ============================================
# TEST 2: Custom Node QwenVL (Image Description)
# ============================================

if (-not $SkipTest2) {
    Write-Host "╔═══════════════════════════════════════════════════════════╗" -ForegroundColor Yellow
    Write-Host "║  TEST 2: Custom Node QwenVL (Image Analysis)             ║" -ForegroundColor Yellow
    Write-Host "╚═══════════════════════════════════════════════════════════╝" -ForegroundColor Yellow
    Write-Host ""
    
    Write-TestLog "⚠️ Test 2 nécessite workflow QwenVL spécifique" "WARNING"
    Write-TestLog "Custom nodes détectés: 28 (incluant QwenVL*)"
    Write-TestLog "TODO: Créer workflow test avec QwenVLCLIPLoader + QwenVLTextEncoder"
    Write-TestLog "Ce test sera implémenté après validation documentation workflows Qwen"
    
    Write-Host ""
    Write-Host "─────────────────────────────────────────────────────────────" -ForegroundColor Gray
    Write-Host ""
}

# ============================================
# TEST 3: Custom Node QwenImageEdit (Édition Guidée)
# ============================================

if (-not $SkipTest3) {
    Write-Host "╔═══════════════════════════════════════════════════════════╗" -ForegroundColor Yellow
    Write-Host "║  TEST 3: QwenImageEdit (Image Editing)                   ║" -ForegroundColor Yellow
    Write-Host "╚═══════════════════════════════════════════════════════════╝" -ForegroundColor Yellow
    Write-Host ""
    
    Write-TestLog "⚠️ Test 3 nécessite workflow QwenImageEdit spécifique" "WARNING"
    Write-TestLog "Custom nodes disponibles: QwenImageModelWithEdit, QwenImageSamplerWithEdit"
    Write-TestLog "TODO: Créer workflow test avec édition guidée par texte"
    Write-TestLog "Ce test sera implémenté après validation documentation workflows Qwen"
    
    Write-Host ""
    Write-Host "─────────────────────────────────────────────────────────────" -ForegroundColor Gray
    Write-Host ""
}

# ============================================
# STATISTIQUES FINALES
# ============================================

Write-Host "╔═══════════════════════════════════════════════════════════╗" -ForegroundColor Cyan
Write-Host "║  RÉSUMÉ STATISTIQUES PHASE 12B                            ║" -ForegroundColor Cyan
Write-Host "╚═══════════════════════════════════════════════════════════╝" -ForegroundColor Cyan
Write-Host ""

# Stats GPU finales
$gpuFinal = Get-GPUStats

if ($gpuFinal) {
    Write-TestLog "GPU État Final:" "INFO"
    Write-TestLog "  - VRAM: $($gpuFinal.MemoryUsed) MB / $($gpuFinal.MemoryTotal) MB ($($gpuFinal.MemoryPercent)%)"
    Write-TestLog "  - Température: $($gpuFinal.Temperature)°C"
    Write-TestLog "  - Utilisation: $($gpuFinal.Utilization)%"
}

Write-Host ""
Write-TestLog "Tests complétés. Logs sauvegardés: $LOGS_DIR"

# ============================================
# GÉNÉRATION RAPPORT JSON
# ============================================

$rapport = @{
    date = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    phase = "12B"
    comfyui_url = $ComfyUIUrl
    infrastructure = @{
        backend = "http://localhost:8188"
        gpu = "NVIDIA RTX 3090 (24GB VRAM)"
        model = "Qwen-Image-Edit-2509-FP8"
    }
    tests = @{
        test1_generation_simple = $test1Result
        test2_qwen_vl = @{
            status = if ($SkipTest2) { "SKIPPED" } else { "PENDING" }
            note = "Nécessite workflow QwenVL spécifique"
        }
        test3_qwen_image_edit = @{
            status = if ($SkipTest3) { "SKIPPED" } else { "PENDING" }
            note = "Nécessite workflow QwenImageEdit spécifique"
        }
    }
    gpu_stats = @{
        initial = $gpuStart
        final = $gpuFinal
        delta_vram_mb = if ($gpuStart -and $gpuFinal) { $gpuFinal.MemoryUsed - $gpuStart.MemoryUsed } else { 0 }
        delta_temp_c = if ($gpuStart -and $gpuFinal) { $gpuFinal.Temperature - $gpuStart.Temperature } else { 0 }
    }
    summary = @{
        total_duration_seconds = $test1TotalDuration
        tests_completed = if ($test1Result.Status -eq "SUCCESS") { 1 } else { 0 }
        tests_pending = 2
        status = if ($test1Result.Status -eq "SUCCESS") { "PARTIAL_SUCCESS" } else { "NEEDS_INVESTIGATION" }
    }
}

$rapportPath = "$LOGS_DIR/rapport-tests-$(Get-Date -Format 'yyyy-MM-dd-HHmmss').json"
$rapport | ConvertTo-Json -Depth 10 | Out-File $rapportPath -Encoding UTF8

Write-TestLog "Rapport JSON sauvegardé: $rapportPath" "SUCCESS"

# ============================================
# RECOMMANDATIONS
# ============================================

Write-Host ""
Write-Host "╔═══════════════════════════════════════════════════════════╗" -ForegroundColor Magenta
Write-Host "║  RECOMMANDATIONS PROCHAINES ÉTAPES                        ║" -ForegroundColor Magenta
Write-Host "╚═══════════════════════════════════════════════════════════╝" -ForegroundColor Magenta
Write-Host ""

if ($test1Result.Status -eq "SUCCESS") {
    Write-TestLog "✅ Infrastructure production validée pour génération basique" "SUCCESS"
    Write-TestLog ""
    Write-TestLog "📋 Prochaines étapes recommandées:"
    Write-TestLog "  1. Documenter workflows Qwen spécifiques (Tests 2 & 3)"
    Write-TestLog "  2. Créer exemples workflows pour custom nodes"
    Write-TestLog "  3. Tester workflows multi-images"
    Write-TestLog "  4. Implémenter monitoring GPU continu"
    Write-TestLog "  5. Créer notebooks pédagogiques (Phase 12C)"
}
elseif ($test1Result.Status -eq "TIMEOUT") {
    Write-TestLog "⚠️ Génération en timeout - vérifier capacité GPU/modèle" "WARNING"
    Write-TestLog ""
    Write-TestLog "🔧 Actions suggérées:"
    Write-TestLog "  1. Vérifier logs ComfyUI: wsl cat /home/jesse/SD/workspace/comfyui-qwen/comfyui.log"
    Write-TestLog "  2. Vérifier VRAM disponible suffisante"
    Write-TestLog "  3. Tester avec résolution plus petite (256x256)"
    Write-TestLog "  4. Vérifier temps génération attendu pour ce modèle"
}
else {
    Write-TestLog "❌ Test échoué - diagnostic requis" "ERROR"
    Write-TestLog ""
    Write-TestLog "🔧 Actions suggérées:"
    Write-TestLog "  1. Vérifier logs: $LOGS_DIR"
    Write-TestLog "  2. Vérifier service ComfyUI: wsl ps aux | grep ComfyUI"
    Write-TestLog "  3. Tester API manuellement: curl $ComfyUIUrl/system_stats"
    Write-TestLog "  4. Vérifier modèle chargé correctement"
}

Write-Host ""
Write-Host "═══════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host "   Tests Phase 12B Terminés - $(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')   " -ForegroundColor Cyan
Write-Host "═══════════════════════════════════════════════════════════════" -ForegroundColor Cyan
Write-Host ""

# Retourner code sortie basé sur résultat
if ($test1Result.Status -eq "SUCCESS") {
    exit 0
}
elseif ($test1Result.Status -eq "TIMEOUT") {
    exit 2  # Timeout
}
else {
    exit 1  # Erreur
}