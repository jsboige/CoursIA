# Script de migration fichiers GenAI vers structure docs/suivis/genai-image/
# Créé le: 2025-10-16
# Utilise git mv pour préserver l'historique

Write-Host "=== Migration Fichiers GenAI Image ===" -ForegroundColor Cyan
Write-Host ""

$ErrorActionPreference = "Continue"
$migratedCount = 0
$errorCount = 0

function Move-GitFile {
    param(
        [string]$Source,
        [string]$Destination
    )
    
    if (Test-Path $Source) {
        try {
            git mv "$Source" "$Destination" 2>$null
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✓ Migré: $Source -> $Destination" -ForegroundColor Green
                $script:migratedCount++
            } else {
                Write-Host "✗ Erreur: $Source" -ForegroundColor Red
                $script:errorCount++
            }
        } catch {
            Write-Host "✗ Exception: $Source - $($_.Exception.Message)" -ForegroundColor Red
            $script:errorCount++
        }
    } else {
        Write-Host "○ Pas trouvé: $Source" -ForegroundColor Yellow
    }
}

Write-Host "Phase 1-8: Docker/MCP (11 fichiers)" -ForegroundColor Cyan
Write-Host "-----------------------------------"

# Phase 1-8 Documents
Move-GitFile "docs/genai-suivis/2025-10-07_01_phase1-2-architecture.md" "docs/suivis/genai-image/phase-01-08-docker/rapports/2025-10-07_01_phase1-2-architecture.md"
Move-GitFile "docs/genai-suivis/2025-10-08_02_phase2-1-final.md" "docs/suivis/genai-image/phase-01-08-docker/rapports/2025-10-08_02_phase2-1-final.md"
Move-GitFile "docs/genai-suivis/2025-10-08_03_phase1-3-production-ready.md" "docs/suivis/genai-image/phase-01-08-docker/rapports/2025-10-08_03_phase1-3-production-ready.md"
Move-GitFile "docs/genai-suivis/2025-10-08_04_sync-git-docker.md" "docs/suivis/genai-image/phase-01-08-docker/rapports/2025-10-08_04_sync-git-docker.md"
Move-GitFile "docs/genai-suivis/2025-10-08_05_tests-docker-mcp-part1.md" "docs/suivis/genai-image/phase-01-08-docker/rapports/2025-10-08_05_tests-docker-mcp-part1.md"
Move-GitFile "docs/genai-suivis/2025-10-08_05_tests-docker-mcp-part2.md" "docs/suivis/genai-image/phase-01-08-docker/rapports/2025-10-08_05_tests-docker-mcp-part2.md"
Move-GitFile "docs/genai-suivis/2025-10-08_05_tests-docker-mcp-part3.md" "docs/suivis/genai-image/phase-01-08-docker/rapports/2025-10-08_05_tests-docker-mcp-part3.md"
Move-GitFile "docs/genai-suivis/2025-10-08_06_deploiement-docker-standalone.md" "docs/suivis/genai-image/phase-01-08-docker/rapports/2025-10-08_06_deploiement-docker-standalone.md"
Move-GitFile "docs/genai-suivis/2025-10-08_07_rapport-final-docker.md" "docs/suivis/genai-image/phase-01-08-docker/rapports/2025-10-08_07_rapport-final-docker.md"

# Phase 1-8 Scripts (depuis scripts/)
Move-GitFile "docs/genai-suivis/scripts/test-01-orchestrator.ps1" "docs/suivis/genai-image/phase-01-08-docker/scripts/test-01-orchestrator.ps1"
Move-GitFile "docs/genai-suivis/scripts/test-02-comfyui.ps1" "docs/suivis/genai-image/phase-01-08-docker/scripts/test-02-comfyui.ps1"

Write-Host ""
Write-Host "Phase 9-10: Investigation Forge (7 fichiers)" -ForegroundColor Cyan
Write-Host "---------------------------------------------"

# Phase 9-10 Documents
Move-GitFile "docs/genai-suivis/2025-10-10_09_rapport-investigation-forge-qwen.md" "docs/suivis/genai-image/phase-09-10-investigation/rapports/2025-10-10_09_rapport-investigation-forge-qwen.md"
Move-GitFile "docs/genai-suivis/2025-10-10_09_rapport-investigation-final-forge-qwen.md" "docs/suivis/genai-image/phase-09-10-investigation/rapports/2025-10-10_09_rapport-investigation-final-forge-qwen.md"
Move-GitFile "docs/genai-suivis/2025-10-11_10_diagnostic-reparation-forge-sdxl.md" "docs/suivis/genai-image/phase-09-10-investigation/rapports/2025-10-11_10_diagnostic-reparation-forge-sdxl.md"
Move-GitFile "docs/genai-suivis/2025-10-08_08_validation-complete-docker-mcp.md" "docs/suivis/genai-image/phase-01-08-docker/rapports/2025-10-08_08_validation-complete-docker-mcp.md"

# Phase 9-10 Scripts
Move-GitFile "docs/genai-suivis/2025-10-10_09_phase9-investigation-forge-qwen.ps1" "docs/suivis/genai-image/phase-09-10-investigation/scripts/2025-10-10_09_phase9-investigation-forge-qwen.ps1"

# Phase 9-10 Screenshots
Move-GitFile "docs/genai-suivis/screenshots/forge-login-mcp.png" "docs/suivis/genai-image/phase-09-10-investigation/screenshots/forge-login-mcp.png"
Move-GitFile "docs/genai-suivis/screenshots/forge-ui.png" "docs/suivis/genai-image/phase-09-10-investigation/screenshots/forge-ui.png"

Write-Host ""
Write-Host "Phase 11: Deployment ComfyUI (15 fichiers)" -ForegroundColor Cyan
Write-Host "-------------------------------------------"

# Phase 11 Documents
Move-GitFile "docs/genai-suivis/2025-10-13_11_checkpoint-semantique-1-comfyui-base.md" "docs/suivis/genai-image/phase-11-deployment/rapports/2025-10-13_11_checkpoint-semantique-1-comfyui-base.md"
Move-GitFile "docs/genai-suivis/2025-10-13_11_checkpoint-semantique-2-standalone-validation.md" "docs/suivis/genai-image/phase-11-deployment/rapports/2025-10-13_11_checkpoint-semantique-2-standalone-validation.md"
Move-GitFile "docs/genai-suivis/2025-10-13_11_rapport-final-phase11-comfyui-qwen.md" "docs/suivis/genai-image/phase-11-deployment/rapports/2025-10-13_11_rapport-final-phase11-comfyui-qwen.md"

# Phase 11 Scripts (.sh)
Move-GitFile "docs/genai-suivis/2025-10-13_11_download-qwen-model.sh" "docs/suivis/genai-image/phase-11-deployment/scripts/2025-10-13_11_download-qwen-model.sh"
Move-GitFile "docs/genai-suivis/2025-10-13_11_install-comfyui-requirements.sh" "docs/suivis/genai-image/phase-11-deployment/scripts/2025-10-13_11_install-comfyui-requirements.sh"
Move-GitFile "docs/genai-suivis/2025-10-13_11_install-qwen-custom-node.sh" "docs/suivis/genai-image/phase-11-deployment/scripts/2025-10-13_11_install-qwen-custom-node.sh"
Move-GitFile "docs/genai-suivis/2025-10-13_11_install-qwen-custom-node-fixed.sh" "docs/suivis/genai-image/phase-11-deployment/scripts/2025-10-13_11_install-qwen-custom-node-fixed.sh"
Move-GitFile "docs/genai-suivis/2025-10-13_11_launch-comfyui-standalone.sh" "docs/suivis/genai-image/phase-11-deployment/scripts/2025-10-13_11_launch-comfyui-standalone.sh"
Move-GitFile "docs/genai-suivis/2025-10-13_11_resolve-gpu-mapping.sh" "docs/suivis/genai-image/phase-11-deployment/scripts/2025-10-13_11_resolve-gpu-mapping.sh"
Move-GitFile "docs/genai-suivis/2025-10-13_11_search-qwen-alternatives.sh" "docs/suivis/genai-image/phase-11-deployment/scripts/2025-10-13_11_search-qwen-alternatives.sh"
Move-GitFile "docs/genai-suivis/2025-10-13_11_test-comfyui-background.sh" "docs/suivis/genai-image/phase-11-deployment/scripts/2025-10-13_11_test-comfyui-background.sh"
Move-GitFile "docs/genai-suivis/2025-10-13_11_test-comfyui-standalone.sh" "docs/suivis/genai-image/phase-11-deployment/scripts/2025-10-13_11_test-comfyui-standalone.sh"
Move-GitFile "docs/genai-suivis/2025-10-13_11_verify-comfyui-setup.sh" "docs/suivis/genai-image/phase-11-deployment/scripts/2025-10-13_11_verify-comfyui-setup.sh"

Write-Host ""
Write-Host "Phase 12A: Production SSL/IIS (32 fichiers)" -ForegroundColor Cyan
Write-Host "--------------------------------------------"

# Phase 12A Documents
Move-GitFile "docs/genai-suivis/2025-10-14_12A_README-PRODUCTION.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-14_12A_README-PRODUCTION.md"
Move-GitFile "docs/genai-suivis/2025-10-14_12A_checkpoint-semantique-production.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-14_12A_checkpoint-semantique-production.md"
Move-GitFile "docs/genai-suivis/2025-10-15_13_checkpoint-semantique-phase12A-production.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-15_13_checkpoint-semantique-phase12A-production.md"
Move-GitFile "docs/genai-suivis/2025-10-15_13_commandes-admin-iis.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-15_13_commandes-admin-iis.md"
Move-GitFile "docs/genai-suivis/2025-10-15_13_guide-installation-iis-ssl.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-15_13_guide-installation-iis-ssl.md"
Move-GitFile "docs/genai-suivis/2025-10-15_13_rapport-debug-comfyui.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-15_13_rapport-debug-comfyui.md"
Move-GitFile "docs/genai-suivis/2025-10-15_13_rapport-deploiement-iis-comfyui.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-15_13_rapport-deploiement-iis-comfyui.md"
Move-GitFile "docs/genai-suivis/2025-10-15_13_rapport-final-iis-ssl-comfyui.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-15_13_rapport-final-iis-ssl-comfyui.md"
Move-GitFile "docs/genai-suivis/2025-10-15_22_INSTRUCTIONS-FINALES-SSL-TESTS.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-15_22_INSTRUCTIONS-FINALES-SSL-TESTS.md"
Move-GitFile "docs/genai-suivis/2025-10-15_22_execution-deploiement-final.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-15_22_execution-deploiement-final.md"
Move-GitFile "docs/genai-suivis/2025-10-15_23_RESUME-FINAL-PHASE12A.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-15_23_RESUME-FINAL-PHASE12A.md"
Move-GitFile "docs/genai-suivis/2025-10-15_23_API-OpenAI-Compatible.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-15_23_API-OpenAI-Compatible.md"
Move-GitFile "docs/genai-suivis/2025-10-15_23_tests-manuels-ui.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-15_23_tests-manuels-ui.md"
Move-GitFile "docs/genai-suivis/2025-10-16_00_rapport-tests-visuels-playwright.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-16_00_rapport-tests-visuels-playwright.md"
Move-GitFile "docs/genai-suivis/2025-10-16_04_rapport-diagnostic-websocket.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-16_04_rapport-diagnostic-websocket.md"
Move-GitFile "docs/genai-suivis/2025-10-16_05_RAPPORT-FINAL-PHASE12A-PRODUCTION.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-16_05_RAPPORT-FINAL-PHASE12A-PRODUCTION.md"
Move-GitFile "docs/genai-suivis/2025-10-16_06_CHECKPOINT-SEMANTIQUE-FINAL-PHASE12A.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-16_06_CHECKPOINT-SEMANTIQUE-FINAL-PHASE12A.md"
Move-GitFile "docs/genai-suivis/2025-10-16_07_VALIDATION-FINALE-COMPLETE.md" "docs/suivis/genai-image/phase-12a-production/rapports/2025-10-16_07_VALIDATION-FINALE-COMPLETE.md"

# Phase 12A Scripts (.ps1 et .sh)
Move-GitFile "docs/genai-suivis/2025-10-14_12A_install-scheduled-task.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-14_12A_install-scheduled-task.ps1"
Move-GitFile "docs/genai-suivis/2025-10-14_12A_monitor-gpu-performance.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-14_12A_monitor-gpu-performance.ps1"
Move-GitFile "docs/genai-suivis/2025-10-14_12A_setup-iis-reverse-proxy.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-14_12A_setup-iis-reverse-proxy.ps1"
Move-GitFile "docs/genai-suivis/2025-10-14_12A_start-comfyui-watchdog.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-14_12A_start-comfyui-watchdog.ps1"
Move-GitFile "docs/genai-suivis/2025-10-15_13_create-iis-site-comfyui.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-15_13_create-iis-site-comfyui.ps1"
Move-GitFile "docs/genai-suivis/2025-10-15_13_debug-comfyui-startup.sh" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-15_13_debug-comfyui-startup.sh"
Move-GitFile "docs/genai-suivis/2025-10-15_13_start-comfyui.sh" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-15_13_start-comfyui.sh"
Move-GitFile "docs/genai-suivis/2025-10-15_13_test-comfyui-access.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-15_13_test-comfyui-access.ps1"
Move-GitFile "docs/genai-suivis/2025-10-15_13_test-comfyui-launch.sh" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-15_13_test-comfyui-launch.sh"
Move-GitFile "docs/genai-suivis/2025-10-15_13_test-playwright-ui.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-15_13_test-playwright-ui.ps1"
Move-GitFile "docs/genai-suivis/2025-10-15_22_configure-ssl-win-acme.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-15_22_configure-ssl-win-acme.ps1"
Move-GitFile "docs/genai-suivis/2025-10-15_23_finalisation-complete-phase12A.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-15_23_finalisation-complete-phase12A.ps1"
Move-GitFile "docs/genai-suivis/2025-10-15_23_test-api-openai.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-15_23_test-api-openai.ps1"
Move-GitFile "docs/genai-suivis/2025-10-15_23_update-rapport-final.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-15_23_update-rapport-final.ps1"
Move-GitFile "docs/genai-suivis/2025-10-15_23_validation-ssl-https.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-15_23_validation-ssl-https.ps1"
Move-GitFile "docs/genai-suivis/2025-10-16_00_copier-screenshots-mcp.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-16_00_copier-screenshots-mcp.ps1"
Move-GitFile "docs/genai-suivis/2025-10-16_00_copier-screenshots-playwright.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-16_00_copier-screenshots-playwright.ps1"
Move-GitFile "docs/genai-suivis/2025-10-16_01_test-websocket-comfyui.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-16_01_test-websocket-comfyui.ps1"
Move-GitFile "docs/genai-suivis/2025-10-16_02_restart-iis-site.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-16_02_restart-iis-site.ps1"
Move-GitFile "docs/genai-suivis/2025-10-16_03_analyze-iis-logs.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-16_03_analyze-iis-logs.ps1"
Move-GitFile "docs/genai-suivis/2025-10-16_07_validation-finale-autonome.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/2025-10-16_07_validation-finale-autonome.ps1"
Move-GitFile "docs/genai-suivis/check-certificates.ps1" "docs/suivis/genai-image/phase-12a-production/scripts/check-certificates.ps1"

# Phase 12A Screenshots
Move-GitFile "docs/genai-suivis/screenshots/comfyui-interface-mcp.png" "docs/suivis/genai-image/phase-12a-production/screenshots/comfyui-interface-mcp.png"
Move-GitFile "docs/genai-suivis/screenshots/comfyui-ui.png" "docs/suivis/genai-image/phase-12a-production/screenshots/comfyui-ui.png"

Write-Host ""
Write-Host "Phase 12B: Tests Génération (4 fichiers)" -ForegroundColor Cyan
Write-Host "-----------------------------------------"

# Phase 12B Documents
Move-GitFile "docs/genai-suivis/2025-10-16_12B_checkpoint-1-workflows-context.md" "docs/suivis/genai-image/phase-12b-tests/rapports/2025-10-16_12B_checkpoint-1-workflows-context.md"
Move-GitFile "docs/genai-suivis/2025-10-16_12B_RAPPORT-FINAL-TESTS-GENERATION.md" "docs/suivis/genai-image/phase-12b-tests/rapports/2025-10-16_12B_RAPPORT-FINAL-TESTS-GENERATION.md"
Move-GitFile "docs/genai-suivis/2025-10-16_12B_CHECKPOINT-SEMANTIQUE-FINAL.md" "docs/suivis/genai-image/phase-12b-tests/rapports/2025-10-16_12B_CHECKPOINT-SEMANTIQUE-FINAL.md"

# Phase 12B Scripts
Move-GitFile "docs/genai-suivis/2025-10-16_12B_test-generation-comfyui.ps1" "docs/suivis/genai-image/phase-12b-tests/scripts/2025-10-16_12B_test-generation-comfyui.ps1"

Write-Host ""
Write-Host "Phase 12C: Architecture Workflows (6 fichiers)" -ForegroundColor Cyan
Write-Host "-----------------------------------------------"

# Phase 12C Documents
Move-GitFile "docs/genai-suivis/2025-10-16_12C_checkpoint-1-taxonomie-nodes-qwen.md" "docs/suivis/genai-image/phase-12c-architecture/rapports/2025-10-16_12C_checkpoint-1-taxonomie-nodes-qwen.md"
Move-GitFile "docs/genai-suivis/2025-10-16_12C_architectures-5-workflows-qwen.md" "docs/suivis/genai-image/phase-12c-architecture/rapports/2025-10-16_12C_architectures-5-workflows-qwen.md"
Move-GitFile "docs/genai-suivis/2025-10-16_12C_design-notebooks-pedagogiques.md" "docs/suivis/genai-image/phase-12c-architecture/rapports/2025-10-16_12C_design-notebooks-pedagogiques.md"
Move-GitFile "docs/genai-suivis/2025-10-16_12C_roadmap-adaptation-18-notebooks.md" "docs/suivis/genai-image/phase-12c-architecture/rapports/2025-10-16_12C_roadmap-adaptation-18-notebooks.md"
Move-GitFile "docs/genai-suivis/2025-10-16_12C_RAPPORT-FINAL-PHASE12C.md" "docs/suivis/genai-image/phase-12c-architecture/rapports/2025-10-16_12C_RAPPORT-FINAL-PHASE12C.md"
Move-GitFile "docs/genai-suivis/2025-10-16_12C_CHECKPOINT-SEMANTIQUE-FINAL.md" "docs/suivis/genai-image/phase-12c-architecture/rapports/2025-10-16_12C_CHECKPOINT-SEMANTIQUE-FINAL.md"

Write-Host ""
Write-Host "Phase 13A: Bridge ComfyUI (2 fichiers)" -ForegroundColor Cyan
Write-Host "---------------------------------------"

# Phase 13A Documents
Move-GitFile "docs/genai-suivis/2025-10-16_13A_checkpoint-1-etat-lieux-bridge.md" "docs/suivis/genai-image/phase-13a-bridge/rapports/2025-10-16_13A_checkpoint-1-etat-lieux-bridge.md"
Move-GitFile "docs/genai-suivis/2025-10-16_13A_RAPPORT-FINAL-BRIDGE-COMFYUI.md" "docs/suivis/genai-image/phase-13a-bridge/rapports/2025-10-16_13A_RAPPORT-FINAL-BRIDGE-COMFYUI.md"

Write-Host ""
Write-Host "=== Résumé Migration ===" -ForegroundColor Cyan
Write-Host "Fichiers migrés: $migratedCount" -ForegroundColor Green
Write-Host "Erreurs: $errorCount" -ForegroundColor $(if ($errorCount -eq 0) { "Green" } else { "Red" })
Write-Host ""
Write-Host "Migration terminée!" -ForegroundColor Green