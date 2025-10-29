# Script de diagnostic : Exploration structure custom node ComfyUI-QwenImageWanBridge
# Date : 2025-10-26
# Mission : Phase 26 - Recovery Workflow Qwen

Write-Host "=== EXPLORATION CUSTOM NODE QWEN ===" -ForegroundColor Cyan

$nodeDir = "/workspace/ComfyUI/custom_nodes/ComfyUI-QwenImageWanBridge"

Write-Host "`n📁 Structure du répertoire custom node..." -ForegroundColor Yellow
docker exec comfyui-qwen ls -la $nodeDir

Write-Host "`n📄 Fichiers Python (.py)..." -ForegroundColor Yellow
docker exec comfyui-qwen find $nodeDir -maxdepth 2 -name "*.py" -type f

Write-Host "`n🔍 Recherche de QwenImageSamplerNode dans les fichiers Python..." -ForegroundColor Yellow
docker exec comfyui-qwen bash -c "grep -r 'class QwenImageSamplerNode' $nodeDir --include='*.py'"

Write-Host "`n✅ Exploration terminée" -ForegroundColor Green