# Wrapper pour tester le reboot Z-Image Turbo avec preuve visuelle
Write-Host "🚀 Test Z-Image Turbo Reboot (Pomme Rouge)..." -ForegroundColor Cyan

# Appel de la suite de validation avec le nouveau workflow (Reboot)
# Note: On passe le chemin relatif correct vers le workflow
$env:PYTHONPATH = "scripts/genai-auth"
# Utilisation de chemin relatif pour contrer le hardcoding dans validation_suite.py
# Le script ajoute "docker-configurations/services/comfyui-qwen/workspace/" devant le nom
python scripts/genai-auth/validation_suite.py --full --workflow ../../../../scripts/genai-auth/workflows/workflow_z_image_reboot.json

if ($LASTEXITCODE -eq 0) {
    Write-Host "✅ Succès ! L'image devrait être dans output/Z-Image-Reboot_..." -ForegroundColor Green
} else {
    Write-Host "❌ Échec du test." -ForegroundColor Red
    exit 1
}