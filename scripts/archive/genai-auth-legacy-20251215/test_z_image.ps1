# Wrapper pour tester le reboot Z-Image Turbo
Write-Host "🚀 Test Z-Image Turbo Reboot (Workflow corrigé)..." -ForegroundColor Cyan

# Attente de chauffe du service (si démarrage frais)
Write-Host "⏳ Attente de 30s pour stabilisation des services..." -ForegroundColor Yellow
Start-Sleep -Seconds 30

# Appel de la suite de validation avec le nouveau workflow (Reboot)
python scripts/genai-auth/validation_suite.py --full --workflow workflow_z_image_reboot.json

if ($LASTEXITCODE -eq 0) {
    Write-Host "✅ Succès ! L'image devrait être dans output/Z-Image-Reboot_..." -ForegroundColor Green
} else {
    Write-Host "❌ Échec du test." -ForegroundColor Red
    exit 1
}