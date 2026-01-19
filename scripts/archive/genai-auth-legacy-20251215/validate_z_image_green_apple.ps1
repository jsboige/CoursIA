# Wrapper pour valider la génération "Green Apple" avec Z-Image
Write-Host "🍏 Test Z-Image Turbo (Green Apple)..." -ForegroundColor Cyan

# Configuration de l'environnement Python
$env:PYTHONPATH = "scripts/genai-auth"

# Chemin vers le workflow (relatif à workspace/ ou relatif au script)
# Le script validation_suite.py s'attend à trouver le workflow relativement à docker-configurations/services/comfyui-qwen/workspace/
# ou si on utilise ../../ on peut remonter.
# Dans test_z_image_reboot.ps1: ../../../../scripts/genai-auth/workflows/workflow_z_image_reboot.json

$workflowPath = "../../../../scripts/genai-auth/workflows/workflow_z_image_green_apple.json"

Write-Host "🚀 Lancement de la génération..."
python scripts/genai-auth/validation_suite.py --full --workflow $workflowPath

if ($LASTEXITCODE -eq 0) {
    Write-Host "✅ Workflow exécuté avec succès par l'API." -ForegroundColor Green
    
    # Vérification physique du fichier
    $outputDir = "docker-configurations/shared/outputs"
    $pattern = "Z-Image-Green-Apple_*"
    
    $latestFile = Get-ChildItem -Path $outputDir -Filter $pattern | Sort-Object LastWriteTime -Descending | Select-Object -First 1
    
    if ($latestFile) {
        Write-Host "🖼️  Image trouvée : $($latestFile.FullName)" -ForegroundColor Green
        Write-Host "📏 Taille : $($latestFile.Length) octets" -ForegroundColor Gray
        
        if ($latestFile.Length -gt 1024) {
             Write-Host "✅ Validation finale : OK" -ForegroundColor Green
        } else {
             Write-Host "⚠️  Attention : L'image semble vide ou trop petite." -ForegroundColor Yellow
        }
    } else {
        Write-Host "❌ Erreur : Fichier image introuvable dans $outputDir avec le pattern $pattern" -ForegroundColor Red
        exit 1
    }
} else {
    Write-Host "❌ Échec de l'exécution du workflow." -ForegroundColor Red
    exit 1
}