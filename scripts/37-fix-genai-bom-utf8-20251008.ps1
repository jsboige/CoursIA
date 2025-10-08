# Script de correction BOM UTF-8 pour les notebooks GenAI
# Corrige les problèmes d'encodage générés par PowerShell

Write-Host "CORRECTION BOM UTF-8 NOTEBOOKS GENAI" -ForegroundColor Cyan

$genaiPath = "MyIA.AI.Notebooks/GenAI"
$notebookFiles = Get-ChildItem -Path $genaiPath -Filter "*.ipynb" -Recurse

Write-Host "Fichiers notebook trouvés: $($notebookFiles.Count)" -ForegroundColor Yellow

$corrected = 0
foreach ($file in $notebookFiles) {
    try {
        # Lecture du contenu brut en bytes pour détecter BOM précisément
        $bytes = [System.IO.File]::ReadAllBytes($file.FullName)
        
        # Vérification BOM UTF-8 (EF BB BF)
        $hasBom = ($bytes.Length -ge 3 -and $bytes[0] -eq 0xEF -and $bytes[1] -eq 0xBB -and $bytes[2] -eq 0xBF)
        
        if ($hasBom) {
            # Lecture du contenu UTF-8 et suppression BOM
            $content = Get-Content -Path $file.FullName -Encoding UTF8 -Raw
            $content = $content.TrimStart([char]0xFEFF)
            
            # Réécriture sans BOM avec encodage UTF-8 strict
            $utf8NoBom = New-Object System.Text.UTF8Encoding $false
            [System.IO.File]::WriteAllText($file.FullName, $content, $utf8NoBom)
            
            Write-Host "  ✅ Corrigé BOM: $($file.Name)" -ForegroundColor Green
            $corrected++
        } else {
            Write-Host "  ✓ Pas de BOM: $($file.Name)" -ForegroundColor Gray
        }
    }
    catch {
        Write-Host "  Erreur: $($file.Name) - $($_.Exception.Message)" -ForegroundColor Red
    }
}

Write-Host "`nRÉSUMÉ CORRECTION BOM" -ForegroundColor Cyan
Write-Host "Fichiers corrigés: $corrected / $($notebookFiles.Count)" -ForegroundColor Green

if ($corrected -gt 0) {
    Write-Host "✅ Notebooks GenAI nettoyés - Compatible MCP Jupyter" -ForegroundColor Green
} else {
    Write-Host "ℹ️  Aucun BOM détecté" -ForegroundColor Gray
}