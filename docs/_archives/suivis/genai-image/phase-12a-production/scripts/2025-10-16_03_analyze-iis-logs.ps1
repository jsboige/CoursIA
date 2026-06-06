# Analyse des logs IIS pour erreur 500
# Date: 2025-10-16
# Objectif: Identifier la cause de l'erreur 500 sur qwen-image-edit.myia.io

Write-Host "`n=== Analyse Logs IIS ===" -ForegroundColor Cyan

# Trouver les logs les plus récents
$logsPath = "C:\inetpub\logs\LogFiles"
$todayLogs = Get-ChildItem "$logsPath\W3SVC*\u_ex251016.log" -ErrorAction SilentlyContinue | 
    Sort-Object LastWriteTime -Descending

Write-Host "`n[1/3] Logs du jour trouvés: $($todayLogs.Count)" -ForegroundColor Yellow

# Chercher les erreurs 500 dans les logs récents
Write-Host "`n[2/3] Recherche d'erreurs 500..." -ForegroundColor Yellow

$errors = @()
foreach ($log in $todayLogs | Select-Object -First 5) {
    Write-Host "  Analyse: $($log.Name)" -ForegroundColor Gray
    
    $content = Get-Content $log.FullName -ErrorAction SilentlyContinue | 
        Select-Object -Last 100 |
        Where-Object { $_ -match ' 500 ' }
    
    if ($content) {
        $errors += @{
            Log = $log.Name
            Errors = $content
        }
    }
}

Write-Host "`n[3/3] Résultats:" -ForegroundColor Yellow

if ($errors.Count -eq 0) {
    Write-Host "✅ Aucune erreur 500 trouvée dans les logs récents" -ForegroundColor Green
    Write-Host "`nLe site semble maintenant fonctionnel." -ForegroundColor White
    Write-Host "Tentez de vous reconnecter à https://qwen-image-edit.myia.io" -ForegroundColor White
} else {
    Write-Host "❌ Erreurs 500 détectées:" -ForegroundColor Red
    
    foreach ($error in $errors) {
        Write-Host "`n  Log: $($error.Log)" -ForegroundColor Yellow
        foreach ($line in $error.Errors | Select-Object -First 5) {
            Write-Host "    $line" -ForegroundColor Gray
        }
    }
    
    Write-Host "`n💡 Actions recommandées:" -ForegroundColor Cyan
    Write-Host "1. Vérifier les logs d'événements Windows" -ForegroundColor White
    Write-Host "2. Vérifier les permissions du répertoire D:\Production\qwen-image-edit.myia.io" -ForegroundColor White
    Write-Host "3. Consulter Event Viewer > Windows Logs > Application" -ForegroundColor White
}

Write-Host "`n=== Fin de l'Analyse ===" -ForegroundColor Cyan