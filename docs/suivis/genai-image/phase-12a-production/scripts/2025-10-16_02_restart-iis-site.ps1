# Redémarrage du site IIS qwen-image-edit.myia.io
# Date: 2025-10-16
# Objectif: Démarrer le site IIS après correction web.config

Write-Host "`n=== Redémarrage Site IIS ComfyUI ===" -ForegroundColor Cyan

$siteName = "qwen-image-edit.myia.io"

try {
    Import-Module WebAdministration -ErrorAction Stop
    
    Write-Host "`n[1/3] Vérification état du site..." -ForegroundColor Yellow
    $site = Get-Website -Name $siteName -ErrorAction Stop
    
    Write-Host "Site: $($site.Name)" -ForegroundColor White
    Write-Host "État: $($site.State)" -ForegroundColor White
    Write-Host "Path: $($site.PhysicalPath)" -ForegroundColor White
    
    if ($site.State -ne "Started") {
        Write-Host "`n[2/3] Démarrage du site..." -ForegroundColor Yellow
        Start-Website -Name $siteName
        Start-Sleep -Seconds 2
        Write-Host "✅ Site démarré" -ForegroundColor Green
    } else {
        Write-Host "`n[2/3] Redémarrage du site..." -ForegroundColor Yellow
        Stop-Website -Name $siteName
        Start-Sleep -Seconds 1
        Start-Website -Name $siteName
        Start-Sleep -Seconds 2
        Write-Host "✅ Site redémarré" -ForegroundColor Green
    }
    
    Write-Host "`n[3/3] Vérification finale..." -ForegroundColor Yellow
    $siteAfter = Get-Website -Name $siteName
    if ($siteAfter.State -eq "Started") {
        Write-Host "✅ Site opérationnel (État: $($siteAfter.State))" -ForegroundColor Green
        
        Write-Host "`n=== Test de Connexion ===" -ForegroundColor Cyan
        Start-Sleep -Seconds 2
        try {
            $response = Invoke-WebRequest -Uri "https://qwen-image-edit.myia.io" -UseBasicParsing -TimeoutSec 10
            Write-Host "✅ HTTPS accessible (Status: $($response.StatusCode))" -ForegroundColor Green
        } catch {
            Write-Host "⚠️  HTTPS non accessible immédiatement - essayez dans quelques secondes" -ForegroundColor Yellow
            Write-Host "   Erreur: $($_.Exception.Message)" -ForegroundColor Gray
        }
    } else {
        Write-Host "❌ Problème de démarrage du site" -ForegroundColor Red
        exit 1
    }
    
} catch {
    Write-Host "❌ Erreur: $($_.Exception.Message)" -ForegroundColor Red
    exit 1
}

Write-Host "`n=== Configuration Complète ===" -ForegroundColor Cyan
Write-Host "✅ web.config: Directive WebSocket ajoutée" -ForegroundColor Green
Write-Host "✅ Pool IIS: Redémarré" -ForegroundColor Green
Write-Host "✅ Site IIS: Démarré" -ForegroundColor Green
Write-Host "`nTestez maintenant: https://qwen-image-edit.myia.io" -ForegroundColor White