# Script Configuration SSL win-acme pour qwen-image-edit.myia.io
# Date: 2025-10-15
# Nécessite: Privilèges Administrateur

$ErrorActionPreference = "Stop"

Write-Host @"
========================================
 Configuration SSL - qwen-image-edit.myia.io
========================================

Étape 1: Vérification win-acme
"@ -ForegroundColor Cyan

# Vérifier win-acme
$wacmePath = "D:\Production\win-acme.v2.2.9.1701.x64.pluggable\wacs.exe"
if (-not (Test-Path $wacmePath)) {
    Write-Host "❌ win-acme non trouvé à: $wacmePath" -ForegroundColor Red
    exit 1
}
Write-Host "✅ win-acme trouvé" -ForegroundColor Green

Write-Host @"

Étape 2: Instructions Configuration SSL
----------------------------------------

OPTION A - Ajouter au plan existant (RECOMMANDÉ si plan www.myia.io existe):
1. win-acme va s'ouvrir en mode interactif
2. Choisir: M (Manage renewals)
3. Trouver le plan 'www.myia.io' (si existe)
4. Choisir option pour modifier le plan
5. Ajouter 'qwen-image-edit.myia.io' comme SAN
6. Tester le renouvellement

OPTION B - Nouveau certificat dédié:
1. win-acme va s'ouvrir en mode interactif
2. Choisir: N (Create certificate - full options)
3. Source: 2 (Manual input)
4. Entrer: qwen-image-edit.myia.io
5. Validation: 2 ([http-01] Save verification files on path)
6. Path: D:\Production\qwen-image-edit.myia.io
7. CSR: 2 (RSA key)
8. Store: 3 (Certificate Store - Local computer)
9. Installation: 2 (IIS Web)
10. Sélectionner le site: qwen-image-edit.myia.io

Le certificat sera automatiquement associé au binding HTTPS.

"@ -ForegroundColor Yellow

$response = Read-Host "Voulez-vous lancer win-acme maintenant? (O/N)"
if ($response -eq "O" -or $response -eq "o") {
    Write-Host "`n🚀 Lancement win-acme..." -ForegroundColor Cyan
    Set-Location "D:\Production\win-acme.v2.2.9.1701.x64.pluggable"
    Start-Process -FilePath ".\wacs.exe" -Wait -NoNewWindow
    
    Write-Host "`n✅ win-acme terminé" -ForegroundColor Green
    Write-Host "Vérification de la configuration..." -ForegroundColor Cyan
    Start-Sleep -Seconds 3
    
    # Retour au répertoire projet
    Set-Location "D:\Dev\CoursIA"
    
    # Vérifier binding HTTPS
    Write-Host "`nÉtape 3: Vérification Binding HTTPS" -ForegroundColor Cyan
    Import-Module WebAdministration
    
    $httpsBinding = Get-WebBinding -Name "qwen-image-edit.myia.io" -Protocol "https"
    
    if ($httpsBinding) {
        Write-Host "✅ Binding HTTPS trouvé:" -ForegroundColor Green
        $httpsBinding | Format-List
        
        # Vérifier certificat associé
        $certHash = $httpsBinding.certificateHash
        if ($certHash) {
            $cert = Get-ChildItem Cert:\LocalMachine\My | Where-Object { $_.Thumbprint -eq $certHash }
            if ($cert) {
                Write-Host "`n✅ Certificat SSL configuré:" -ForegroundColor Green
                Write-Host "   Subject: $($cert.Subject)" -ForegroundColor White
                Write-Host "   Thumbprint: $($cert.Thumbprint)" -ForegroundColor White
                Write-Host "   Expire: $($cert.NotAfter)" -ForegroundColor White
                Write-Host "   Jours restants: $(($cert.NotAfter - (Get-Date)).Days)" -ForegroundColor White
                
                # Sauvegarder infos certificat
                $certInfo = @{
                    Subject = $cert.Subject
                    Thumbprint = $cert.Thumbprint
                    Expires = $cert.NotAfter
                    DaysRemaining = ($cert.NotAfter - (Get-Date)).Days
                }
                $certInfo | ConvertTo-Json | Out-File "docs/genai-suivis/certificat-ssl-info.json"
                Write-Host "`n✅ Informations sauvegardées dans certificat-ssl-info.json" -ForegroundColor Green
                
                # Test HTTPS
                Write-Host "`nÉtape 4: Test HTTPS" -ForegroundColor Cyan
                try {
                    $response = Invoke-WebRequest -Uri "https://qwen-image-edit.myia.io/system_stats" -UseBasicParsing
                    Write-Host "✅ HTTPS fonctionne! Status: $($response.StatusCode)" -ForegroundColor Green
                    
                    # Ouvrir dans browser
                    $openBrowser = Read-Host "`nVoulez-vous ouvrir https://qwen-image-edit.myia.io dans le navigateur? (O/N)"
                    if ($openBrowser -eq "O" -or $openBrowser -eq "o") {
                        Start-Process "https://qwen-image-edit.myia.io"
                        Write-Host "✅ Navigateur ouvert" -ForegroundColor Green
                    }
                }
                catch {
                    Write-Host "⚠️ Test HTTPS échoué: $($_.Exception.Message)" -ForegroundColor Yellow
                    Write-Host "Cela peut être normal si DNS pas encore propagé" -ForegroundColor Yellow
                }
            }
            else {
                Write-Host "⚠️ Certificat avec thumbprint $certHash non trouvé" -ForegroundColor Yellow
            }
        }
        else {
            Write-Host "⚠️ Aucun certificat associé au binding HTTPS" -ForegroundColor Yellow
            Write-Host "Relancez win-acme ou associez manuellement un certificat" -ForegroundColor Yellow
        }
    }
    else {
        Write-Host "❌ Binding HTTPS non trouvé" -ForegroundColor Red
    }
}
else {
    Write-Host "`n⏸️ Configuration SSL reportée" -ForegroundColor Yellow
    Write-Host "Lancez win-acme manuellement quand prêt:" -ForegroundColor Yellow
    Write-Host "   cd D:\Production\win-acme.v2.2.9.1701.x64.pluggable" -ForegroundColor White
    Write-Host "   .\wacs.exe" -ForegroundColor White
}

Write-Host "`n========================================" -ForegroundColor Cyan
Write-Host "Script terminé" -ForegroundColor Cyan
Write-Host "========================================`n" -ForegroundColor Cyan