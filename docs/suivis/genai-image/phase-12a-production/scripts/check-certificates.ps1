# Recherche certificats wildcard myia.io
$certs = Get-ChildItem Cert:\LocalMachine\My | Where-Object { 
    $_.Subject -like '**.myia.io*' -and $_.NotAfter -gt (Get-Date)
} | Select-Object Subject, Thumbprint, @{Name='Expires';Expression={$_.NotAfter}}, @{Name='DaysRemaining';Expression={($_.NotAfter - (Get-Date)).Days}}

if ($certs) {
    Write-Host "`n✅ Certificats wildcard trouvés:" -ForegroundColor Green
    $certs | Format-Table -AutoSize
    
    # Sauvegarder dans fichier
    $certs | Out-File "docs/genai-suivis/certificats-disponibles.txt"
    Write-Host "✅ Liste sauvegardée dans certificats-disponibles.txt" -ForegroundColor Green
}
else {
    Write-Host "`n⚠️ Aucun certificat wildcard *.myia.io trouvé" -ForegroundColor Yellow
    Write-Host "Recherche de tous les certificats myia.io..." -ForegroundColor Yellow
    
    $allCerts = Get-ChildItem Cert:\LocalMachine\My | Where-Object { 
        $_.Subject -like '*myia.io*' -and $_.NotAfter -gt (Get-Date)
    } | Select-Object Subject, Thumbprint, @{Name='Expires';Expression={$_.NotAfter}}, @{Name='DaysRemaining';Expression={($_.NotAfter - (Get-Date)).Days}}
    
    if ($allCerts) {
        Write-Host "`n✅ Certificats myia.io trouvés:" -ForegroundColor Green
        $allCerts | Format-Table -AutoSize
        $allCerts | Out-File "docs/genai-suivis/certificats-disponibles.txt"
    }
    else {
        Write-Host "`n❌ Aucun certificat myia.io trouvé" -ForegroundColor Red
        Write-Host "📝 Génération certificat via win-acme nécessaire" -ForegroundColor Yellow
    }
}