# Script pour diagnostiquer l'encodage du fichier
param([string]$FilePath)

if (-not $FilePath) {
    $FilePath = "corriges/demo-roo-code/04-creation-contenu/demo-1-web-orchestration-optimisee/roo_task_sep-8-2025_11-11-29-pm.md"
}

Write-Host "=== DIAGNOSTIC D'ENCODAGE ===" -ForegroundColor Yellow
Write-Host "Fichier: $FilePath" -ForegroundColor Cyan

# Vérifier l'existence du fichier
if (-not (Test-Path $FilePath)) {
    Write-Host "ERREUR: Fichier non trouvé" -ForegroundColor Red
    exit 1
}

# Lire les premiers octets pour détecter BOM
$bytes = [System.IO.File]::ReadAllBytes($FilePath)
Write-Host "`nPremiers octets (BOM check):" -ForegroundColor Yellow
$first10 = $bytes[0..9] | ForEach-Object { '{0:X2}' -f $_ }
Write-Host ($first10 -join ' ') -ForegroundColor White

# Détecter BOM
if ($bytes.Length -ge 3 -and $bytes[0] -eq 0xEF -and $bytes[1] -eq 0xBB -and $bytes[2] -eq 0xBF) {
    Write-Host "BOM UTF-8 detecté" -ForegroundColor Green
} elseif ($bytes.Length -ge 2 -and $bytes[0] -eq 0xFF -and $bytes[1] -eq 0xFE) {
    Write-Host "BOM UTF-16 LE detecté" -ForegroundColor Yellow
} elseif ($bytes.Length -ge 2 -and $bytes[0] -eq 0xFE -and $bytes[1] -eq 0xFF) {
    Write-Host "BOM UTF-16 BE detecté" -ForegroundColor Yellow
} else {
    Write-Host "Aucun BOM detecté" -ForegroundColor Red
}

# Tester différents encodages
Write-Host "`n=== TEST ENCODAGES ===" -ForegroundColor Yellow

try {
    Write-Host "`nLecture avec UTF-8:" -ForegroundColor Green
    $contentUTF8 = Get-Content -Path $FilePath -Raw -Encoding UTF8
    $preview = $contentUTF8.Substring(0, [Math]::Min(200, $contentUTF8.Length))
    Write-Host $preview -ForegroundColor White
    
    # Chercher des caractères accentués problématiques
    if ($preview -match 'Ã') {
        Write-Host "ATTENTION: Caractères corrompus détectés (Ã)" -ForegroundColor Red
    }
} catch {
    Write-Host "ERREUR UTF-8: $($_.Exception.Message)" -ForegroundColor Red
}

try {
    Write-Host "`nLecture avec Default:" -ForegroundColor Green
    $contentDefault = Get-Content -Path $FilePath -Raw -Encoding Default
    $preview2 = $contentDefault.Substring(0, [Math]::Min(200, $contentDefault.Length))
    Write-Host $preview2 -ForegroundColor White
} catch {
    Write-Host "ERREUR Default: $($_.Exception.Message)" -ForegroundColor Red
}

try {
    Write-Host "`nLecture avec UTF8NoBOM:" -ForegroundColor Green
    $contentUTF8NoBOM = [System.IO.File]::ReadAllText($FilePath, [System.Text.UTF8Encoding]::new($false))
    $preview3 = $contentUTF8NoBOM.Substring(0, [Math]::Min(200, $contentUTF8NoBOM.Length))
    Write-Host $preview3 -ForegroundColor White
    
    if ($preview3 -match 'Ã') {
        Write-Host "ATTENTION: Caractères corrompus détectés dans UTF8NoBOM aussi" -ForegroundColor Red
    } else {
        Write-Host "UTF8NoBOM semble correct" -ForegroundColor Green
    }
} catch {
    Write-Host "ERREUR UTF8NoBOM: $($_.Exception.Message)" -ForegroundColor Red
}