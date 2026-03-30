# Script de conversion WebP vers JPEG
# Usage: .\convert-webp-to-jpg.ps1

param(
    [string]$WebpPath = "ateliers/demo-roo-code/01-decouverte/demo-2-vision/ressources/uml-class-diagram.webp",
    [string]$JpgPath = "ateliers/demo-roo-code/01-decouverte/demo-2-vision/ressources/uml-class-diagram.jpg"
)

Write-Host "Début de la conversion WebP vers JPEG..."
Write-Host "Source: $WebpPath"
Write-Host "Destination: $JpgPath"

# Vérifier si le fichier source existe
if (-not (Test-Path $WebpPath)) {
    Write-Error "Le fichier source WebP n'existe pas: $WebpPath"
    exit 1
}

try {
    # Méthode 1: Essayer avec .NET System.Drawing
    Write-Host "Tentative de conversion avec .NET System.Drawing..."
    Add-Type -AssemblyName System.Drawing
    
    $fullWebpPath = (Resolve-Path $WebpPath).Path
    $fullJpgPath = Join-Path (Get-Location) $JpgPath
    
    $image = [System.Drawing.Image]::FromFile($fullWebpPath)
    $image.Save($fullJpgPath, [System.Drawing.Imaging.ImageFormat]::Jpeg)
    $image.Dispose()
    
    Write-Host "✅ Conversion réussie avec .NET System.Drawing" -ForegroundColor Green
    
    # Afficher les informations du fichier créé
    if (Test-Path $JpgPath) {
        $fileInfo = Get-Item $JpgPath
        Write-Host "Fichier créé:" -ForegroundColor Green
        Write-Host "  - Nom: $($fileInfo.Name)"
        Write-Host "  - Taille: $($fileInfo.Length) octets"
        Write-Host "  - Date: $($fileInfo.LastWriteTime)"
    }
} catch {
    Write-Warning "Échec avec .NET System.Drawing: $($_.Exception.Message)"
    
    try {
        # Méthode 2: Essayer avec ImageMagick
        Write-Host "Tentative de conversion avec ImageMagick..."
        & magick convert $WebpPath $JpgPath
        
        if (Test-Path $JpgPath) {
            Write-Host "✅ Conversion réussie avec ImageMagick" -ForegroundColor Green
            $fileInfo = Get-Item $JpgPath
            Write-Host "Fichier créé:" -ForegroundColor Green
            Write-Host "  - Nom: $($fileInfo.Name)"
            Write-Host "  - Taille: $($fileInfo.Length) octets"
            Write-Host "  - Date: $($fileInfo.LastWriteTime)"
        } else {
            throw "La conversion avec ImageMagick a échoué"
        }
    } catch {
        Write-Warning "Échec avec ImageMagick: $($_.Exception.Message)"
        
        # Méthode 3: Solution temporaire - copier le fichier avec extension .jpg
        Write-Host "Solution temporaire: copie du fichier avec extension .jpg..."
        Copy-Item $WebpPath $JpgPath -Force
        
        if (Test-Path $JpgPath) {
            Write-Host "⚠️  Fichier copié avec extension .jpg (conversion manuelle nécessaire)" -ForegroundColor Yellow
            $fileInfo = Get-Item $JpgPath
            Write-Host "Fichier créé:" -ForegroundColor Yellow
            Write-Host "  - Nom: $($fileInfo.Name)"
            Write-Host "  - Taille: $($fileInfo.Length) octets"
            Write-Host "  - Date: $($fileInfo.LastWriteTime)"
            Write-Host ""
            Write-Host "ATTENTION: Le fichier est toujours au format WebP mais avec extension .jpg" -ForegroundColor Red
            Write-Host "Pour une vraie conversion, installez ImageMagick ou utilisez un autre outil." -ForegroundColor Red
        } else {
            Write-Error "Toutes les méthodes de conversion ont échoué"
            exit 1
        }
    }
}

Write-Host "Script terminé." -ForegroundColor Green