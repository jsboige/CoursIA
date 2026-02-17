# FFmpeg Installation Script for Windows
# This script downloads and installs FFmpeg locally for the CoursIA project

param(
    [string]$InstallPath = "D:\Dev\CoursIA\tools\ffmpeg",
    [switch]$Force = $false
)

$ErrorActionPreference = "Stop"

Write-Host "=== FFmpeg Installation Script for CoursIA ===" -ForegroundColor Cyan
Write-Host ""

# Check if already installed
if (Test-Path "$InstallPath\bin\ffmpeg.exe") {
    if (-not $Force) {
        Write-Host "FFmpeg is already installed at: $InstallPath" -ForegroundColor Green
        $version = & "$InstallPath\bin\ffmpeg.exe" -version 2>&1 | Select-Object -First 1
        Write-Host "Version: $version" -ForegroundColor Gray
        Write-Host ""
        Write-Host "Use -Force to reinstall." -ForegroundColor Yellow
        exit 0
    }
    Write-Host "Removing existing installation..." -ForegroundColor Yellow
    Remove-Item -Path $InstallPath -Recurse -Force
}

# Create installation directory
Write-Host "Creating installation directory: $InstallPath" -ForegroundColor Cyan
New-Item -ItemType Directory -Path $InstallPath -Force | Out-Null

# Download FFmpeg
$ffmpegUrl = "https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip"
$zipPath = "$env:TEMP\ffmpeg-release-essentials.zip"

Write-Host "Downloading FFmpeg from: $ffmpegUrl" -ForegroundColor Cyan
Write-Host "This may take a few minutes (file size: ~100 MB)..." -ForegroundColor Gray

try {
    # Use ProgressPreference for faster download
    $ProgressPreference = 'SilentlyContinue'
    Invoke-WebRequest -Uri $ffmpegUrl -OutFile $zipPath -UseBasicParsing
    $ProgressPreference = 'Continue'
} catch {
    Write-Host "Download failed: $_" -ForegroundColor Red
    exit 1
}

Write-Host "Download complete. Extracting..." -ForegroundColor Green

# Extract only the ffmpeg folder
Write-Host "Extracting FFmpeg files..." -ForegroundColor Cyan
try {
    # Use Expand-Archive (built into PowerShell 5+)
    $tempExtract = "$env:TEMP\ffmpeg_extract"
    if (Test-Path $tempExtract) { Remove-Item -Path $tempExtract -Recurse -Force }
    New-Item -ItemType Directory -Path $tempExtract -Force | Out-Null

    Expand-Archive -Path $zipPath -DestinationPath $tempExtract -Force

    # Find the extracted folder
    $extractedFolder = Get-ChildItem -Path $tempExtract -Directory | Select-Object -First 1
    $ffmpegSource = Join-Path $extractedFolder.FullName "ffmpeg-*-essentials_build"

    # Copy to install location
    Write-Host "Copying files to: $InstallPath" -ForegroundColor Cyan
    Copy-Item -Path "$ffmpegSource\*" -Destination $InstallPath -Recurse -Force

    # Cleanup
    Write-Host "Cleaning up temporary files..." -ForegroundColor Gray
    Remove-Item -Path $zipPath -Force
    Remove-Item -Path $tempExtract -Recurse -Force

} catch {
    Write-Host "Extraction failed: $_" -ForegroundColor Red
    exit 1
}

# Verify installation
if (Test-Path "$InstallPath\bin\ffmpeg.exe") {
    Write-Host ""
    Write-Host "=== FFmpeg installed successfully! ===" -ForegroundColor Green
    Write-Host "Location: $InstallPath" -ForegroundColor Cyan
    $version = & "$InstallPath\bin\ffmpeg.exe" -version 2>&1 | Select-Object -First 1
    Write-Host "Version: $version" -ForegroundColor Gray
    Write-Host ""
    Write-Host "The scripts/genai-stack/commands/notebooks.py will automatically" -ForegroundColor White
    Write-Host "add this location to PATH when executing notebooks." -ForegroundColor White
    Write-Host ""
    Write-Host "You can also add it manually to your system PATH:" -ForegroundColor Yellow
    Write-Host "  $InstallPath\bin" -ForegroundColor Gray
    exit 0
} else {
    Write-Host "Installation verification failed!" -ForegroundColor Red
    exit 1
}
