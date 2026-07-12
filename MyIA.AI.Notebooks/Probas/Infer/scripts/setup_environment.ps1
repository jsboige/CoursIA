# Setup script for Infer.NET Notebooks
# This script installs all required dependencies for running the Infer.NET notebook series

param(
    [switch]$SkipDotnetInteractive,
    [switch]$SkipPapermill,
    [switch]$Verbose
)

$ErrorActionPreference = "Stop"

function Write-Status {
    param([string]$Message, [string]$Color = "Cyan")
    Write-Host "[$([DateTime]::Now.ToString('HH:mm:ss'))] $Message" -ForegroundColor $Color
}

function Test-Command {
    param([string]$Command)
    $null = Get-Command $Command -ErrorAction SilentlyContinue
    return $?
}

Write-Status "=== Infer.NET Notebooks Environment Setup ===" "Green"

# Check .NET SDK
Write-Status "Checking .NET SDK..."
if (Test-Command "dotnet") {
    $dotnetVersion = dotnet --version
    Write-Status "  .NET SDK found: $dotnetVersion" "Green"
} else {
    Write-Status "  .NET SDK not found. Please install from https://dotnet.microsoft.com/download" "Red"
    exit 1
}

# Check/Install dotnet-interactive
if (-not $SkipDotnetInteractive) {
    Write-Status "Checking dotnet-interactive..."
    $toolList = dotnet tool list -g 2>$null
    if ($toolList -match "microsoft.dotnet-interactive") {
        Write-Status "  dotnet-interactive already installed" "Green"
    } else {
        Write-Status "  Installing dotnet-interactive..."
        dotnet tool install -g Microsoft.dotnet-interactive
        if ($LASTEXITCODE -eq 0) {
            Write-Status "  dotnet-interactive installed successfully" "Green"
        } else {
            Write-Status "  Failed to install dotnet-interactive" "Red"
            exit 1
        }
    }

    # Register Jupyter kernels
    Write-Status "Registering .NET Interactive Jupyter kernels..."
    dotnet interactive jupyter install
    if ($LASTEXITCODE -eq 0) {
        Write-Status "  Kernels registered successfully" "Green"
    } else {
        Write-Status "  Warning: Could not register kernels (may already exist)" "Yellow"
    }
}

# Check Python and pip
Write-Status "Checking Python..."
if (Test-Command "python") {
    $pythonVersion = python --version
    Write-Status "  Python found: $pythonVersion" "Green"
} else {
    Write-Status "  Python not found. Please install Python 3.8+" "Red"
    exit 1
}

# Check/Install papermill
if (-not $SkipPapermill) {
    Write-Status "Checking papermill..."
    $papermillInstalled = python -c "import papermill" 2>$null
    if ($LASTEXITCODE -eq 0) {
        Write-Status "  papermill already installed" "Green"
    } else {
        Write-Status "  Installing papermill..."
        pip install papermill jupyter
        if ($LASTEXITCODE -eq 0) {
            Write-Status "  papermill installed successfully" "Green"
        } else {
            Write-Status "  Failed to install papermill" "Red"
            exit 1
        }
    }
}

# List available Jupyter kernels
Write-Status "Available Jupyter kernels:"
jupyter kernelspec list

Write-Status ""
Write-Status "=== Setup Complete ===" "Green"
Write-Status "You can now run the Infer.NET notebooks in:"
Write-Status "  MyIA.AI.Notebooks/Probas/Infer/"
Write-Status ""
Write-Status "To test notebooks with papermill:"
Write-Status "  python scripts/infer-notebooks/test_notebooks.py"
