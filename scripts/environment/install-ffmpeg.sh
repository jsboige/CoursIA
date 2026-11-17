#!/bin/bash
# FFmpeg Installation Script for Linux/macOS
# Ce script installe FFmpeg avec le gestionnaire de paquets système.

set -e

FORCE=false
usage() {
    cat <<'EOF'
Usage: install-ffmpeg.sh [--force] [--help]

Installe FFmpeg avec le gestionnaire de paquets système (apt, yum, dnf ou Homebrew).
Les chemins personnalisés ne sont pas pris en charge.
EOF
}

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --force)
            FORCE=true
            shift
            ;;
        --help|-h)
            usage
            exit 0
            ;;
        --path)
            if [[ $# -lt 2 || -z "$2" || "$2" == --* ]]; then
                echo "Erreur : --path requiert un chemin non vide ; les chemins personnalisés ne sont pas pris en charge." >&2
            else
                echo "Erreur : --path '$2' n’est pas pris en charge ; FFmpeg est installé avec le gestionnaire de paquets système." >&2
            fi
            echo "Consultez --help pour connaître les options." >&2
            exit 1
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

echo "=== FFmpeg Installation Script for CoursIA ==="
echo ""

# Check if already installed
if command -v ffmpeg &> /dev/null; then
    if [ "$FORCE" = false ]; then
        echo "FFmpeg is already installed."
        ffmpeg -version | head -1
        echo ""
        echo "Use --force to reinstall."
        exit 0
    fi
fi

# Detect OS
if [[ "$OSTYPE" == "linux-gnu"* ]]; then
    echo "Detected: Linux"

    # Check for package manager
    if command -v apt-get &> /dev/null; then
        echo "Installing FFmpeg via apt..."
        sudo apt-get update
        sudo apt-get install -y ffmpeg
    elif command -v yum &> /dev/null; then
        echo "Installing FFmpeg via yum..."
        sudo yum install -y ffmpeg
    elif command -v dnf &> /dev/null; then
        echo "Installing FFmpeg via dnf..."
        sudo dnf install -y ffmpeg
    else
        echo "Error: No supported package manager found (apt/yum/dnf)"
        echo "Please install FFmpeg manually"
        exit 1
    fi

elif [[ "$OSTYPE" == "darwin"* ]]; then
    echo "Detected: macOS"

    if command -v brew &> /dev/null; then
        echo "Installing FFmpeg via Homebrew..."
        brew install ffmpeg
    else
        echo "Error: Homebrew not found"
        echo "Please install Homebrew first: https://brew.sh/"
        exit 1
    fi

else
    echo "Error: Unsupported OS: $OSTYPE"
    exit 1
fi

# Verify installation
if command -v ffmpeg &> /dev/null; then
    echo ""
    echo "=== FFmpeg installed successfully! ==="
    ffmpeg -version | head -1
    echo ""
    echo "Location: $(which ffmpeg)"
else
    echo "Error: Installation verification failed!"
    exit 1
fi
