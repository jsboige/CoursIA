#!/bin/bash

# Script de diagnostic ComfyUI - 2025-10-15
# Objectif: Diagnostiquer pourquoi ComfyUI ne démarre pas sur port 8188

WORKSPACE="/home/jesse/SD/workspace/comfyui-qwen/ComfyUI"
VENV="$WORKSPACE/venv"
LOG_FILE="/tmp/comfyui-debug-$(date +%Y%m%d-%H%M%S).log"

echo "=== DIAGNOSTIC COMFYUI - $(date) ===" | tee $LOG_FILE
echo "" | tee -a $LOG_FILE

# 1. Vérifier l'environnement de base
echo "## 1. ENVIRONNEMENT DE BASE" | tee -a $LOG_FILE
echo "Workspace: $WORKSPACE" | tee -a $LOG_FILE
echo "Venv: $VENV" | tee -a $LOG_FILE
echo "" | tee -a $LOG_FILE

if [ -d "$WORKSPACE" ]; then
    echo "✅ Workspace existe" | tee -a $LOG_FILE
else
    echo "❌ Workspace n'existe pas!" | tee -a $LOG_FILE
    exit 1
fi

if [ -f "$WORKSPACE/main.py" ]; then
    echo "✅ main.py trouvé" | tee -a $LOG_FILE
else
    echo "❌ main.py manquant!" | tee -a $LOG_FILE
    exit 1
fi

if [ -d "$VENV" ]; then
    echo "✅ Venv existe" | tee -a $LOG_FILE
else
    echo "❌ Venv manquant!" | tee -a $LOG_FILE
    exit 1
fi

echo "" | tee -a $LOG_FILE

# 2. Vérifier les GPUs
echo "## 2. CONFIGURATION GPU" | tee -a $LOG_FILE
nvidia-smi --query-gpu=index,name,memory.total,memory.used,temperature.gpu,utilization.gpu --format=csv | tee -a $LOG_FILE
echo "" | tee -a $LOG_FILE

# 3. Vérifier PyTorch dans le venv
echo "## 3. PYTORCH & CUDA" | tee -a $LOG_FILE
cd "$WORKSPACE"
source "$VENV/bin/activate"

python -c "
import torch
import sys

print(f'Python version: {sys.version}')
print(f'PyTorch version: {torch.__version__}')
print(f'CUDA available: {torch.cuda.is_available()}')
print(f'CUDA version: {torch.version.cuda if torch.cuda.is_available() else \"N/A\"}')
print(f'GPU count: {torch.cuda.device_count()}')

if torch.cuda.is_available():
    for i in range(torch.cuda.device_count()):
        print(f'GPU {i}: {torch.cuda.get_device_name(i)}')
        props = torch.cuda.get_device_properties(i)
        print(f'  - Memory: {props.total_memory / 1024**3:.2f} GB')
        print(f'  - Compute capability: {props.major}.{props.minor}')
" 2>&1 | tee -a $LOG_FILE

echo "" | tee -a $LOG_FILE

# 4. Test avec CUDA_VISIBLE_DEVICES
echo "## 4. TEST CUDA_VISIBLE_DEVICES=0 (RTX 3090)" | tee -a $LOG_FILE
CUDA_VISIBLE_DEVICES=0 python -c "
import torch
if torch.cuda.is_available():
    print(f'Visible GPU: {torch.cuda.get_device_name(0)}')
    props = torch.cuda.get_device_properties(0)
    print(f'VRAM: {props.total_memory / 1024**3:.2f} GB')
else:
    print('❌ CUDA non disponible avec CUDA_VISIBLE_DEVICES=0')
" 2>&1 | tee -a $LOG_FILE

echo "" | tee -a $LOG_FILE

# 5. Vérifier le port 8188
echo "## 5. VÉRIFICATION PORT 8188" | tee -a $LOG_FILE
if netstat -tulpn 2>/dev/null | grep -q ":8188"; then
    echo "⚠️  Port 8188 déjà utilisé:" | tee -a $LOG_FILE
    netstat -tulpn 2>/dev/null | grep ":8188" | tee -a $LOG_FILE
    echo "" | tee -a $LOG_FILE
    echo "Processus utilisant le port:" | tee -a $LOG_FILE
    lsof -i :8188 2>/dev/null | tee -a $LOG_FILE
else
    echo "✅ Port 8188 disponible" | tee -a $LOG_FILE
fi

echo "" | tee -a $LOG_FILE

# 6. Vérifier les dépendances critiques
echo "## 6. DÉPENDANCES CRITIQUES" | tee -a $LOG_FILE
python -c "
packages = ['torch', 'torchvision', 'torchaudio', 'transformers', 'safetensors', 'einops']
import importlib
for pkg in packages:
    try:
        module = importlib.import_module(pkg)
        version = getattr(module, '__version__', 'unknown')
        print(f'✅ {pkg}: {version}')
    except ImportError:
        print(f'❌ {pkg}: NON INSTALLÉ')
" 2>&1 | tee -a $LOG_FILE

echo "" | tee -a $LOG_FILE

# 7. Tester le démarrage de ComfyUI (mode help uniquement)
echo "## 7. TEST LANCEMENT COMFYUI (--help)" | tee -a $LOG_FILE
timeout 5 python main.py --help 2>&1 | head -20 | tee -a $LOG_FILE

echo "" | tee -a $LOG_FILE

# 8. Vérifier les logs existants
echo "## 8. LOGS RÉCENTS" | tee -a $LOG_FILE
if [ -f "/home/jesse/SD/workspace/comfyui-qwen/comfyui.log" ]; then
    echo "Dernières 30 lignes de comfyui.log:" | tee -a $LOG_FILE
    tail -30 /home/jesse/SD/workspace/comfyui-qwen/comfyui.log | tee -a $LOG_FILE
else
    echo "⚠️  Aucun log comfyui.log trouvé" | tee -a $LOG_FILE
fi

echo "" | tee -a $LOG_FILE

# 9. Vérifier custom nodes
echo "## 9. CUSTOM NODES" | tee -a $LOG_FILE
if [ -d "$WORKSPACE/custom_nodes" ]; then
    echo "Custom nodes installés:" | tee -a $LOG_FILE
    ls -1 "$WORKSPACE/custom_nodes" | tee -a $LOG_FILE
else
    echo "⚠️  Répertoire custom_nodes absent" | tee -a $LOG_FILE
fi

echo "" | tee -a $LOG_FILE
echo "=== FIN DIAGNOSTIC ===" | tee -a $LOG_FILE
echo "" | tee -a $LOG_FILE
echo "Log complet sauvegardé dans: $LOG_FILE" | tee -a $LOG_FILE
echo "Pour lancer le diagnostic complet avec démarrage réel:" | tee -a $LOG_FILE
echo "  cd $WORKSPACE && source venv/bin/activate" | tee -a $LOG_FILE
echo "  CUDA_VISIBLE_DEVICES=0 python main.py --listen 0.0.0.0 --port 8188 --preview-method auto --use-split-cross-attention" | tee -a $LOG_FILE