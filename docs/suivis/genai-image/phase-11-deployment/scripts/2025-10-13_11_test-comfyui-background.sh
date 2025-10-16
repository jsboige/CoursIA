#!/bin/bash
# Phase 11: Test ComfyUI en arrière-plan avec validation
# Date: 2025-10-13

set -e

echo "================================================================"
echo "TEST COMFYUI EN ARRIÈRE-PLAN - RTX 3090"
echo "================================================================"
echo ""

# Naviguer vers ComfyUI
cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI
source venv/bin/activate

echo "=== Vérifications préalables ==="
echo "GPU: $(CUDA_VISIBLE_DEVICES=0 python3 -c 'import torch; print(torch.cuda.get_device_name(0))')"
echo "Modèle: models/checkpoints/Qwen-Image-Edit-2509-FP8"
ls -lh models/checkpoints/Qwen-Image-Edit-2509-FP8/ | head -5
echo "Custom node: custom_nodes/ComfyUI-QwenImageWanBridge"
ls -d custom_nodes/ComfyUI-QwenImageWanBridge
echo ""

# Arrêter processus existants
echo "=== Nettoyage processus existants ==="
pkill -f "python.*main.py.*8188" || echo "Aucun processus ComfyUI actif"
sleep 2
echo ""

# Créer répertoire logs
mkdir -p logs

echo "=== Lancement ComfyUI en arrière-plan ==="
echo "Port: 8188"
echo "GPU: CUDA_VISIBLE_DEVICES=0 (RTX 3090)"
echo "Logs: logs/comfyui-standalone.log"
echo ""

# Lancer ComfyUI en arrière-plan
CUDA_VISIBLE_DEVICES=0 nohup python3 main.py \
    --listen 0.0.0.0 \
    --port 8188 \
    --preview-method auto \
    > logs/comfyui-standalone.log 2>&1 &

COMFYUI_PID=$!
echo "ComfyUI lancé (PID: $COMFYUI_PID)"
echo ""

# Attendre démarrage (max 120 secondes)
echo "=== Attente démarrage ComfyUI ==="
MAX_WAIT=120
WAITED=0
while [ $WAITED -lt $MAX_WAIT ]; do
    if grep -q "To see the GUI go to" logs/comfyui-standalone.log 2>/dev/null; then
        echo "✓ ComfyUI démarré avec succès!"
        break
    fi
    
    if ! ps -p $COMFYUI_PID > /dev/null 2>&1; then
        echo "✗ ERREUR: Processus ComfyUI arrêté prématurément"
        echo "Dernières lignes du log:"
        tail -20 logs/comfyui-standalone.log
        exit 1
    fi
    
    sleep 5
    WAITED=$((WAITED + 5))
    echo "Attente... ${WAITED}s / ${MAX_WAIT}s"
done

if [ $WAITED -ge $MAX_WAIT ]; then
    echo "✗ TIMEOUT: ComfyUI n'a pas démarré dans les ${MAX_WAIT}s"
    echo "Dernières lignes du log:"
    tail -30 logs/comfyui-standalone.log
    kill $COMFYUI_PID || true
    exit 1
fi

echo ""
echo "=== Extraction informations startup ==="
grep -E "(Total VRAM|Loading:|To see the GUI)" logs/comfyui-standalone.log | tail -20
echo ""

# Test connexion HTTP
echo "=== Test connexion HTTP ==="
for i in {1..10}; do
    if curl -s http://localhost:8188 > /dev/null 2>&1; then
        echo "✓ Port 8188 accessible"
        break
    fi
    if [ $i -eq 10 ]; then
        echo "✗ ERREUR: Port 8188 inaccessible après 10 tentatives"
        exit 1
    fi
    sleep 2
done
echo ""

# Test API system_stats
echo "=== Test API system_stats ==="
STATS=$(curl -s http://localhost:8188/system_stats)
if [ ! -z "$STATS" ]; then
    echo "✓ API system_stats fonctionne"
    echo "$STATS" | python3 -m json.tool | head -20
else
    echo "✗ ERREUR: API system_stats ne répond pas"
fi
echo ""

# Afficher informations GPU en temps réel
echo "=== État GPU actuel ==="
nvidia-smi --query-gpu=index,name,memory.used,memory.total,utilization.gpu --format=csv
echo ""

echo "================================================================"
echo "COMFYUI STANDALONE OPÉRATIONNEL"
echo "================================================================"
echo "URL: http://localhost:8188"
echo "PID: $COMFYUI_PID"
echo "Logs: $(pwd)/logs/comfyui-standalone.log"
echo ""
echo "Pour arrêter: kill $COMFYUI_PID"
echo "Pour suivre logs: tail -f logs/comfyui-standalone.log"
echo ""
echo "NEXT STEP: Ouvrir http://localhost:8188 dans navigateur"
echo "           et tester workflows Qwen Image-Edit"
echo "================================================================"