#!/bin/bash

# Script de test démarrage ComfyUI - 2025-10-15
# Objectif: Lancer ComfyUI et capturer les logs de démarrage

WORKSPACE="/home/jesse/SD/workspace/comfyui-qwen/ComfyUI"
VENV="$WORKSPACE/venv"
LOG_FILE="/tmp/comfyui-launch-$(date +%Y%m%d-%H%M%S).log"
PID_FILE="/tmp/comfyui.pid"

echo "=== TEST LANCEMENT COMFYUI - $(date) ===" | tee $LOG_FILE
echo "" | tee -a $LOG_FILE

# Nettoyer les anciens processus si nécessaire
if [ -f "$PID_FILE" ]; then
    OLD_PID=$(cat $PID_FILE)
    if ps -p $OLD_PID > /dev/null 2>&1; then
        echo "⚠️  Ancien processus ComfyUI détecté (PID: $OLD_PID)" | tee -a $LOG_FILE
        echo "   Arrêt du processus..." | tee -a $LOG_FILE
        kill $OLD_PID 2>/dev/null
        sleep 2
        if ps -p $OLD_PID > /dev/null 2>&1; then
            kill -9 $OLD_PID 2>/dev/null
        fi
        rm -f $PID_FILE
    fi
fi

# Vérifier qu'aucun processus n'utilise le port 8188
if netstat -tulpn 2>/dev/null | grep -q ":8188"; then
    echo "❌ Port 8188 occupé!" | tee -a $LOG_FILE
    netstat -tulpn 2>/dev/null | grep ":8188" | tee -a $LOG_FILE
    echo "" | tee -a $LOG_FILE
    echo "Voulez-vous tuer le processus? (y/n)" | tee -a $LOG_FILE
    read -t 10 -n 1 answer
    if [ "$answer" = "y" ]; then
        PID_8188=$(lsof -ti:8188)
        kill $PID_8188 2>/dev/null
        sleep 2
    else
        echo "Abandon du test." | tee -a $LOG_FILE
        exit 1
    fi
fi

echo "## 1. PRÉPARATION" | tee -a $LOG_FILE
cd "$WORKSPACE"
source "$VENV/bin/activate"
echo "✅ Venv activé" | tee -a $LOG_FILE
echo "✅ Working directory: $(pwd)" | tee -a $LOG_FILE
echo "" | tee -a $LOG_FILE

echo "## 2. LANCEMENT COMFYUI" | tee -a $LOG_FILE
echo "Commande:" | tee -a $LOG_FILE
echo "  CUDA_VISIBLE_DEVICES=0 python main.py --listen 0.0.0.0 --port 8188 --preview-method auto --use-split-cross-attention" | tee -a $LOG_FILE
echo "" | tee -a $LOG_FILE

# Créer un log temporaire pour la sortie
COMFYUI_LOG="/tmp/comfyui-output-$(date +%Y%m%d-%H%M%S).log"

# Lancer ComfyUI en background avec redirection des logs
CUDA_VISIBLE_DEVICES=0 nohup python main.py \
    --listen 0.0.0.0 \
    --port 8188 \
    --preview-method auto \
    --use-split-cross-attention \
    > "$COMFYUI_LOG" 2>&1 &

COMFYUI_PID=$!
echo $COMFYUI_PID > $PID_FILE

echo "✅ ComfyUI lancé (PID: $COMFYUI_PID)" | tee -a $LOG_FILE
echo "📝 Logs en cours d'écriture dans: $COMFYUI_LOG" | tee -a $LOG_FILE
echo "" | tee -a $LOG_FILE

echo "## 3. ATTENTE DÉMARRAGE (30 secondes)" | tee -a $LOG_FILE
for i in {1..30}; do
    echo -n "." | tee -a $LOG_FILE
    sleep 1
    
    # Vérifier si le processus est toujours actif
    if ! ps -p $COMFYUI_PID > /dev/null 2>&1; then
        echo "" | tee -a $LOG_FILE
        echo "❌ Le processus ComfyUI s'est arrêté prématurément!" | tee -a $LOG_FILE
        echo "" | tee -a $LOG_FILE
        echo "Logs du processus:" | tee -a $LOG_FILE
        cat "$COMFYUI_LOG" | tee -a $LOG_FILE
        exit 1
    fi
    
    # Tester la connexion au port 8188 tous les 5 secondes
    if [ $((i % 5)) -eq 0 ]; then
        if curl -s http://localhost:8188/system_stats > /dev/null 2>&1; then
            echo "" | tee -a $LOG_FILE
            echo "✅ Port 8188 répond après $i secondes!" | tee -a $LOG_FILE
            break
        fi
    fi
done

echo "" | tee -a $LOG_FILE
echo "" | tee -a $LOG_FILE

echo "## 4. VÉRIFICATION PORT 8188" | tee -a $LOG_FILE
if curl -s http://localhost:8188/system_stats > /dev/null 2>&1; then
    echo "✅ ComfyUI répond sur port 8188" | tee -a $LOG_FILE
    echo "" | tee -a $LOG_FILE
    
    echo "Statistiques système:" | tee -a $LOG_FILE
    curl -s http://localhost:8188/system_stats | python3 -m json.tool 2>/dev/null | head -30 | tee -a $LOG_FILE
else
    echo "❌ Port 8188 ne répond pas!" | tee -a $LOG_FILE
    echo "" | tee -a $LOG_FILE
    
    echo "Vérification netstat:" | tee -a $LOG_FILE
    netstat -tulpn 2>/dev/null | grep ":8188" | tee -a $LOG_FILE
fi

echo "" | tee -a $LOG_FILE

echo "## 5. ÉTAT PROCESSUS" | tee -a $LOG_FILE
if ps -p $COMFYUI_PID > /dev/null 2>&1; then
    echo "✅ Processus ComfyUI actif (PID: $COMFYUI_PID)" | tee -a $LOG_FILE
    ps aux | grep $COMFYUI_PID | grep -v grep | tee -a $LOG_FILE
else
    echo "❌ Processus ComfyUI arrêté" | tee -a $LOG_FILE
fi

echo "" | tee -a $LOG_FILE

echo "## 6. LOGS COMFYUI (50 premières lignes)" | tee -a $LOG_FILE
head -50 "$COMFYUI_LOG" | tee -a $LOG_FILE

echo "" | tee -a $LOG_FILE
echo "## 7. GPU STATS" | tee -a $LOG_FILE
nvidia-smi --query-gpu=index,name,memory.used,memory.total,temperature.gpu,utilization.gpu --format=csv | tee -a $LOG_FILE

echo "" | tee -a $LOG_FILE
echo "=== FIN TEST ===" | tee -a $LOG_FILE
echo "" | tee -a $LOG_FILE
echo "📝 Rapport complet: $LOG_FILE" | tee -a $LOG_FILE
echo "📝 Logs ComfyUI complets: $COMFYUI_LOG" | tee -a $LOG_FILE
echo "🔧 PID ComfyUI: $COMFYUI_PID (sauvegardé dans $PID_FILE)" | tee -a $LOG_FILE
echo "" | tee -a $LOG_FILE
echo "Pour voir les logs en continu:" | tee -a $LOG_FILE
echo "  tail -f $COMFYUI_LOG" | tee -a $LOG_FILE
echo "" | tee -a $LOG_FILE
echo "Pour arrêter ComfyUI:" | tee -a $LOG_FILE
echo "  kill $COMFYUI_PID" | tee -a $LOG_FILE
echo "  # ou" | tee -a $LOG_FILE
echo "  kill \$(cat $PID_FILE)" | tee -a $LOG_FILE