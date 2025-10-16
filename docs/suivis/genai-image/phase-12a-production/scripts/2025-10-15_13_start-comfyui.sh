#!/bin/bash
# ComfyUI Startup Script
# Date: 2025-10-15

cd /home/jesse/SD/workspace/comfyui-qwen/ComfyUI
source venv/bin/activate

CUDA_VISIBLE_DEVICES=0 nohup python main.py \
  --listen 0.0.0.0 \
  --port 8188 \
  --preview-method auto \
  --use-split-cross-attention \
  > /home/jesse/SD/workspace/comfyui-qwen/comfyui.log 2>&1 &

echo "ComfyUI démarré en arrière-plan, PID: $!"
echo "Logs: /home/jesse/SD/workspace/comfyui-qwen/comfyui.log"