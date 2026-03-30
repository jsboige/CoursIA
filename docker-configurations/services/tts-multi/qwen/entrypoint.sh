#!/bin/bash
# Entrypoint script for Qwen3 TTS vLLM-Omni server
# Provides OpenAI-compatible /v1/audio/speech endpoint

MODEL_NAME="Qwen/Qwen3-TTS-12Hz-1.7B-${MODEL_TYPE:-CustomVoice}"

echo "Starting Qwen3-TTS vLLM-Omni server..."
echo "Model: $MODEL_NAME"
echo "Task Type: ${MODEL_TYPE:-CustomVoice}"
echo "GPU Memory Utilization: ${GPU_MEMORY_UTILIZATION:-0.6}"
echo "Port: ${PORT:-8000}"

# Force HuggingFace download (not ModelScope) to avoid path mangling
export VLLM_USE_MODELSCOPE=false

# Launch vLLM-Omni server with TTS support
# The --omni flag enables multi-modal (audio) support
# The --stage-configs-path is required for Qwen3-TTS
exec vllm serve "$MODEL_NAME" \
    --stage-configs-path /usr/local/lib/python3.12/dist-packages/vllm_omni/model_executor/stage_configs/qwen3_tts.yaml \
    --omni \
    --host 0.0.0.0 \
    --port "${PORT:-8000}" \
    --gpu-memory-utilization "${GPU_MEMORY_UTILIZATION:-0.6}" \
    --trust-remote-code \
    --enforce-eager
