#!/bin/bash
# Entrypoint script for Qwen3 TTS vLLM-Omni server
# Provides OpenAI-compatible /v1/audio/speech endpoint

MODEL_NAME="Qwen/Qwen3-TTS-12Hz-1.7B-${MODEL_TYPE:-CustomVoice}"

echo "Starting Qwen3-TTS vLLM-Omni server..."
echo "Model: $MODEL_NAME"
echo "Task Type: ${MODEL_TYPE:-CustomVoice}"
echo "GPU Memory Utilization: ${GPU_MEMORY_UTILIZATION:-0.6}"
echo "Port: ${PORT:-8000}"

# HuggingFace, never ModelScope -- and the flag must be ABSENT, not "false".
# vllm_omni 0.16.0 resolves it with `os.environ.get("VLLM_USE_MODELSCOPE", False)`
# (vllm_omni/entrypoints/omni.py:115): the string "false" is truthy in Python, so any
# non-empty value -- "false" included -- selects the ModelScope hub. Measured
# 2026-11-25: every cold start resolved the model through modelscope, whose anonymous
# metadata call fails intermittently ("Authentication token does not exist, failed to
# access model ... may not exist or may be private"), and the container could no
# longer start at all (15 restarts in 4 min). Unset = HuggingFace path, where the
# repository is public (apache-2.0).
unset VLLM_USE_MODELSCOPE

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
