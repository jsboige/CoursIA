#!/bin/bash
set -e

echo "Starting Qwen ASR API..."
echo "Model: ${QWEN_ASR_MODEL}"
echo "Device: ${QWEN_ASR_DEVICE}"
echo "Dtype: ${QWEN_ASR_DTYPE}"
echo "Forced Aligner: ${FORCED_ALIGNER:-disabled}"
echo "Idle Timeout: ${IDLE_TIMEOUT}s"

# Start uvicorn
exec uvicorn app:app --host 0.0.0.0 --port 8195 --log-level info
