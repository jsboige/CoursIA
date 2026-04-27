#!/bin/bash
set -e

echo "Starting FunASR API..."
echo "Model: ${FUNASR_MODEL}"
echo "Device: ${FUNASR_DEVICE}"
echo "Idle Timeout: ${IDLE_TIMEOUT}s"

# Apply compatibility patches
/app/patch-funasr.sh

# Start uvicorn
exec uvicorn app:app --host 0.0.0.0 --port 8194 --log-level info
