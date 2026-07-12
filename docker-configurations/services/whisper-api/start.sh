#!/bin/bash
set -e

echo "Starting Whisper API..."
echo "Model: ${WHISPER_MODEL}"
echo "Device: ${WHISPER_DEVICE}"
echo "Compute Type: ${WHISPER_COMPUTE_TYPE}"

# Start uvicorn
exec uvicorn app:app --host 0.0.0.0 --port 8190 --log-level info
