#!/bin/bash
set -e

echo "Starting MusicGen API..."
echo "Model: ${MUSICGEN_MODEL}"
echo "Device: ${MUSICGEN_DEVICE}"

# Start uvicorn
exec uvicorn app:app --host 0.0.0.0 --port 8192 --log-level info
