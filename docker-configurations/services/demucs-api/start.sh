#!/bin/bash
set -e

echo "Starting Demucs API..."
echo "Model: ${DEMUCS_MODEL}"
echo "Device: ${DEMUCS_DEVICE}"

# Start uvicorn
exec uvicorn app:app --host 0.0.0.0 --port 8193 --log-level info
