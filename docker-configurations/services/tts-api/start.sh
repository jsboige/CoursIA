#!/bin/bash
set -e

echo "Starting TTS API..."
echo "Device: ${TTS_DEVICE}"
echo "Default Voice: ${DEFAULT_TTS_VOICE}"

# Start uvicorn
exec uvicorn app:app --host 0.0.0.0 --port 8191 --log-level info
