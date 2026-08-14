#!/bin/bash
set -e

echo "Starting TTS API..."
echo "Device: ${TTS_DEVICE}"
echo "Default Voice: ${DEFAULT_TTS_VOICE}"

# Kokoro requires the spaCy English model (en_core_web_sm); download it if absent
# (idempotent: skips on subsequent starts). Missing model = OSError E050 on first
# inference even though `pip install kokoro` pulled spacy itself.
if ! python -c "import spacy; spacy.load('en_core_web_sm')" 2>/dev/null; then
    echo "Downloading spaCy model en_core_web_sm..."
    python -m spacy download en_core_web_sm --quiet
fi

# Start uvicorn
exec uvicorn app:app --host 0.0.0.0 --port 8191 --log-level info
