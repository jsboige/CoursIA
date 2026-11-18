# FishAudio S2-Pro TTS API Server
# Based on official fishaudio/fish-speech
#
# Checkpoint: official HuggingFace snapshot fishaudio/s2-pro (~11GB safetensors),
# downloaded at runtime if not present in ./checkpoints/s2-pro (see README setup).

FROM fishaudio/fish-speech:latest

WORKDIR /app

# The upstream image ships its Python in /app/.venv (not on PATH) and its
# default entrypoint (run_webui.py) intercepts CLI args: pin the api_server
# interpreter explicitly (measured 2026-10-06).
ENTRYPOINT ["/app/.venv/bin/python"]

RUN mkdir -p /app/checkpoints /app/references

# Expose API server port
EXPOSE 8080

# Start API server with S2-Pro model
# --half: fp16 inference (measured 20.3GB VRAM warm-up on a RTX 3090)
# --listen: bind to all interfaces
# Compile disabled by default
CMD ["tools/api_server.py", \
     "--llama-checkpoint-path", "checkpoints/s2-pro", \
     "--decoder-checkpoint-path", "checkpoints/s2-pro/codec.pth", \
     "--decoder-config-name", "modded_dac_vq", \
     "--listen", "0.0.0.0:8080", \
     "--half"]
