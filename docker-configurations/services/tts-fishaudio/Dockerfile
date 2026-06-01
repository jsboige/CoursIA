# FishAudio S2-Pro TTS API Server
# Based on official fishaudio/fish-speech with custom entrypoint
#
# Downloads model from HuggingFace on first build/run:
#   fishaudio/s2-pro (~8GB)

FROM fishaudio/fish-speech:latest

WORKDIR /app

# Download model at build time if token is provided
# (Will also download at runtime if not present in checkpoints/)
RUN mkdir -p /app/checkpoints /app/references

# Expose API server port
EXPOSE 8080

# Start API server with S2-Pro model
# --half: fp16 inference (reduces VRAM from ~24GB to ~12GB)
# --listen: bind to all interfaces
# Compile disabled by default (enable with COMPILE=1 env var)
CMD ["python", "tools/api_server.py", \
     "--llama-checkpoint-path", "checkpoints/s2-pro", \
     "--decoder-checkpoint-path", "checkpoints/s2-pro/codec.pth", \
     "--listen", "0.0.0.0:8080", \
     "--half"]
