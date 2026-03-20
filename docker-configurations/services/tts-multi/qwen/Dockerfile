# Use official vLLM-Omni image for audio model support
FROM vllm/vllm-omni:v0.16.0

WORKDIR /app

# Install curl for healthcheck
RUN apt-get update && apt-get install -y --no-install-recommends curl && rm -rf /var/lib/apt/lists/*

# Copy entrypoint script
COPY entrypoint.sh /app/entrypoint.sh
RUN chmod +x /app/entrypoint.sh

# Expose port
EXPOSE 8000

# Set environment variables for Qwen3-TTS
ENV PYTHONUNBUFFERED=1
ENV VLLM_USE_MODELSCOPE=false
ENV HF_HUB_ENABLE_HF_TRANSFER=1
ENV VLLM_ALLOW_LONG_MAX_MODEL_LEN=1

# Default model type (can be overridden by docker-compose)
ENV MODEL_TYPE=CustomVoice
ENV GPU_MEMORY_UTILIZATION=0.6
ENV PORT=8000

# Use entrypoint script
ENTRYPOINT ["/app/entrypoint.sh"]
