#!/usr/bin/env python3
"""
Qwen3 TTS Service - OpenAI-compatible API via vLLM-Omni

This service starts the vLLM-Omni server for Qwen3-TTS models.

Based on: https://github.com/vllm-project/vllm-omni/tree/main/examples/online_serving/qwen3_tts

Usage:
    python app.py                          # Default: CustomVoice model
    MODEL=VoiceDesign python app.py        # VoiceDesign model
    MODEL=Base python app.py               # Base (voice clone) model
"""

import os
import sys
import subprocess
import logging

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

# Configuration
MODEL_TYPE = os.getenv("MODEL", "CustomVoice")  # CustomVoice, VoiceDesign, Base
PORT = int(os.getenv("PORT", "8000"))
GPU_MEMORY_UTILIZATION = float(os.getenv("GPU_MEMORY_UTILIZATION", "0.6"))
HOST = os.getenv("HOST", "0.0.0.0")

# Model mapping
MODELS = {
    "CustomVoice": "Qwen/Qwen3-TTS-12Hz-1.7B-CustomVoice",
    "VoiceDesign": "Qwen/Qwen3-TTS-12Hz-1.7B-VoiceDesign",
    "Base": "Qwen/Qwen3-TTS-12Hz-1.7B-Base",
}

MODEL_NAME = MODELS.get(MODEL_TYPE, MODELS["CustomVoice"])

def main():
    """Start the vLLM-Omni server for Qwen3-TTS."""

    logger.info(f"Starting Qwen3-TTS server")
    logger.info(f"Model Type: {MODEL_TYPE}")
    logger.info(f"Model: {MODEL_NAME}")
    logger.info(f"Host: {HOST}")
    logger.info(f"Port: {PORT}")
    logger.info(f"GPU Memory Utilization: {GPU_MEMORY_UTILIZATION}")

    # Build vLLM serve command
    cmd = [
        "vllm", "serve", MODEL_NAME,
        "--stage-configs-path", "vllm_omni/model_executor/stage_configs/qwen3_tts.yaml",
        "--omni",
        "--host", HOST,
        "--port", str(PORT),
        "--gpu-memory-utilization", str(GPU_MEMORY_UTILIZATION),
        "--trust-remote-code",
        "--enforce-eager",
    ]

    logger.info(f"Command: {' '.join(cmd)}")

    # Start the server
    try:
        # Use subprocess to run vLLM serve
        process = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            universal_newlines=True,
            bufsize=1
        )

        # Stream output
        for line in process.stdout:
            print(line, end='', flush=True)

        # Wait for process to complete
        return_code = process.wait()
        sys.exit(return_code)

    except KeyboardInterrupt:
        logger.info("Shutting down server...")
        process.terminate()
        process.wait()
        sys.exit(0)
    except Exception as e:
        logger.error(f"Failed to start server: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
