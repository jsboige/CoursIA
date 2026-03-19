#!/usr/bin/env python3
"""
Multi-Model TTS Gateway - Routes requests to appropriate TTS model

Path routing:
- /v1/audio/speech → Kokoro (default, backward compatible)
- /tada/v1/audio/speech → TADA 3B ML
- /qwen/v1/audio/speech → Qwen3 TTS
"""

import os
import logging
from fastapi import FastAPI, HTTPException, Request
from fastapi.responses import StreamingResponse, JSONResponse
import httpx
from typing import Optional

# Configuration
KOKORO_SERVICE_URL = os.getenv("KOKORO_SERVICE_URL", "http://tts-kokoro:8000")
TADA_SERVICE_URL = os.getenv("TADA_SERVICE_URL", "http://tts-tada:8000")
QWEN_SERVICE_URL = os.getenv("QWEN_SERVICE_URL", "http://tts-qwen:8000")

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

app = FastAPI(
    title="Multi-Model TTS Gateway",
    description="OpenAI-compatible TTS API with 3 models: Kokoro, TADA, Qwen3",
    version="1.0.0"
)

# Async HTTP client for upstream requests
client = httpx.AsyncClient(timeout=300.0)


@app.get("/health")
async def health_check():
    """Health check endpoint."""
    return {"status": "healthy", "models": ["kokoro", "tada", "qwen"]}


@app.get("/v1/models")
async def list_models():
    """List available TTS models (OpenAI-compatible format)."""
    return {
        "object": "list",
        "data": [
            {
                "id": "kokoro",
                "name": "Kokoro TTS",
                "description": "Fast, lightweight TTS model (default)",
                "path": "/v1/audio/speech"
            },
            {
                "id": "tada",
                "name": "TADA 3B ML",
                "description": "HumeAI's advanced TTS model",
                "path": "/tada/v1/audio/speech"
            },
            {
                "id": "qwen3",
                "name": "Qwen3 TTS",
                "description": "Qwen's high-quality TTS with custom voice",
                "path": "/qwen/v1/audio/speech"
            }
        ]
    }


@app.get("/v1/voices")
async def list_voices():
    """List available voices (OpenAI-compatible format)."""
    # Map voices for each model
    return {
        "voices": [
            {"id": "alloy", "name": "Alloy", "models": ["kokoro", "tada", "qwen"]},
            {"id": "echo", "name": "Echo", "models": ["kokoro", "tada"]},
            {"id": "fable", "name": "Fable", "models": ["kokoro", "tada"]},
            {"id": "onyx", "name": "Onyx", "models": ["kokoro", "tada"]},
            {"id": "nova", "name": "Nova", "models": ["kokoro", "tada"]},
            {"id": "shimmer", "name": "Shimmer", "models": ["kokoro", "tada"]},
        ]
    }


async def proxy_request(
    request: Request,
    service_url: str,
    path: str
):
    """Proxy request to upstream TTS service."""
    upstream_url = f"{service_url}{path}"

    # Forward headers
    headers = dict(request.headers)
    headers.pop("host", None)  # Remove host header

    # Get request body
    body = await request.body()

    logger.info(f"Proxying {request.method} {upstream_url}")

    try:
        # Proxy the request
        response = await client.request(
            method=request.method,
            url=upstream_url,
            headers=headers,
            content=body,
            params=request.query_params
        )

        # Handle streaming responses (audio)
        if "audio" in response.headers.get("content-type", ""):
            return StreamingResponse(
                response.aiter_bytes(),
                status_code=response.status_code,
                headers=dict(response.headers)
            )
        else:
            # Handle JSON responses
            return JSONResponse(
                content=response.json(),
                status_code=response.status_code,
                headers=dict(response.headers)
            )

    except httpx.RequestError as e:
        logger.error(f"Upstream request failed: {e}")
        raise HTTPException(status_code=503, detail=f"Service unavailable: {str(e)}")


@app.api_route("/{path:path}", methods=["GET", "POST"])
async def gateway_handler(request: Request, path: str):
    """
    Route requests to appropriate TTS service based on path prefix.

    Path patterns:
    - /tada/* → TADA service
    - /qwen/* → Qwen service
    - /v1/*, /* → Kokoro service (default)
    """
    if path.startswith("tada/"):
        # Strip "tada/" prefix and proxy to TADA service
        remaining_path = path[5:]  # Remove "tada/"
        return await proxy_request(request, TADA_SERVICE_URL, f"/{remaining_path}")

    elif path.startswith("qwen/"):
        # Strip "qwen/" prefix and proxy to Qwen service
        remaining_path = path[5:]  # Remove "qwen/"
        return await proxy_request(request, QWEN_SERVICE_URL, f"/{remaining_path}")

    else:
        # Default to Kokoro service
        return await proxy_request(request, KOKORO_SERVICE_URL, f"/{path}")


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)
