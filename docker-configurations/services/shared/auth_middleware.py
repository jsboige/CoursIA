"""
Shared Bearer Token Authentication Middleware for GenAI API containers.

Usage in app.py:
    from auth_middleware import create_auth_dependency, setup_auth

    # Option 1: FastAPI dependency (per-endpoint)
    auth_required = create_auth_dependency()
    app.add_api_route("/v1/audio/transcriptions", transcribe, dependencies=[Depends(auth_required)])

    # Option 2: Global middleware (all endpoints except health)
    setup_auth(app)

Environment variables:
    API_KEY: Bearer token for authentication. If not set, auth is DISABLED (with warning).
    AUTH_ENABLED: Set to "false" to explicitly disable auth (default: true if API_KEY is set)
"""

import os
import logging
import secrets
from typing import Optional

from fastapi import FastAPI, Request, HTTPException, Depends
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials

logger = logging.getLogger("auth-middleware")

# Global config
_API_KEY: Optional[str] = None
_AUTH_ENABLED: bool = False

security = HTTPBearer(auto_error=False)


def _init_auth():
    """Initialize auth configuration from environment variables."""
    global _API_KEY, _AUTH_ENABLED

    _API_KEY = os.getenv("API_KEY", "").strip()
    auth_enabled_env = os.getenv("AUTH_ENABLED", "").strip().lower()

    if auth_enabled_env == "false":
        _AUTH_ENABLED = False
        logger.warning("AUTH_ENABLED=false - Authentication explicitly DISABLED")
    elif _API_KEY:
        _AUTH_ENABLED = True
        logger.info("Bearer token authentication ENABLED")
    else:
        _AUTH_ENABLED = False
        logger.warning(
            "API_KEY not set - Authentication DISABLED. "
            "Set API_KEY environment variable to enable auth."
        )


def is_auth_enabled() -> bool:
    """Check if authentication is enabled."""
    return _AUTH_ENABLED


def verify_token(credentials: HTTPAuthorizationCredentials = Depends(security)) -> bool:
    """Verify bearer token. Returns True if valid, raises 401 if invalid."""
    if not _AUTH_ENABLED:
        return True

    if credentials is None:
        raise HTTPException(
            status_code=401,
            detail="Missing Authorization header",
            headers={"WWW-Authenticate": "Bearer"},
        )

    if not secrets.compare_digest(credentials.credentials, _API_KEY):
        logger.warning(f"Invalid bearer token attempt from {credentials.credentials[:8]}...")
        raise HTTPException(
            status_code=401,
            detail="Invalid bearer token",
            headers={"WWW-Authenticate": "Bearer"},
        )

    return True


def create_auth_dependency():
    """Create a FastAPI dependency for bearer token authentication."""
    _init_auth()
    return verify_token


# Paths that skip authentication (health checks, docs)
_PUBLIC_PATHS = {"/health", "/docs", "/openapi.json", "/redoc"}


class BearerAuthMiddleware:
    """ASGI middleware that enforces bearer token on all non-public paths."""

    def __init__(self, app):
        self.app = app

    async def __call__(self, scope, receive, send):
        if scope["type"] != "http":
            await self.app(scope, receive, send)
            return

        path = scope.get("path", "")

        # Allow public paths without auth
        if path in _PUBLIC_PATHS or path.startswith("/admin/"):
            await self.app(scope, receive, send)
            return

        # If auth disabled, pass through
        if not _AUTH_ENABLED:
            await self.app(scope, receive, send)
            return

        # Extract Authorization header from ASGI scope
        headers = dict(scope.get("headers", []))
        auth_header = headers.get(b"authorization", b"").decode("utf-8", errors="replace")

        if not auth_header.startswith("Bearer "):
            await self._send_401(send, "Missing or invalid Authorization header")
            return

        token = auth_header[7:]  # Remove "Bearer " prefix
        if not secrets.compare_digest(token, _API_KEY):
            logger.warning(f"Invalid bearer token attempt: {token[:8]}...")
            await self._send_401(send, "Invalid bearer token")
            return

        await self.app(scope, receive, send)

    async def _send_401(self, send, detail: str):
        """Send a 401 JSON response."""
        import json

        body = json.dumps({"error": {"message": detail, "type": "authentication_error"}}).encode()
        await send({
            "type": "http.response.start",
            "status": 401,
            "headers": [
                [b"content-type", b"application/json"],
                [b"www-authenticate", b"Bearer"],
            ],
        })
        await send({
            "type": "http.response.body",
            "body": body,
        })


def setup_auth(app: FastAPI):
    """Setup authentication middleware on a FastAPI app.

    Adds BearerAuthMiddleware which checks all non-public paths.
    Public paths: /health, /docs, /openapi.json, /redoc

    Must be called AFTER CORS middleware is added.
    """
    _init_auth()

    if _AUTH_ENABLED:
        app.add_middleware(BearerAuthMiddleware)
        logger.info("Bearer auth middleware installed on all non-public endpoints")
    else:
        logger.warning("Auth middleware NOT installed - API is open")
