"""API REST locale pour le cœur Structured Outputs."""

from __future__ import annotations

from contextlib import asynccontextmanager
from typing import Any

from fastapi import FastAPI, Request
from fastapi.exceptions import RequestValidationError
from fastapi.responses import JSONResponse
from pydantic import BaseModel, ConfigDict, Field

from structured_outputs_core import (
    StructuredExtractionError,
    StructuredInputError,
    _configured_client,
    extract_structured,
)


class ExtractRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    prompt: str
    json_schema: dict[str, Any] = Field(alias="schema")
    model: str | None = None


def create_app(client: Any | None = None) -> FastAPI:
    """Construit le service; ``client`` est une injection destinée aux tests."""
    @asynccontextmanager
    async def lifespan(app: FastAPI):
        owns_client = client is None
        active_client = _configured_client() if owns_client else client
        app.state.llm_client = active_client
        try:
            yield
        finally:
            if owns_client:
                active_client.close()

    app = FastAPI(title="Structured Outputs", version="0.1.0", lifespan=lifespan)
    # Les tests peuvent exercer l'application ASGI sans démarrer son lifespan.
    # L'injection est externe et ne doit jamais être fermée par le service.
    app.state.llm_client = client

    @app.exception_handler(RequestValidationError)
    async def request_validation_error_handler(
        request: Request, exc: RequestValidationError
    ) -> JSONResponse:
        del request, exc
        return JSONResponse(
            status_code=422,
            content={"status": "invalid", "error": "corps invalide : vérifiez prompt, schema et model"},
        )

    @app.post("/texte/extract")
    def extract(payload: ExtractRequest) -> JSONResponse:
        try:
            data = extract_structured(
                prompt=payload.prompt,
                schema=payload.json_schema,
                model=payload.model,
                client=app.state.llm_client,
            )
            # Les réponses API sont JSON; Pydantic BaseModel est également
            # serialisable par FastAPI si le même cœur est appelé avec un modèle.
            if isinstance(data, BaseModel):
                data = data.model_dump(mode="json")
            return JSONResponse(status_code=200, content={"status": "ok", "data": data})
        except StructuredInputError:
            return JSONResponse(
                status_code=422,
                content={"status": "invalid", "error": "entrée invalide : vérifiez prompt, schema et model"},
            )
        except StructuredExtractionError:
            return JSONResponse(
                status_code=502,
                content={"status": "error", "error": "échec de l'extraction structurée"},
            )
        except Exception:
            # Dernière barrière HTTP : le contrat ne renvoie jamais de trace
            # ni de détail d'exception imprévu au client.
            return JSONResponse(
                status_code=502,
                content={"status": "error", "error": "échec de l'extraction structurée"},
            )

    return app


app = create_app()
