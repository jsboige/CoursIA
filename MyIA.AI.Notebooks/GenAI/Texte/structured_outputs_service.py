"""API REST locale pour le cœur Structured Outputs."""

from __future__ import annotations

from typing import Any

from fastapi import FastAPI, Request
from fastapi.exceptions import RequestValidationError
from fastapi.responses import JSONResponse
from pydantic import BaseModel, ConfigDict, Field

from structured_outputs_core import (
    StructuredExtractionError,
    StructuredInputError,
    extract_structured,
)


class ExtractRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    prompt: str
    json_schema: dict[str, Any] = Field(alias="schema")
    model: str | None = None


def create_app(client: Any | None = None) -> FastAPI:
    """Construit le service; ``client`` est une injection destinée aux tests."""
    app = FastAPI(title="Structured Outputs", version="0.1.0")
    app.state.llm_client = client

    @app.exception_handler(RequestValidationError)
    async def request_validation_error_handler(
        request: Request, exc: RequestValidationError
    ) -> JSONResponse:
        del request
        details = "; ".join(
            f"{'.'.join(str(part) for part in error['loc'][1:]) or 'body'} : {error['msg']}"
            for error in exc.errors()
        )
        return JSONResponse(
            status_code=422,
            content={"status": "invalid", "error": f"corps invalide : {details}"},
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
        except StructuredInputError as exc:
            return JSONResponse(
                status_code=422,
                content={"status": "invalid", "error": str(exc)},
            )
        except StructuredExtractionError as exc:
            return JSONResponse(
                status_code=502,
                content={"status": "error", "error": str(exc)},
            )
        except Exception as exc:
            # Dernière barrière HTTP : le contrat ne renvoie jamais de trace
            # ni de détail d'exception imprévu au client.
            return JSONResponse(
                status_code=502,
                content={"status": "error", "error": f"échec interne ({type(exc).__name__})"},
            )

    return app


app = create_app()
