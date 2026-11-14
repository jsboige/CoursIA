"""API REST locale pour le coeur d'automates finis (automata_core).

Frontend FastAPI du contrat `POST /automata/run` (pli 0 v2, #26511). Le meme
coeur `automata_core.run` sert aussi la cellule d'endpoint Kernel Gateway du
carnet Search-10-SymbolicAutomata — les deux frontends partagent la validation
et les operations, seuls les codes HTTP vivent ici.
"""

from __future__ import annotations

from typing import Any

from fastapi import FastAPI, Request
from fastapi.exceptions import RequestValidationError
from fastapi.responses import JSONResponse
from pydantic import BaseModel, ConfigDict, Field

from automata_core import (
    ALLOWED_OPS,
    AutomataInputError,
    AutomataRunError,
    run,
)


class AutomataRunRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    automaton: dict[str, Any]
    op: str = Field(default="accepts")
    word: str | None = None
    other: dict[str, Any] | None = None


def create_app() -> FastAPI:
    """Construit le service (sans dependance externe : automate-lib est pur)."""
    app = FastAPI(title="SymbolicAutomata", version="0.1.0")

    @app.exception_handler(RequestValidationError)
    async def request_validation_error_handler(
        request: Request, exc: RequestValidationError
    ) -> JSONResponse:
        del request, exc
        return JSONResponse(
            status_code=422,
            content={
                "status": "invalid",
                "error": "corps invalide : verifiez automaton, op (" +
                         ", ".join(ALLOWED_OPS) + "), word et other",
            },
        )

    @app.post("/automata/run")
    def run_endpoint(payload: AutomataRunRequest) -> JSONResponse:
        try:
            data = run(payload.model_dump())
            return JSONResponse(status_code=200, content={"status": "ok", "data": data})
        except AutomataInputError:
            return JSONResponse(
                status_code=422,
                content={
                    "status": "invalid",
                    "error": "entree invalide : verifiez automaton, op, word et other",
                },
            )
        except AutomataRunError:
            # Derniere barriere HTTP : le contrat ne renvoie jamais de trace
            # ni de detail d'exception imprevu au client.
            return JSONResponse(
                status_code=502,
                content={"status": "error", "error": "echec de l'execution de l'automate"},
            )
        except Exception:
            return JSONResponse(
                status_code=502,
                content={"status": "error", "error": "echec de l'execution de l'automate"},
            )

    return app


app = create_app()
