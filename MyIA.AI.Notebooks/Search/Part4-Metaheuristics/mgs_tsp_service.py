"""API REST locale pour le coeur TSP (mgs_tsp_core).

Frontend FastAPI du contrat `POST /search/tsp` (pli 0 v2, #27218). Le meme coeur
`mgs_tsp_core.run` sert aussi la cellule d'endpoint Kernel Gateway du carnet
MGS-07-TSP — les deux frontends partagent la validation et l'optimisation, seuls
les codes HTTP vivent ici.
"""

from __future__ import annotations

from typing import Any

from fastapi import FastAPI, Request
from fastapi.exceptions import RequestValidationError
from fastapi.responses import JSONResponse
from pydantic import BaseModel, ConfigDict, Field

from mgs_tsp_core import (
    ALLOWED_ALGORITHMS,
    TspInputError,
    TspRunError,
    run,
)


class CityModel(BaseModel):
    model_config = ConfigDict(extra="forbid")

    name: str
    x: float
    y: float


class TspParamsModel(BaseModel):
    model_config = ConfigDict(extra="forbid")

    population: int = Field(default=100)
    generations: int = Field(default=500)
    seed: int = Field(default=42)
    island_nb: int = Field(default=4)
    migration_period: int = Field(default=5)
    migration_mode: str = Field(default="Static")


class TspRunRequest(BaseModel):
    model_config = ConfigDict(extra="forbid")

    cities: list[CityModel]
    algorithm: str = Field(default="ga")
    params: TspParamsModel = Field(default_factory=TspParamsModel)


def create_app() -> FastAPI:
    """Construit le service TSP (sans dependance externe : le coeur est pur Python)."""
    app = FastAPI(title="MGS-TSP", version="0.1.0")

    @app.exception_handler(RequestValidationError)
    async def request_validation_error_handler(
        request: Request, exc: RequestValidationError
    ) -> JSONResponse:
        del request, exc
        return JSONResponse(
            status_code=422,
            content={
                "status": "invalid",
                "error": "corps invalide : verifiez cities (name, x, y), algorithm ("
                         + ", ".join(ALLOWED_ALGORITHMS) + ") et params",
            },
        )

    @app.post("/search/tsp")
    def run_endpoint(payload: TspRunRequest) -> JSONResponse:
        try:
            data = run(payload.model_dump())
            return JSONResponse(status_code=200, content={"status": "ok", "data": data})
        except TspInputError as exc:
            return JSONResponse(
                status_code=422,
                content={"status": "invalid", "error": str(exc)},
            )
        except TspRunError:
            # Derniere barriere HTTP : le contrat ne renvoie jamais de trace
            # ni de detail d'exception imprevu au client.
            return JSONResponse(
                status_code=502,
                content={"status": "error", "error": "echec de l'optimisation TSP"},
            )
        except Exception:
            return JSONResponse(
                status_code=502,
                content={"status": "error", "error": "echec de l'optimisation TSP"},
            )

    return app


app = create_app()
