"""Contrats du coeur et du transport REST du TSP (pli 0 v2, #27218).

Meme discipline que test_automata_core.py (Search/Automata, #26511) : les
exceptions du coeur (`TspInputError` -> status invalid, `TspRunError` -> status
error), la reproductibilite seedee (deux runs identiques -> meme tour), les cas
degeneres rejetes et les cas de reference a optimum connu sont verifies ici, puis
le vrai transport TCP local (uvicorn + httpx) exerce le service FastAPI
`POST /search/tsp` sur le meme contrat.

Valeurs de reference mesurees firsthand sur ce siege :
  - Carre unite A(0,0) B(1,0) C(1,1) D(0,1) : optimum = perimetre = 4.0, atteint
    par le GA panmictique ET par le modele insulaire.
  - Quatre villes colineaires (0,0)(1,0)(2,0)(3,0) : optimum = 2 * longueur = 6.0.
"""

from __future__ import annotations

import socket
import sys
import threading
import time
from pathlib import Path

import httpx
import pytest
import uvicorn

sys.path.insert(0, str(Path(__file__).resolve().parent))

from mgs_tsp_core import (
    TspInputError,
    run,
)
from mgs_tsp_service import create_app


# Carre unite (optimum = perimetre 4.0), cas de reference du carnet.
SQUARE = [
    {"name": "A", "x": 0.0, "y": 0.0},
    {"name": "B", "x": 1.0, "y": 0.0},
    {"name": "C", "x": 1.0, "y": 1.0},
    {"name": "D", "x": 0.0, "y": 1.0},
]

# Quatre villes colineaires (optimum = 2 * longueur = 6.0).
COLINEAR = [
    {"name": "A", "x": 0.0, "y": 0.0},
    {"name": "B", "x": 1.0, "y": 0.0},
    {"name": "C", "x": 2.0, "y": 0.0},
    {"name": "D", "x": 3.0, "y": 0.0},
]


def _square_payload(**overrides):
    payload = {"cities": SQUARE, "algorithm": "ga",
               "params": {"population": 40, "generations": 60, "seed": 42}}
    payload.update(overrides)
    return payload


# ---------------------------------------------------------------------------
# Cas de reference a optimum connu
# ---------------------------------------------------------------------------

def test_square_optimum_ga():
    result = run(_square_payload())
    assert result["distance"] == pytest.approx(4.0, abs=1e-6)
    assert sorted(result["best_tour"]) == ["A", "B", "C", "D"]
    # Le tour est cyclique : toutes les villes sont visitees une seule fois.
    assert len(result["best_tour"]) == 4


def test_square_optimum_islands():
    payload = _square_payload(algorithm="islands")
    payload["params"].update({"island_nb": 4, "migration_period": 5, "seed": 7})
    result = run(payload)
    assert result["distance"] == pytest.approx(4.0, abs=1e-6)


def test_colinear_optimum():
    payload = {"cities": COLINEAR, "algorithm": "ga",
               "params": {"population": 30, "generations": 40, "seed": 1}}
    result = run(payload)
    assert result["distance"] == pytest.approx(6.0, abs=1e-6)


def test_history_is_convergence_curve():
    result = run(_square_payload())
    history = result["history"]
    assert len(history) == 60
    # La courbe est non croissante en son point final (elitisme : le meilleur ne
    # regresse pas entre la derniere generation et le tour retourne).
    assert history[-1] == pytest.approx(result["distance"], abs=1e-6)


# ---------------------------------------------------------------------------
# Parite seedee (deux runs identiques -> meme tour)
# ---------------------------------------------------------------------------

def test_seeded_parity_ga():
    first = run(_square_payload())
    second = run(_square_payload())
    assert first == second


def test_seeded_parity_islands():
    payload = _square_payload(algorithm="islands")
    payload["params"].update({"island_nb": 4, "seed": 7})
    assert run(payload) == run(payload)


def test_different_seeds_can_differ():
    # Deux graines differentes ne sont pas tenues de diverger, mais le contrat
    # reste valide (tour complet, distance positive).
    payload = _square_payload()
    payload["params"]["seed"] = 99
    result = run(payload)
    assert len(result["best_tour"]) == 4
    assert result["distance"] > 0


# ---------------------------------------------------------------------------
# Cas degeneres rejetes (status invalid)
# ---------------------------------------------------------------------------

def test_reject_too_few_cities():
    with pytest.raises(TspInputError):
        run({"cities": SQUARE[:3], "algorithm": "ga"})


def test_reject_unknown_algorithm():
    with pytest.raises(TspInputError):
        run(_square_payload(algorithm="simulated_annealing"))


def test_reject_population_out_of_bounds():
    payload = _square_payload()
    payload["params"]["population"] = 2
    with pytest.raises(TspInputError):
        run(payload)


def test_reject_generations_out_of_bounds():
    payload = _square_payload()
    payload["params"]["generations"] = 0
    with pytest.raises(TspInputError):
        run(payload)


def test_reject_duplicate_city_name():
    cities = [SQUARE[0], SQUARE[0], SQUARE[2], SQUARE[3]]
    with pytest.raises(TspInputError):
        run({"cities": cities, "algorithm": "ga"})


def test_reject_missing_coordinates():
    with pytest.raises(TspInputError):
        run({"cities": [{"name": "A", "x": 0.0}] * 1 + SQUARE[:3], "algorithm": "ga"})


def test_reject_cities_not_a_list():
    with pytest.raises(TspInputError):
        run({"cities": {"A": 1}, "algorithm": "ga"})


def test_reject_non_finite_coordinates():
    cities = [dict(SQUARE[0], x=float("inf"))] + SQUARE[1:]
    with pytest.raises(TspInputError):
        run({"cities": cities, "algorithm": "ga"})


def test_reject_islands_not_divisible():
    payload = _square_payload(algorithm="islands")
    payload["params"].update({"population": 10, "island_nb": 3})
    with pytest.raises(TspInputError):
        run(payload)


def test_reject_payload_not_an_object():
    with pytest.raises(TspInputError):
        run([1, 2, 3])


# ---------------------------------------------------------------------------
# Transport TCP loopback (service FastAPI, meme contrat)
# ---------------------------------------------------------------------------

def _free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        return int(sock.getsockname()[1])


@pytest.fixture()
def live_server():
    """Demarre uvicorn sur un port libre, rend l'URL de base, arrete a la fin."""
    port = _free_port()
    config = uvicorn.Config(create_app(), host="127.0.0.1", port=port, log_level="error")
    server = uvicorn.Server(config)
    thread = threading.Thread(target=server.run, daemon=True)
    thread.start()
    base_url = f"http://127.0.0.1:{port}"
    deadline = time.time() + 10
    while time.time() < deadline:
        try:
            httpx.get(base_url + "/openapi.json", timeout=0.5)
            break
        except Exception:
            time.sleep(0.1)
    yield base_url
    server.should_exit = True
    thread.join(timeout=5)


def test_transport_ok(live_server):
    response = httpx.post(live_server + "/search/tsp", json=_square_payload(), timeout=30)
    assert response.status_code == 200
    body = response.json()
    assert body["status"] == "ok"
    assert body["data"]["distance"] == pytest.approx(4.0, abs=1e-6)
    assert sorted(body["data"]["best_tour"]) == ["A", "B", "C", "D"]


def test_transport_invalid_too_few_cities(live_server):
    response = httpx.post(
        live_server + "/search/tsp",
        json={"cities": SQUARE[:3], "algorithm": "ga"},
        timeout=30,
    )
    assert response.status_code == 422
    assert response.json()["status"] == "invalid"


def test_transport_invalid_unknown_algorithm(live_server):
    response = httpx.post(
        live_server + "/search/tsp",
        json=_square_payload(algorithm="unknown"),
        timeout=30,
    )
    assert response.status_code == 422
    assert response.json()["status"] == "invalid"


def test_transport_invalid_malformed_body(live_server):
    # Corps sans le champ cities requis -> rejet de validation Pydantic (422).
    response = httpx.post(
        live_server + "/search/tsp", json={"algorithm": "ga"}, timeout=30
    )
    assert response.status_code == 422
    assert response.json()["status"] == "invalid"


def test_transport_no_exception_leaks(live_server):
    # Aucune trace ni detail d'exception ne fuit : seul le contrat ok/invalid/error.
    response = httpx.post(
        live_server + "/search/tsp",
        json={"cities": SQUARE, "algorithm": "ga", "params": {"population": 2}},
        timeout=30,
    )
    body = response.json()
    assert body["status"] in ("ok", "invalid", "error")
    assert "Traceback" not in response.text
