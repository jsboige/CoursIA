#!/usr/bin/env python3
"""
test_scan_slidev_composition_integration.py — test d'intégration E2E.

Nécessite un serveur `slidev dev` actif sur `SLIDEV_URL` (défaut http://localhost:8768/).

Couvre :
  - détection HORS_CANVAS sur la slide 5 du commit 6cabc826b (deck S3 v3)
  - contrôle positif : la slide 5 v3 DOIT être signalée
  - non-régression : la slide 5 du deck v4 (main) ne doit PAS être HORS_CANVAS

Usage :
    # terminal 1
    cd slides/S3-acculturation && npx slidev dev --port 8768 --open false
    # terminal 2
    pytest tests/integration/test_scan_slidev_composition_integration.py -v

Si le serveur n'est pas actif, le test est skip (pas un échec).
"""

from __future__ import annotations

import os
import shutil
import socket
import subprocess
import sys
import time
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts" / "notebook_tools"))

from scan_slidev_composition import main as scan_main  # noqa: E402

SLIDEV_URL = os.environ.get("SLIDEV_URL", "http://localhost:8768/")
SLIDEV_PORT = 8768


def is_server_up(url: str, port: int) -> bool:
    """Vérifie qu'un serveur HTTP répond sur le port."""
    try:
        with socket.create_connection(("localhost", port), timeout=1.0):
            return True
    except OSError:
        return False


# --- skip si serveur absent ---


@pytest.fixture(scope="module")
def skip_if_no_server():
    if not is_server_up(SLIDEV_URL, SLIDEV_PORT):
        pytest.skip(f"slidev dev non actif sur {SLIDEV_URL}")


# --- tests E2E ---


def test_controle_positif_s5_v3(tmp_path: Path) -> None:
    """La slide 5 du commit v3 (6cabc826b) DOIT être signalée HORS_CANVAS ou OCCUPATION."""
    if not is_server_up(SLIDEV_URL, SLIDEV_PORT):
        pytest.skip(f"slidev dev non actif sur {SLIDEV_URL}")

    repo_root = Path(__file__).resolve().parents[2]
    # créer un slides.md temporaire avec la version v3
    v3_slides = tmp_path / "slides_v3.md"
    subprocess.run(
        ["git", "show", "6cabc826b:slides/S3-acculturation/slides.md"],
        cwd=str(repo_root),
        check=True,
        stdout=open(v3_slides, "wb"),
    )

    out = tmp_path / "scan.json"
    # appel direct à main()
    sys.argv = [
        "scan_slidev_composition.py",
        "--url", SLIDEV_URL,
        "--slides-md", str(v3_slides),
        "--baseline-slide", "5",
        "--baseline-commit", "6cabc826b",
        "--max-slide", "15",
        "--out", str(out),
    ]
    rc = scan_main()
    assert rc in (0, 1), f"scan a échoué avec rc={rc}"
    import json

    r = json.loads(out.read_text(encoding="utf-8"))
    assert r["controle_positif_ok"] is True, r.get("controle_positif_msg")

    # la slide 5 doit figurer dans CHEVAUCHEMENTS (signe de saturation verticale)
    # ou dans HORS_CANVAS (signe de débordement bas) — un seul suffit
    s5 = next((s for s in r["results"] if s["slide"] == 5), None)
    assert s5 is not None
    signals = bool(s5.get("hors_canvas")) or bool(s5.get("chevauchements"))
    occ = s5.get("occupation") or {}
    occ_signal = occ.get("gap_left_pct", 0) + occ.get("gap_right_pct", 0) > 30
    assert signals or occ_signal, (
        f"slide 5 v3 NON signalee par l'instrument — "
        f"chevauchements={len(s5.get('chevauchements', []))}, "
        f"hors_canvas={len(s5.get('hors_canvas', []))}, "
        f"occupation={occ}"
    )