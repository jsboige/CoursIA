#!/usr/bin/env python3
"""Tests pour populate_cost_metadata.py — Issue #8056, profile quantbook."""

import json
import sys
from pathlib import Path

# Importer le module voisin (scripts/audit est sur sys.path via conftest ou ajout manuel).
HERE = Path(__file__).resolve().parent
AUDIT_DIR = HERE.parent
sys.path.insert(0, str(AUDIT_DIR))

import populate_cost_metadata as pcm  # noqa: E402


def _make_quantbook(n_code_cells: int = 10) -> dict:
    """Un notebook QuantBook minimal avec n cellules code."""
    nb = {
        "cells": [
            {"cell_type": "markdown", "metadata": {}, "source": ["# Demo\n"]},
            {"cell_type": "code", "execution_count": None, "metadata": {},
             "outputs": [], "source": ["qb = QuantBook()\n"]},
        ],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    for _ in range(n_code_cells - 1):
        nb["cells"].append({"cell_type": "code", "execution_count": None,
                            "metadata": {}, "outputs": [], "source": ["x = 1\n"]})
    return nb


def _make_non_qc() -> dict:
    return {"cells": [{"cell_type": "code", "execution_count": None,
                       "metadata": {}, "outputs": [], "source": ["print('hi')\n"]}],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


# === Heuristic QCC ===

def test_qcc_heuristic_floor():
    """Peu de cellules → plancher 400 (cf #8056, cost-matrix.md)."""
    assert pcm.qcc_tokens_estimate(0) == 400
    assert pcm.qcc_tokens_estimate(1) == 400
    assert pcm.qcc_tokens_estimate(5) == 400  # 5×70=350 < 400


def test_qcc_heuristic_linear():
    """Au-delà du plancher, ~70 QCC/cellule."""
    assert pcm.qcc_tokens_estimate(10) == 700
    assert pcm.qcc_tokens_estimate(14) == 980   # acceptance #8056 : « 14 cellules ≈ 800-1200 »
    assert pcm.qcc_tokens_estimate(28) == 1960  # QC-Py-04 observé


# === Detection ===

def test_uses_quantbook_detect():
    assert pcm._uses_quantbook(_make_quantbook())
    assert not pcm._uses_quantbook(_make_non_qc())


def test_count_code_cells_ignores_empty():
    nb = _make_quantbook(3)
    nb["cells"].append({"cell_type": "code", "execution_count": None,
                        "metadata": {}, "outputs": [], "source": ["   \n"]})  # whitespace only
    assert pcm._count_code_cells(nb) == 3  # cellule vide non comptée


# === build_quantbook_cost : champs obligatoires + valeurs canoniques ===

def test_build_cost_has_all_mandatory_fields():
    cost = pcm.build_quantbook_cost(_make_quantbook(10), by="m:w", today="2026-07-26")
    mandatory = {"api_usd_est", "api_provider", "cpu_min", "gpu_required",
                 "network", "external_account", "reproducibility",
                 "last_validated", "validator"}
    assert mandatory <= set(cost), f"champs obligatoires manquants: {mandatory - set(cost)}"


def test_build_cost_clears_litmus5_and_7():
    """validator=qc_cloud (Litmus 5) + qcc_tokens_est nonzero (Litmus 7)."""
    cost = pcm.build_quantbook_cost(_make_quantbook(10), by="m:w", today="2026-07-26")
    assert cost["validator"] == "qc_cloud"
    assert cost["qcc_tokens_est"] > 0


def test_build_cost_honest_nulls_for_notebook_specific():
    """reduced_pedagogical + free_alternative = null (jugement humain, jamais fabriqué)."""
    cost = pcm.build_quantbook_cost(_make_quantbook(10), by="m:w", today="2026-07-26")
    assert cost["reduced_pedagogical"] is None
    assert cost["free_alternative"] is None


def test_build_cost_matches_migrated_consensus():
    """Consensus des 13 quantbooks migrés (#8585) : api_provider=none, network=true,
    external_account=quantconnect-organization."""
    cost = pcm.build_quantbook_cost(_make_quantbook(10), by="m:w", today="2026-07-26")
    assert cost["api_provider"] == "none"
    assert cost["network"] is True
    assert cost["external_account"] == "quantconnect-organization"


# === Idempotence (HARD) ===

def test_populate_idempotent_never_overwrites(tmp_path):
    """Un notebook déjà peuplé est skippé — JAMAIS écraser un bloc existant."""
    nb = _make_quantbook(10)
    nb["metadata"]["cost"] = {"api_usd_est": 0.42, "validator": "manual"}  # bloc existant
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")

    status = pcm.populate_notebook(p, by="m:w", today="2026-07-26", apply=True)
    assert status == "skipped-has-cost"
    # Le bloc existant est intact
    after = json.loads(p.read_text(encoding="utf-8"))
    assert after["metadata"]["cost"]["api_usd_est"] == 0.42
    assert after["metadata"]["cost"]["validator"] == "manual"


def test_populate_skips_non_qc(tmp_path):
    nb = _make_non_qc()
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    assert pcm.populate_notebook(p, by="m:w", today="2026-07-26", apply=True) == "skipped-no-quantbook"


def test_populate_applies_and_writes(tmp_path):
    nb = _make_quantbook(10)
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    status = pcm.populate_notebook(p, by="m:w", today="2026-07-26", apply=True)
    assert status == "populated"
    after = json.loads(p.read_text(encoding="utf-8"))
    assert after["metadata"]["cost"]["qcc_tokens_est"] == 700
    assert after["metadata"]["cost"]["validator"] == "qc_cloud"


def test_populate_dry_run_writes_nothing(tmp_path):
    nb = _make_quantbook(10)
    p = tmp_path / "nb.ipynb"
    original = json.dumps(nb, indent=1)
    p.write_text(original, encoding="utf-8")
    status = pcm.populate_notebook(p, by="m:w", today="2026-07-26", apply=False)
    assert status == "populated"  # rapporte qu'il peuplerait
    assert p.read_text(encoding="utf-8") == original  # mais n'écrit rien


def test_populate_preserves_notebook_structure(tmp_path):
    """La transformation ne touche QUE metadata.cost — cells/kernel/nbformat intacts."""
    nb = _make_quantbook(10)
    nb["metadata"]["kernelspec"] = {"name": "python3", "display_name": "Python 3"}
    nb["metadata"]["custom_field"] = "preserve-me"
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    pcm.populate_notebook(p, by="m:w", today="2026-07-26", apply=True)
    after = json.loads(p.read_text(encoding="utf-8"))
    assert after["metadata"]["kernelspec"]["display_name"] == "Python 3"
    assert after["metadata"]["custom_field"] == "preserve-me"
    assert after["nbformat"] == 4
    assert len(after["cells"]) == len(nb["cells"])  # aucune cellule touchée
