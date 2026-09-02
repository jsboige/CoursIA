#!/usr/bin/env python3
"""Tests for audit_engine_named_not_invoked.

Covers the 5 verdicts + sequence-aware grouping + edge cases:

* ``ENGINE_EXEC_PROVED`` : claim + wiring + real output (Lab16 BigQuery
  post-fix, OpenAI with real response).
* ``DISCLOSED_SEQUENCE_PROVED`` : deterministic notebook + successor with
  wiring/proof (Track2 Lab8/Lab16 etc).
* ``WIRING_ONLY`` : import present but no real output (key-gated code).
* ``SIMULATED_TERMINAL`` : outputs = simulation, no wiring (SW-12
  GraphRAG).
* ``NAMED_NOT_INVOKED`` : claim present but zero wiring (Track2 ADK
  baseline).

Plus :
* Multi-engine per notebook (engine X proved, engine Y NAMED_NOT_INVOKED).
* Sibling grouping (cache) successeurs successifs.
* Verdict filtres --check exit code.
* Exclusion artefacts _output.ipynb/_executed.ipynb.

Run::

    pytest scripts/notebook_tools/tests/test_audit_engine_named_not_invoked.py
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

SCRIPT_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPT_DIR))

from audit_engine_named_not_invoked import (  # noqa: E402
    ENGINE_REGISTRY,
    classify_notebook,
    main,
    scan_repo,
    _is_disclosed_deterministic,
    _iter_notebooks,
)


# --- helpers ---------------------------------------------------------------

def _nb(md_cells=(), code_cells=()):
    """Construit un notebook en memoire."""
    cells = []
    for src in md_cells:
        cells.append({"cell_type": "markdown", "source": src, "metadata": {}, "outputs": []})
    for src, outputs in code_cells:
        cells.append({
            "cell_type": "code",
            "source": src,
            "metadata": {},
            "execution_count": 1 if outputs else None,
            "outputs": outputs,
        })
    return {
        "cells": cells,
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _out_stream(text):
    return [{"output_type": "stream", "name": "stdout", "text": text + "\n"}]


# --- Engine registry structure ---------------------------------------------

def test_registry_has_three_engines():
    expected = {"google_adk", "openai_llm", "bigquery"}
    assert set(ENGINE_REGISTRY.keys()) == expected


def test_registry_entries_have_required_fields():
    for key, spec in ENGINE_REGISTRY.items():
        assert spec.key == key
        assert spec.imports, f"{key}: imports vide"
        assert spec.claims, f"{key}: claims vide"
        assert spec.simulation_markers, f"{key}: simulation_markers vide"
        assert spec.label


# --- ENGINE_EXEC_PROVED ----------------------------------------------------

def test_engine_exec_proved_bigquery():
    """Lab16 post-fix : import bigquery + claim BQML + output reel."""
    nb = _nb(
        md_cells=["# Lab 16 : BigQuery BQML reel\nCe lab utilise **BigQuery**."],
        code_cells=[
            ("from google.cloud import bigquery\nclient = bigquery.Client()", _out_stream("Dataset cree")),
        ],
    )
    p = Path("/tmp/_test_engine_exec_proved.ipynb")
    p.write_text(json.dumps(nb))
    try:
        results = classify_notebook(p, nb, ["bigquery"], {p.parent.resolve(): [p]})
        assert "bigquery" in results
        assert results["bigquery"]["verdict"] == "ENGINE_EXEC_PROVED"
        assert results["bigquery"]["wiring"]
    finally:
        p.unlink()


def test_engine_exec_proved_openai_real_response():
    """Import openai + output reponse API (pas 'Reponse simulee')."""
    nb = _nb(
        md_cells=["# GPT-4 integration\nAppel reel a `gpt-4`."],
        code_cells=[
            (
                "import openai\nr = openai.ChatCompletion.create(model='gpt-4', messages=[{'role':'user','content':'hi'}])\nprint(r.choices[0].message.content)",
                _out_stream("Bonjour, comment puis-je vous aider ?"),
            ),
        ],
    )
    p = Path("/tmp/_test_openai_proved.ipynb")
    p.write_text(json.dumps(nb))
    try:
        results = classify_notebook(p, nb, ["openai_llm"], {p.parent.resolve(): [p]})
        assert "openai_llm" in results
        assert results["openai_llm"]["verdict"] == "ENGINE_EXEC_PROVED"
    finally:
        p.unlink()


# --- DISCLOSED_SEQUENCE_PROVED ---------------------------------------------

def test_disclosed_sequence_proved_via_successor():
    """Notebook deterministe qui REFERENCE Google ADK dans sa prose
    + successeur dans la meme serie avec wiring+proof reels.
    Le verdict attendu : DISCLOSED_SEQUENCE_PROVED (le notebook lui-meme
    est deterministe, mais il annonce le successeur qui apporte le reel).
    """
    p1 = Path("/tmp/_test_seq1.ipynb")
    p2 = Path("/tmp/_test_seq2.ipynb")

    nb1 = _nb(
        md_cells=[
            "# Lab A : preparation deterministe\n"
            "Ce notebook est deterministe, sans LLM. Il prepare le terrain pour "
            "le **Google ADK** runtime developpe dans Lab B.",
        ],
        code_cells=[
            ("# Calcul deterministe\nresult = 2 + 2\nprint(result)", _out_stream("4")),
        ],
    )
    nb2 = _nb(
        md_cells=["# Lab B : Google ADK reel"],
        code_cells=[
            (
                "from google.adk import Agent\nagent = Agent()",
                _out_stream("Agent initialise"),
            ),
        ],
    )
    p1.write_text(json.dumps(nb1))
    p2.write_text(json.dumps(nb2))
    try:
        siblings = [p1, p2]
        cache = {p1.parent.resolve(): siblings}
        results = classify_notebook(p1, nb1, ["google_adk"], cache)
        assert "google_adk" in results, (
            "Le claim 'Google ADK' doit declencher la classification "
            "meme si le notebook est deterministe lui-meme"
        )
        assert results["google_adk"]["verdict"] == "DISCLOSED_SEQUENCE_PROVED"
    finally:
        p1.unlink()
        p2.unlink()


def test_disclosed_deterministic_marker_recognised():
    """Le marker deterministe/sans LLM doit etre detecte."""
    nb = _nb(md_cells=["# Test\nNotebook deterministe, sans appel LLM."])
    assert _is_disclosed_deterministic(nb) is True

    nb2 = _nb(md_cells=["# Test\nNotebook normal."])
    assert _is_disclosed_deterministic(nb2) is False


# --- WIRING_ONLY -----------------------------------------------------------

def test_wiring_only_no_proof():
    """Import present mais output gate par cle absente (vide)."""
    nb = _nb(
        md_cells=["# GPT-4 integration (key absente)"],
        code_cells=[
            (
                "import openai\n# cle api-key absente\nexec(openai.ChatCompletion.create)",
                [],  # pas d'output reel
            ),
        ],
    )
    p = Path("/tmp/_test_wiring_only.ipynb")
    p.write_text(json.dumps(nb))
    try:
        results = classify_notebook(p, nb, ["openai_llm"], {p.parent.resolve(): [p]})
        assert results["openai_llm"]["verdict"] == "WIRING_ONLY"
    finally:
        p.unlink()


# --- SIMULATED_TERMINAL ----------------------------------------------------

def test_simulated_terminal_graphrag():
    """SW-12 GraphRAG : outputs 'Reponse simulee', pas d'import openai."""
    nb = _nb(
        md_cells=[
            "# SW-12 GraphRAG\nExtraction reelle avec GPT/Claude.",
        ],
        code_cells=[
            (
                "# extraction\nprint('Reponse simulee : [entities...]')",
                _out_stream("Reponse simulee : [entities...]"),
            ),
        ],
    )
    p = Path("/tmp/_test_simulated.ipynb")
    p.write_text(json.dumps(nb))
    try:
        results = classify_notebook(p, nb, ["openai_llm"], {p.parent.resolve(): [p]})
        assert results["openai_llm"]["verdict"] == "SIMULATED_TERMINAL"
    finally:
        p.unlink()


# --- NAMED_NOT_INVOKED -----------------------------------------------------

def test_simulated_terminal_or_named_not_invoked_track2_adk_baseline():
    """Track2 baseline : claim Google ADK, zero import.

    Verdict attendu : SIMULATED_TERMINAL (plus precis que NAMED_NOT_INVOKED)
    car le code contient ``class MockAgent`` qui est un simulation_marker.
    Le scanner detecte 'mock agent' comme preuve de simulation locale --
    c'est le defaut firsthand documente dans #13927 (Track2 : 10 labs sans
    import `google.adk` mais avec des classes mock locales).
    """
    nb = _nb(
        md_cells=[
            "# Lab 5 : Google ADK agent\nIntegration du Google ADK runtime.",
        ],
        code_cells=[
            ("# mock agent\nclass MockAgent:\n    pass", _out_stream("mock created")),
        ],
    )
    p = Path("/tmp/_test_named_not_invoked.ipynb")
    p.write_text(json.dumps(nb))
    try:
        results = classify_notebook(p, nb, ["google_adk"], {p.parent.resolve(): [p]})
        # Le scanner detecte la simulation_marker `class MockAgent` :
        # verdict = SIMULATED_TERMINAL (le notebook simule sans le declarer
        # comme deterministe, et il n'a pas de successeur dans ce test).
        assert results["google_adk"]["verdict"] == "SIMULATED_TERMINAL"
        assert results["google_adk"]["simulation"], "le mock class doit etre flag"
    finally:
        p.unlink()


def test_named_not_invoked_no_mock_no_wiring():
    """Cas pur NAMED_NOT_INVOKED : claim present, ni mock ni import."""
    nb = _nb(
        md_cells=[
            "# Lab 7 : Google ADK demo\nCas pedagogique isole.",
        ],
        code_cells=[
            ("# Pas de mock, pas d'import\nprint('placeholder')", _out_stream("placeholder")),
        ],
    )
    p = Path("/tmp/_test_pure_named.ipynb")
    p.write_text(json.dumps(nb))
    try:
        results = classify_notebook(p, nb, ["google_adk"], {p.parent.resolve(): [p]})
        assert results["google_adk"]["verdict"] == "NAMED_NOT_INVOKED"
    finally:
        p.unlink()


# --- Multi-engine ----------------------------------------------------------

def test_multi_engine_per_notebook():
    """Un notebook peut etre ENGINE_EXEC_PROVED pour X et NAMED_NOT_INVOKED pour Y."""
    nb = _nb(
        md_cells=[
            "# Multi\nUtilise Google ADK **et** BigQuery.",
        ],
        code_cells=[
            ("from google.cloud import bigquery", _out_stream("Client() OK")),
            # pas d'import google.adk
        ],
    )
    p = Path("/tmp/_test_multi.ipynb")
    p.write_text(json.dumps(nb))
    try:
        results = classify_notebook(p, nb, ["google_adk", "bigquery"], {p.parent.resolve(): [p]})
        assert "google_adk" in results
        assert "bigquery" in results
        assert results["google_adk"]["verdict"] == "NAMED_NOT_INVOKED"
        assert results["bigquery"]["verdict"] == "ENGINE_EXEC_PROVED"
    finally:
        p.unlink()


def test_no_claim_no_trigger():
    """Pas de claim = pas de verdict (moteur non pertinent)."""
    nb = _nb(
        md_cells=["# Pure Python"],
        code_cells=[("print(2 + 2)", _out_stream("4"))],
    )
    p = Path("/tmp/_test_no_claim.ipynb")
    p.write_text(json.dumps(nb))
    try:
        results = classify_notebook(p, nb, None, {p.parent.resolve(): [p]})
        assert results == {}
    finally:
        p.unlink()


# --- iter_notebooks --------------------------------------------------------

def test_iter_excludes_output_artifacts(tmp_path):
    (tmp_path / "good.ipynb").write_text("{}")
    (tmp_path / "bad_output.ipynb").write_text("{}")
    (tmp_path / "bad_executed.ipynb").write_text("{}")
    seen = [p.name for p in _iter_notebooks(tmp_path)]
    assert "good.ipynb" in seen
    assert "bad_output.ipynb" not in seen
    assert "bad_executed.ipynb" not in seen


# --- CLI -------------------------------------------------------------------

def test_cli_check_exit_code_on_defect(tmp_path):
    """`--check` exit 1 si NAMED_NOT_INVOKED ou SIMULATED_TERMINAL trouve."""
    (tmp_path / "claim_only.ipynb").write_text(json.dumps(_nb(
        md_cells=["# Google ADK integration"],
        code_cells=[("# no import", _out_stream("foo"))],
    )))
    rc = main(["--scan-all", str(tmp_path), "--check"])
    assert rc == 1


def test_cli_json_output(tmp_path):
    (tmp_path / "clean.ipynb").write_text(json.dumps(_nb(
        md_cells=["# Clean"],
        code_cells=[("print(1)", _out_stream("1"))],
    )))
    rc = main(["--scan-all", str(tmp_path), "--json"])
    assert rc == 0


def test_cli_scan_single_notebook(tmp_path):
    p = tmp_path / "one.ipynb"
    p.write_text(json.dumps(_nb(
        md_cells=["# BigQuery claim"],
        code_cells=[("from google.cloud import bigquery", _out_stream("ok"))],
    )))
    rc = main(["--scan", str(p)])
    assert rc == 0


def test_cli_scan_repo_no_defects_exits_zero(tmp_path):
    (tmp_path / "good.ipynb").write_text(json.dumps(_nb(
        md_cells=["# Pure Python"],
        code_cells=[("print('hi')", _out_stream("hi"))],
    )))
    rc = main(["--scan-all", str(tmp_path), "--check"])
    assert rc == 0


# --- scan_repo end-to-end --------------------------------------------------

def test_scan_repo_finds_track2_adk_baseline(tmp_path):
    """Reproduction du cas Track2 baseline dans un repo temporaire."""
    (tmp_path / "Track2-Day5-Lab10.ipynb").write_text(json.dumps(_nb(
        md_cells=["# Lab 10\nGoogle ADK integration avec runtime"],
        code_cells=[("# no import google.adk", _out_stream("10"))],
    )))
    results = scan_repo(tmp_path)
    found = False
    for nb_path, nb_results in results.items():
        if "google_adk" in nb_results:
            assert nb_results["google_adk"]["verdict"] == "NAMED_NOT_INVOKED"
            found = True
    assert found, "Lab10 Track2 devrait declencher NAMED_NOT_INVOKED"