#!/usr/bin/env python3
"""Tests pour les helpers Python externalises de twin-parity-cron.yml.

Le cron workflow (.github/workflows/twin-parity-cron.yml) utilise deux
helpers Python externalises pour eviter le YAML/Bash quoting croise :
- _cron_extract_drift.py : liste des paires touchees par le drift
  (sortie affichee par `::error title=...::...` du workflow)
- _cron_render_summary.py : rapport markdown pour $GITHUB_STEP_SUMMARY

Ces tests pincent les cas Exercices du cron (c.984) :
- helpers executables sans erreur
- sortie conforme aux semantiques documentees (pas de drift -> <none>)
- robustesse aux entrees degradees (JSON mal forme, args manquants)
"""
from __future__ import annotations

import json
import os
import subprocess
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


# --- helpers -----------------------------------------------------------------

def _write_tmp_json(d: dict) -> str:
    """Ecrit un JSON dans un fichier tmp et retourne son chemin."""
    import tempfile
    fd, path = tempfile.mkstemp(suffix=".json")
    os.close(fd)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(d, f)
    return path


def _run_helper(name: str, args: list[str]) -> subprocess.CompletedProcess:
    """Execute scripts/notebook_tools/_cron_<name>.py avec les args."""
    script = os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        f"_cron_{name}.py",
    )
    return subprocess.run(
        ["python", script, *args],
        capture_output=True,
        text=True,
    )


# --- _cron_extract_drift ----------------------------------------------------

def test_extract_lists_touched_pairs():
    """Paires drift -> une ligne par paire au format `name (family, parity)`."""
    d = {
        "pairs": [
            {"name": "OK-1", "family": "Search", "parity_level": "full", "status": "OK"},
            {"name": "DRIFT-A", "family": "Sudoku", "parity_level": "full", "status": "DRIFT_BLOB"},
            {"name": "DRIFT-B", "family": "ML", "parity_level": "partial", "status": "DRIFT_CONTENT"},
        ]
    }
    path = _write_tmp_json(d)
    try:
        r = _run_helper("extract_drift", [path])
        assert r.returncode == 0, r.stderr
        lines = r.stdout.strip().split("\n")
        assert "DRIFT-A (Sudoku, full)" in lines
        assert "DRIFT-B (ML, partial)" in lines
        assert "OK-1" not in r.stdout
    finally:
        os.unlink(path)


def test_extract_no_drift_emits_none():
    """Aucun drift -> sortie `<none>` (le `::error` du workflow reste lisible)."""
    d = {
        "pairs": [
            {"name": "OK-1", "family": "Search", "parity_level": "full", "status": "OK"},
            {"name": "OK-2", "family": "Probas", "parity_level": "full", "status": "OK"},
        ]
    }
    path = _write_tmp_json(d)
    try:
        r = _run_helper("extract_drift", [path])
        assert r.returncode == 0, r.stderr
        assert r.stdout.strip() == "<none>", f"got {r.stdout!r}"
    finally:
        os.unlink(path)


def test_extract_missing_pairs_key_handled():
    """JSON sans cle `pairs` -> sortie `<none>`, pas de crash."""
    d = {"total": 0, "ci_strict": {}}
    path = _write_tmp_json(d)
    try:
        r = _run_helper("extract_drift", [path])
        assert r.returncode == 0
        assert r.stdout.strip() == "<none>"
    finally:
        os.unlink(path)


def test_extract_malformed_json_exits_nonzero():
    """JSON mal forme -> exit 1 (≠ drift finding, le cron distingue via
    la parsabilite du JSON de check_twin_parity.py qui aura deja rate)."""
    import tempfile
    fd, path = tempfile.mkstemp(suffix=".json")
    os.close(fd)
    with open(path, "w", encoding="utf-8") as f:
        f.write("not valid json {{")
    try:
        r = _run_helper("extract_drift", [path])
        assert r.returncode != 0, "malformed JSON doit echouer"
    finally:
        os.unlink(path)


def test_extract_missing_arg_exits_two():
    """Aucun argument -> exit 2 (usage error, distinct de l'absence de drift)."""
    r = _run_helper("extract_drift", [])
    assert r.returncode == 2, f"missing arg devrait exit 2, got {r.returncode}"


def test_extract_missing_file_exits_nonzero():
    """Fichier inexistant -> exit 1."""
    r = _run_helper("extract_drift", ["/nonexistent/twin_parity_cron.json"])
    assert r.returncode != 0


# --- _cron_render_summary ---------------------------------------------------

def test_render_basic():
    """Sortie contient header + table des compteurs + liste des paires touchees."""
    d = {
        "total": 156,
        "ci_strict": {
            "n_ok_legacy": 149, "n_ok_content": 4, "n_drift_blob": 3,
            "n_drift_content": 0,
        },
        "pairs": [
            {"name": "Sudoku-8", "family": "Sudoku", "parity_level": "full", "status": "DRIFT_BLOB"},
        ],
    }
    path = _write_tmp_json(d)
    try:
        r = _run_helper("render_summary", [path])
        assert r.returncode == 0, r.stderr
        assert "Twin parity CI-strict -- 156 paires" in r.stdout
        assert "n_ok_legacy" in r.stdout
        assert "Sudoku-8" in r.stdout
        assert "DRIFT_BLOB" in r.stdout
    finally:
        os.unlink(path)


def test_render_no_touched_pairs():
    """Aucune paire touchee -> pas de section `### N paire(s) touchee(s)`."""
    d = {
        "total": 100,
        "ci_strict": {"n_ok_legacy": 100},
        "pairs": [
            {"name": "All-OK", "family": "Search", "parity_level": "full", "status": "OK"}
        ],
    }
    path = _write_tmp_json(d)
    try:
        r = _run_helper("render_summary", [path])
        assert r.returncode == 0
        assert "paire(s) touchee(s)" not in r.stdout, r.stdout
    finally:
        os.unlink(path)


def test_render_touched_pair_includes_details():
    """Les `details` d'une paire touchee apparaissent en sous-liste."""
    d = {
        "total": 1,
        "ci_strict": {"n_drift_blob": 1},
        "pairs": [
            {
                "name": "Sudoku-8", "family": "Sudoku", "parity_level": "full",
                "status": "DRIFT_BLOB",
                "details": ["python_blob != recorded_sha: abc... vs def..."]
            }
        ],
    }
    path = _write_tmp_json(d)
    try:
        r = _run_helper("render_summary", [path])
        assert r.returncode == 0
        assert "python_blob != recorded_sha" in r.stdout, r.stdout
    finally:
        os.unlink(path)


def test_render_malformed_json_exits_nonzero():
    """JSON mal forme -> exit 1."""
    import tempfile
    fd, path = tempfile.mkstemp(suffix=".json")
    os.close(fd)
    with open(path, "w", encoding="utf-8") as f:
        f.write("not valid json {{")
    try:
        r = _run_helper("render_summary", [path])
        assert r.returncode != 0
    finally:
        os.unlink(path)


def test_render_missing_arg_exits_two():
    r = _run_helper("render_summary", [])
    assert r.returncode == 2