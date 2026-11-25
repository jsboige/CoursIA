"""Tests du fixer d'ids déterministe et byte-preserving (#25136)."""

import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import fix_cell_ids as fixer  # noqa: E402
from check_cell_id_invalid_ratchet import invalid_count  # noqa: E402


def make_nb():
    return {
        "nbformat": 4,
        "nbformat_minor": 5,
        "metadata": {"kernelspec": {"name": "python3"}},
        "cells": [
            {"cell_type": "code", "id": "ok1", "metadata": {}, "source": ["a = 1\n"], "outputs": [], "execution_count": 1},
            {"cell_type": "markdown", "id": "", "metadata": {}, "source": ["# Titre"]},
            {"cell_type": "markdown", "metadata": {}, "source": ["pas d id"]},
            {"cell_type": "code", "id": "bad.id!", "metadata": {}, "source": ["b = 2\n"], "outputs": [], "execution_count": 2},
            {"cell_type": "markdown", "id": "ok1", "metadata": {}, "source": ["doublon"]},
        ],
    }


def test_repair_changes_only_ids_and_preserves_valid_id(monkeypatch):
    monkeypatch.setattr(fixer, "_external_references", lambda *_: [])
    original = make_nb()
    raw = json.dumps(original, indent=1) + "\n"
    assert invalid_count(raw) == 4

    fixed = fixer.repair_text(raw, Path("nb.ipynb"))
    assert fixer.repair_text(fixed, Path("nb.ipynb")) == fixed
    assert invalid_count(fixed) == 0
    parsed = json.loads(fixed)
    strip_ids = lambda nb: [  # noqa: E731
        {key: value for key, value in cell.items() if key != "id"}
        for cell in nb["cells"]
    ]
    assert strip_ids(parsed) == strip_ids(original)
    assert parsed["metadata"] == original["metadata"]

    ids = [cell["id"] for cell in parsed["cells"]]
    assert ids[0] == "ok1"
    assert ids[3] != "bad.id!" and ids[4] != "ok1"
    assert all(re.fullmatch(r"[A-Za-z0-9_-]{1,64}", value) for value in ids)
    assert len(set(ids)) == len(ids)

    # Le formatage JSON hors des lignes d'id reste byte-identique, y compris
    # les sorties, execution_count, metadata et source.
    before_non_id = [line for line in raw.splitlines() if '"id":' not in line]
    after_non_id = [line for line in fixed.splitlines() if '"id":' not in line]
    assert after_non_id == before_non_id


def test_repair_text_is_read_only_and_does_not_write_its_input(tmp_path, monkeypatch):
    monkeypatch.setattr(fixer, "_external_references", lambda *_: [])
    path = tmp_path / "nb.ipynb"
    original = json.dumps(make_nb(), indent=1) + "\n"
    path.write_text(original, encoding="utf-8")

    repaired = fixer.repair_text(original, path)

    assert repaired != original
    assert path.read_text(encoding="utf-8") == original


def test_existing_invalid_id_with_external_reference_is_refused(monkeypatch):
    monkeypatch.setattr(
        fixer, "_external_references", lambda *_: ["translations.csv:1:bad.id!"]
    )
    raw = json.dumps(make_nb(), indent=1) + "\n"
    try:
        fixer.repair_text(raw, Path("nb.ipynb"))
    except ValueError as exc:
        assert "référencé hors du carnet" in str(exc)
    else:
        raise AssertionError("une référence externe doit empêcher le renommage")
