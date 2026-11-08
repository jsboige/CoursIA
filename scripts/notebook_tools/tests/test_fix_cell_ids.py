"""Tests du fixer deterministe des ids de cellules (#25136).

Le controle central : le fixer ne change QUE les identifiants — ni source,
ni sorties, ni execution_count, ni aucune autre cle.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fix_cell_ids import classify, process_file  # noqa: E402


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


def test_classify_compte_les_quatre_classes():
    nb = make_nb()
    classes = [c for _, c, _ in classify(nb["cells"])]
    assert classes == ["empty", "absent", "pattern", "duplicate"]
    assert classify([{"cell_type": "code", "id": "valide", "metadata": {}, "source": [], "outputs": []}]) == []


def test_apply_ne_change_que_les_ids(tmp_path):
    p = tmp_path / "nb.ipynb"
    original = make_nb()
    p.write_text(json.dumps(original, indent=1) + "\n", encoding="utf-8")

    report = process_file(p, apply=True)
    assert report["before"] == 4 and report["after"] == 0

    fixed = json.loads(p.read_text(encoding="utf-8"))
    strip = lambda nb: [  # noqa: E731
        {k: v for k, v in c.items() if k != "id"} for c in nb["cells"]
    ]
    assert strip(fixed) == strip(original)  # rien d'autre que les ids n a change
    assert fixed["metadata"] == original["metadata"]

    ids = [c["id"] for c in fixed["cells"]]
    assert ids[0] == "ok1"  # id valide jamais modifie
    assert ids[3] != "bad.id!" and ids[4] != "ok1"  # hors-motif et doublon re-ids
    import re

    assert all(re.match(r"^[a-zA-Z0-9_-]{1,64}$", i) for i in ids)
    assert len(set(ids)) == len(ids)  # unicite


def test_check_sans_apply_necrit_rien(tmp_path):
    p = tmp_path / "nb.ipynb"
    before = json.dumps(make_nb(), indent=1) + "\n"
    p.write_text(before, encoding="utf-8")
    report = process_file(p, apply=False)
    assert report["before"] == 4 and report["after"] is None
    assert p.read_text(encoding="utf-8") == before
