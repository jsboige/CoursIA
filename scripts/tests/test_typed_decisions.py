#!/usr/bin/env python3
"""L'organe typé `typed_decisions.py` (Pli 2 de #18204) sert le même banc à tous les carnets.

Extraction byte-fidèle des cellules 4 et 7 de `03b_Typed_Decisions_System1.ipynb`.
Ces tests gardent l'intégrité du banc (4 classes, 12 tickets chacune, découpage
déterministe 6/3/3) et du contrat (`Question.decide` → distribution sur l'espace
fermé). Aucun accès réseau, aucun modèle.
"""

import importlib.util
from pathlib import Path

import pytest

_MOD_PATH = Path(__file__).resolve().parent.parent / "genai-stack" / "typed_decisions.py"
_spec = importlib.util.spec_from_file_location("typed_decisions", _MOD_PATH)
organ = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(organ)


def test_bench_counts():
    b = organ.load_bench()
    assert len(b["X_train"]) == 24
    assert len(b["X_cal"]) == 12
    assert len(b["X_test"]) == 12


def test_tickets_12_per_class():
    assert all(len(v) == 12 for v in organ.TICKETS.values())
    assert set(organ.TICKETS) == set(organ.CLASSES)
    assert len(organ.CLASSES) == 4


def test_test_set_covers_all_classes():
    b = organ.load_bench()
    assert set(b["y_test"]) == set(organ.CLASSES)


def test_question_decide_is_a_distribution():
    q = organ.Question(organ.CHOICE, "etat", organ.CLASSES)
    d = q.decide([0.05, 0.10, 0.80, 0.05])
    assert d.shape == (len(organ.CLASSES),)
    assert pytest.approx(float(d.sum()), abs=1e-9) == 1.0
    assert int(d.argmax()) == 2  # option de score maximal : « livraison »


def test_question_rejects_unknown_kind():
    with pytest.raises(AssertionError):
        organ.Question("bogus", "etat", organ.CLASSES)
