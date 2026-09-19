# -*- coding: utf-8 -*-
"""Tests de la couche corpus humor_pairs (#14035, tranche 1)."""
from __future__ import annotations

import os

import pytest

from ict.humor_pairs import (
    LABELS,
    gt24b_path,
    label_distribution,
    load_corpus_dur,
    validate_corpus,
)

# Les cellules endpoint de GT-24b exigent la cle OpenRouter (presente dans
# .secrets/master.env sur les machines du cluster, absente en CI sans secrets).
# Le corpus lui-meme est deterministe et n'appelle jamais l'API.
_NEEDS_KEY = pytest.mark.skipif(
    not os.environ.get("OPENROUTER_API_KEY"),
    reason="cle OPENROUTER_API_KEY requise par les cellules endpoint de GT-24b",
)


@pytest.fixture(scope="module")
def corpus() -> list[dict]:
    return load_corpus_dur()


# Les deux tests de rejet ne chargent pas le corpus : pas de cle requise.


def test_gt24b_path_exists() -> None:
    assert gt24b_path().exists(), f"GT-24b manquant : {gt24b_path()}"


@_NEEDS_KEY
def test_load_corpus_dur_contract(corpus: list[dict]) -> None:
    # Le banc consolide declare >= 100 instances annotees manuellement.
    assert len(corpus) >= 100
    validate_corpus(corpus)  # leve si champs/taxonomie/unicite violent le contrat


@_NEEDS_KEY
def test_label_distribution_sums_to_corpus(corpus: list[dict]) -> None:
    dist = label_distribution(corpus)
    assert sum(dist.values()) == len(corpus)
    assert set(dist) <= set(LABELS)


def test_validate_corpus_rejects_bad_label() -> None:
    bad = [{"id": "x", "texte": "t", "features": {}, "label": "drole", "justification": "", "source": "s"}]
    with pytest.raises(AssertionError, match="hors taxonomie"):
        validate_corpus(bad, min_size=1)


def test_validate_corpus_rejects_duplicate_ids() -> None:
    inst = {"id": "x", "texte": "t", "features": {}, "label": "rien", "justification": "", "source": "s"}
    with pytest.raises(AssertionError, match="dupliques"):
        validate_corpus([inst, dict(inst)], min_size=1)
