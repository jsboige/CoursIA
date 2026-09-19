# -*- coding: utf-8 -*-
"""Couche d'acces au corpus humour consolide (CORPUS_DUR) pour #14035.

Reproduit le geste du pilote ICT-35 : les cellules code [0..10] de
``GameTheory-24b-Humour-Banc-Dur.ipynb`` sont executees dans un namespace
isole, sans editer le notebook source, et ``CORPUS_DUR`` en est extrait.
La source de verite reste le notebook GT-24b, jamais copie.
"""
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

# Taxonomie de labels du banc consolide (GT-24b, verifiee sur le pilote ICT-35).
LABELS: tuple[str, ...] = (
    "humour_reussi",
    "rire_sans_recadrage",
    "recadrage_sans_rire",
    "offensif_compris_non_partage",
    "rien",
)

# Derniere cellule code de GT-24b a executer : CORPUS_DUR est construit dans
# la cellule 10 (mesure firsthand sur le notebook source).
_CORPUS_CELL_END = 10

# Champs du contrat d'instance (GT-24b cellule 10, verbe du banc).
_REQUIRED_FIELDS = ("id", "texte", "features", "label", "justification", "source")


def gt24b_path() -> Path:
    """Chemin canonique du banc humour consolide, resolu depuis ce module."""
    return (
        Path(__file__).resolve().parents[3]
        / "GameTheory"
        / "GameTheory-24b-Humour-Banc-Dur.ipynb"
    )


def load_corpus_dur(path: Path | None = None) -> list[dict[str, Any]]:
    """Charge ``CORPUS_DUR`` en executant les cellules de GT-24b.

    Reproduction deterministe (``random.seed(42)`` est pose par GT-24b
    lui-meme dans la cellule 10) ; le notebook source n'est jamais modifie.
    """
    nb_path = path or gt24b_path()
    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    ns: dict[str, Any] = {}
    for i, cell in enumerate(nb["cells"]):
        if cell["cell_type"] == "code" and i <= _CORPUS_CELL_END:
            exec("".join(cell["source"]), ns)  # noqa: S102 - reproduction, motif du pilote ICT-35 cell[3]
    corpus = ns["CORPUS_DUR"]
    validate_corpus(corpus)
    return corpus


def validate_corpus(corpus: list[dict[str, Any]], *, min_size: int = 100) -> None:
    """Verifie le contrat du corpus : taille, champs, taxonomie, unicite des ids."""
    assert isinstance(corpus, list) and len(corpus) >= min_size, (
        f"CORPUS_DUR attendu >= {min_size} instances, recu {len(corpus)}"
    )
    ids = [inst["id"] for inst in corpus]
    assert len(set(ids)) == len(ids), "ids dupliques dans CORPUS_DUR"
    for inst in corpus:
        for field in _REQUIRED_FIELDS:
            assert field in inst, f"champ {field} manquant sur {inst.get('id')}"
        assert inst["label"] in LABELS, (
            f"label hors taxonomie : {inst['label']!r} sur {inst['id']}"
        )


def label_distribution(corpus: list[dict[str, Any]]) -> Counter:
    """Effectifs par label, pour le controle de stratification des tranches."""
    return Counter(inst["label"] for inst in corpus)
