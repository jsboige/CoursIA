"""Tests for check_end_block_answers.py — blocs « Vérifiez votre compréhension »
sans réponse.

Le noyau testé est la détection pure (``verif_blocks`` / ``block_has_answer`` /
``no_answer_blocks``), sans git ni kernel. Le point central du fichier est le
contrôle du faux positif fondateur : un carnet qui porte une section
« Exercices » (volontairement sans réponse) ET un bloc « Vérifiez votre
compréhension » AVEC réponses repliées doit rester SAIN — c'est le cas de
ChoixSocial-08, le format de référence de la campagne #19297, qu'un détecteur
large signalait à tort.
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_end_block_answers as organ


def _nb(cells):
    return {"cells": [{"cell_type": t, "source": s} for t, s in cells]}


# ---------------------------------------------------------------------------
# Détection pure
# ---------------------------------------------------------------------------

def test_verif_block_without_answer_detected():
    nb = _nb([("markdown", "## Vérifiez votre compréhension\n1. Pourquoi ?\n"
                            "2. Comment ?\n")])
    assert organ.count_no_answer(nb) == 1


def test_verif_block_with_details_answer_clean():
    nb = _nb([("markdown", "## Vérifiez votre compréhension\n1. Pourquoi ?\n"
                           "<details>\n<summary>Éléments de réponse</summary>\n"
                           "1. Parce que.\n</details>\n")])
    assert organ.count_no_answer(nb) == 0


def test_verif_block_with_inline_answer_clean():
    nb = _nb([("markdown", "## Vérifiez votre compréhension\n1. Pourquoi ?\n"
                           "**Réponses :**\n1. Parce que.\n")])
    assert organ.count_no_answer(nb) == 0


def test_exercices_block_not_counted():
    # Une section « Exercices » seule n'est pas un bloc « vérifiez » : hors cible.
    nb = _nb([("markdown", "## Exercices\n1. Résoudre tel problème.\n")])
    assert organ.verif_blocks(nb) == []
    assert organ.count_no_answer(nb) == 0


def test_founding_false_positive_exercices_plus_answered_verif():
    # ChoixSocial-08 : « Exercices » (sans réponse) + « vérifiez » (avec
    # réponse repliée) -> SAIN, 0 bloc sans réponse.
    nb = _nb([
        ("markdown", "## Exercices\n1. Un exercice (sans réponse).\n"),
        ("markdown", "## Vérifiez votre compréhension\n1. Pourquoi ?\n"
                    "<details>\n<summary>Éléments de réponse</summary>\n"
                    "1. Parce que.\n</details>\n"),
    ])
    assert organ.count_no_answer(nb) == 0


def test_multiple_verif_blocks_one_without_answer():
    nb = _nb([
        ("markdown", "## Vérifiez votre compréhension\n1. Q ?\n"
                    "<details>\n<summary>Réponse</summary>\n1. R.\n</details>\n"),
        ("markdown", "## Vérifiez votre compréhension\n2. Q sans réponse.\n"),
    ])
    assert organ.count_no_answer(nb) == 1


def test_details_without_answer_summary_not_enough():
    # Un <details> dont le <summary> ne porte pas un mot de réponse ne compte
    # pas comme réponse (ex. un <details> de mise en forme).
    nb = _nb([("markdown", "## Vérifiez votre compréhension\n1. Q ?\n"
                           "<details>\n<summary>Notes</summary>\n"
                           "du texte\n</details>\n")])
    assert organ.count_no_answer(nb) == 1


# ---------------------------------------------------------------------------
# Mode triage (dossier temp)
# ---------------------------------------------------------------------------

def _write_nb(path, cells):
    path.write_text(json.dumps(_nb(cells), ensure_ascii=False), encoding="utf-8")


def test_triage_lists_only_no_answer(tmp_path, monkeypatch):
    series_dir = tmp_path / "MyIA.AI.Notebooks" / "TestSerie"
    series_dir.mkdir(parents=True)
    _write_nb(series_dir / "sain.ipynb",
              [("markdown", "## Vérifiez votre compréhension\n1. Q ?\n"
                           "<details>\n<summary>Réponse</summary>\n1. R.\n"
                           "</details>\n")])
    _write_nb(series_dir / "sans_reponse.ipynb",
              [("markdown", "## Vérifiez votre compréhension\n1. Q ?\n")])
    _write_nb(series_dir / "exercices_seul.ipynb",
              [("markdown", "## Exercices\n1. Un exercice.\n")])
    monkeypatch.setattr(organ, "SERIES_ROOT", str(tmp_path / "MyIA.AI.Notebooks"))

    verdict = organ.triage("TestSerie")
    assert verdict["rc"] == 1
    assert verdict["with_answer"] == 1
    assert verdict["no_answer"] == 1
    # Le chemin est relatif a SERIES_ROOT (repo-relative en CI) ; le tmp_path
    # du test est absolu, on matche donc le suffixe series/carnet.
    assert [f["path"] for f in verdict["flagged"]] == ["TestSerie/sans_reponse.ipynb"] \
        or all(f["path"].replace("\\", "/").endswith("TestSerie/sans_reponse.ipynb")
               for f in verdict["flagged"])


def test_triage_all_clean(tmp_path, monkeypatch):
    series_dir = tmp_path / "MyIA.AI.Notebooks" / "Saine"
    series_dir.mkdir(parents=True)
    _write_nb(series_dir / "ok.ipynb",
              [("markdown", "## Vérifiez votre compréhension\n1. Q ?\n"
                           "<details>\n<summary>Réponse</summary>\n1. R.\n"
                           "</details>\n")])
    monkeypatch.setattr(organ, "SERIES_ROOT", str(tmp_path / "MyIA.AI.Notebooks"))
    assert organ.triage("Saine")["rc"] == 0


def test_triage_unknown_series(tmp_path, monkeypatch):
    monkeypatch.setattr(organ, "SERIES_ROOT", str(tmp_path / "MyIA.AI.Notebooks"))
    assert organ.triage("NExistePas")["error"] == "series_not_found"


def test_triage_path_traversal_refused(tmp_path, monkeypatch):
    monkeypatch.setattr(organ, "SERIES_ROOT", str(tmp_path / "MyIA.AI.Notebooks"))
    assert organ.triage("../etc")["error"] == "invalid_series_name"
    assert organ.triage("C:/x")["error"] == "invalid_series_name"


# ---------------------------------------------------------------------------
# Self-test
# ---------------------------------------------------------------------------

def test_self_test_passes(capsys):
    assert organ.self_test() == 0
    assert "SELF-TEST OK" in capsys.readouterr().out
