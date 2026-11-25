"""Tests for scripts/notebook_tools/check_end_block_answers.py (#27611).

Ce que ce fichier pinle
------------------------
1. **Le predicat** -- un bloc « Verifiez votre comprehension » sans reponse
   repliee est signale ; un carnet sans ce bloc ne l'est jamais (l'absence du
   bloc n'est pas le defaut vise) ; un bloc « Exercices » n'est jamais signale.
2. **Les deux formats de reponse en usage** -- la forme de reference (#27049,
   un ``<details>`` « Elements de reponse ») et la forme par question (un
   ``<details>`` par question, le corps portant « Reponse »).
3. **La fenetre** -- les reponses d'une section SUIVANTE (« Pour aller plus
   loin ») ne sont pas les reponses du bloc canonique : le carnet reste signale.
4. **Le panneau du mainteneur** -- les constats de la serie GameTheory sont
   tous inclus dans les 12 fichiers listes par #27611. Le COMPTE n'est pas
   pinle : il doit pouvoir descendre quand la remediation avance. Ce qui est
   pinle, c'est l'absence de faux positif.

Ce que ce fichier ne pinle pas
-------------------------------
Le nombre exact de constats du corpus : il evolue avec la remediation.
"""
from __future__ import annotations

import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_end_block_answers as organ  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[3]
NOTEBOOK_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"

PANEL_27611 = {
    "GameTheory/Dynamics/Dynamics-04c-Cooperation-Payorienne-Kripke-CSharp.ipynb",
    "GameTheory/Dynamics/Dynamics-04c-Cooperation-Payorienne-Kripke-Python.ipynb",
    "GameTheory/GameTheory-04h-Routing-PriceOfAnarchy-CSharp.ipynb",
    "GameTheory/GameTheory-04h-Routing-PriceOfAnarchy-Python.ipynb",
    "GameTheory/GameTheory-09b-Commitment-Stackelberg-CSharp.ipynb",
    "GameTheory/GameTheory-09b-Commitment-Stackelberg-Python.ipynb",
    "GameTheory/GameTheory-18-Capstone-Metajeux-CSharp.ipynb",
    "GameTheory/GameTheory-18-Capstone-Metajeux-Python.ipynb",
    "GameTheory/Metajeux/Metajeux-01-Open-Games-Lentilles-Python.ipynb",
    "GameTheory/Metajeux/Metajeux-01-Open-Games-Lentilles-CSharp.ipynb",
    "GameTheory/Metajeux/Metajeux-02-Casser-la-Composition-CSharp.ipynb",
    "GameTheory/Metajeux/Metajeux-02-Casser-la-Composition-Python.ipynb",
    "GameTheory/Metajeux/Metajeux-03-Abstraction-a-Dette-Python.ipynb",
    "GameTheory/Metajeux/Metajeux-04-Chemin-Minimal-Robinson-Goforth-Python.ipynb",
    "GameTheory/Metajeux/Metajeux-05-Temoins-Impossibilite-Python.ipynb",
    "GameTheory/Metajeux/Metajeux-05-Temoins-Impossibilite-CSharp.ipynb",
    "GameTheory/Metajeux/Metajeux-06-Chemin-Minimal-3x2-Ordinal-Python.ipynb",
}


def md(source: str) -> dict:
    """Cellule markdown synthetique."""
    return {"cell_type": "markdown", "source": source.splitlines(True)}


def flagged(cells: list) -> bool:
    """Vrai si le carnet synthetique est signale par l'organe."""
    found = organ.find_end_block(cells)
    if found is None:
        return False
    index, level, title_line = found
    return not organ.has_answers(organ.block_text(cells, index, level, title_line))


def test_reference_format_is_not_flagged():
    """La forme de reference (#27049) : un details « Elements de reponse »."""
    cells = [
        md("## Verifiez votre comprehension\n\n1. Une question ?\n"),
        md(
            "<details>\n<summary>Elements de reponse</summary>\n\n"
            "1. Une reponse.\n\n</details>\n"
        ),
    ]
    assert not flagged(cells)


def test_per_question_format_is_not_flagged():
    """La forme par question : le corps du details porte « Reponse »."""
    cells = [
        md("## Verifiez votre comprehension\n\n<details><summary>Q1 -- ?</summary>\n\n"
           "**Reponse** : la valeur mesuree.\n\n</details>\n"),
    ]
    assert not flagged(cells)


def test_block_without_answers_is_flagged():
    """Un bloc de questions sans reponse repliee est signale."""
    cells = [md("## Verifiez votre comprehension\n\n1. Une question ?\n2. Autre ?\n")]
    assert flagged(cells)


def test_exercises_block_is_never_flagged():
    """Les exercices restent sans reponse, par convention : jamais signales."""
    cells = [md("## Exercices\n\n1. A faire\n")]
    assert not flagged(cells)


def test_notebook_without_end_block_is_never_flagged():
    """L'absence du bloc n'est pas le defaut vise."""
    cells = [md("## A retenir\n\n- Un point.\n")]
    assert not flagged(cells)


def test_answers_of_next_section_do_not_count():
    """Les reponses d'une section suivante ne sont pas celles du bloc."""
    cells = [
        md("## Verifiez votre comprehension\n\n1. Une question ?\n"),
        md("## Pour aller plus loin\n\n<details>\n<summary>Elements de reponse</summary>\n\n"
           "1. ok\n\n</details>\n"),
    ]
    assert flagged(cells)


def test_answers_in_the_same_cell_after_the_title_are_found():
    """Le carnet qui tient tout en une cellule : le bloc est borne au titre."""
    cells = [
        md("## A retenir\n\n- Un point.\n\n"
           "## Verifiez votre comprehension\n\n1. Une question ?\n\n"
           "<details>\n<summary>Elements de reponse</summary>\n\n1. ok\n\n</details>\n\n"
           "## Pour aller plus loin\n\n- Une reference.\n"),
    ]
    assert not flagged(cells)


def test_title_is_matched_without_accents():
    """Le titre est reconnu sans accents et avec une ponctuation finale."""
    cells = [md("## Verifiez votre comprehension !\n\n1. Une question ?\n")]
    assert flagged(cells)


def test_gametheory_findings_stay_inside_the_panel():
    """Aucun faux positif sur GameTheory : les constats sont dans le panneau."""
    findings = organ.scan_corpus(str(NOTEBOOK_ROOT), "GameTheory")
    assert findings, "le corpus GameTheory doit porter des constats"
    for finding in findings:
        relative = os.path.relpath(finding["path"], str(NOTEBOOK_ROOT))
        relative = relative.replace(os.sep, "/")
        assert relative in PANEL_27611, relative


def test_self_test_passes():
    """Le controle interne de l'organe passe."""
    assert organ.self_test() == 0
