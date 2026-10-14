"""Identite d'un finding ANCHOR_OOR : le jeton, pas la phrase qui l'entoure.

Le message ANCHOR_OOR embarque deux fragments d'ETAT descriptif -- le nombre de
cellules de code de la tete, et ``abs_state`` (le type de la cellule a l'index
absolu N). Les deux bougent quand un PR insere ou retire des cellules, sans que
le defaut change. La difference base-vs-tete clee sur le message brut annoncait
donc comme NEUF un defaut pre-existant (mesure #17064, 2026-09-26 : base et tete
portaient les memes 5 ANCHOR_OOR, valeurs {12,14,16,18,22} ; seul ``abs_state``
diffrait, `markdown` -> `out of notebook`).

Ces tests pinnent l'invariant : meme ancre non resolue des deux cotes -> pas de
regression, quel que soit le deplacement ; ancre reellement neuve -> detectee.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from enrich_quality_ci import regressions  # noqa: E402

# Lignes markdown substantielles partagees par la base et la tete. Elles
# survivent verbatim, ce qui garde MD_REWRITE (une autre categorie, base-vs-tete,
# qui se declenche des que < 25 % des lignes de la base survivent) hors du champ
# de ces tests : on mesure l'identite des ancres, pas la reecriture.
FILLER = [
    "Premiere ligne substantielle du corps, conservee telle quelle.",
    "Deuxieme ligne substantielle du corps, conservee telle quelle.",
    "Troisieme ligne substantielle du corps, conservee telle quelle.",
]


def _md(text: str) -> dict:
    return {"cell_type": "markdown", "metadata": {}, "source": [text]}


def _code(text: str = "x = 1") -> dict:
    return {"cell_type": "code", "metadata": {}, "source": [text],
            "outputs": [], "execution_count": 1}


def _write(path: Path, cells: list[dict]) -> str:
    path.write_text(json.dumps({"cells": cells, "metadata": {},
                                "nbformat": 4, "nbformat_minor": 5}),
                    encoding="utf-8")
    return str(path)


def _anchors(findings: list[tuple[str, str]]) -> list[tuple[str, str]]:
    return [f for f in findings if f[0] == "ANCHOR_OOR"]


@pytest.fixture
def anchor_case(tmp_path):
    """base et tete portent la MEME ancre non resolue `code[9]`, mais le nombre
    de cellules de code differe (4 -> 3) : le message brut change, le defaut non."""
    base = _write(tmp_path / "base.ipynb",
                  [_md("Intro : voir code[9] pour le detail.")] + [_code()] * 4
                  + [_md(t) for t in FILLER])
    head = _write(tmp_path / "head.ipynb",
                  [_md("Intro : voir code[9] pour le detail.")] + [_code()] * 3
                  + [_md(t) for t in FILLER])
    return base, head


def test_same_dangling_anchor_is_not_a_regression_when_code_count_shifts(anchor_case):
    """Le compte de cellules de code passe de 4 a 3 : le message dit
    « exceeds the 4 ... » puis « exceeds the 3 ... », le defaut est identique."""
    base, head = anchor_case
    assert regressions(base, head, Path(base).parent) == []


def test_abs_state_shift_is_not_a_regression(tmp_path):
    """`code[9]` reste non resolue des deux cotes, mais l'index absolu 9 tombe
    sur une cellule markdown en base et sur une cellule de code a la tete :
    `abs_state` passe de `markdown` a `out of notebook` sans nouveau defaut."""
    base = _write(tmp_path / "base.ipynb",
                  [_md("Intro : voir code[9].")] + [_code()] * 4
                  + [_md("note")] + [_code()] * 3 + [_md("pied")]
                  + [_md(t) for t in FILLER])
    head = _write(tmp_path / "head.ipynb",
                  [_md("Intro : voir code[9].")] + [_code()] * 4
                  + [_md("note")] + [_code()] * 4
                  + [_md(t) for t in FILLER])
    assert regressions(base, head, tmp_path) == []


def test_a_genuinely_new_dangling_anchor_is_still_caught(anchor_case):
    """Controle negatif : l'invariant ne doit pas masquer un defaut neuf."""
    base, head = anchor_case
    nb = json.loads(Path(head).read_text(encoding="utf-8"))
    nb["cells"][0] = _md("Intro : voir code[9], et code[42] pour l'annexe.")
    broken = Path(head).parent / "head_new.ipynb"
    broken.write_text(json.dumps(nb), encoding="utf-8")
    new = _anchors(regressions(base, str(broken), Path(head).parent))
    assert len(new) == 1, new
    assert "code[42]" in new[0][1]


def test_repairing_a_dangling_anchor_reports_nothing(anchor_case):
    """Symetrique : reprendre l'ancre sur une cellule qui existe -> 0 finding."""
    base, head = anchor_case
    nb = json.loads(Path(head).read_text(encoding="utf-8"))
    nb["cells"][0] = _md("Intro : voir code[2] pour le detail.")
    fixed = Path(head).parent / "head_fixed.ipynb"
    fixed.write_text(json.dumps(nb), encoding="utf-8")
    assert _anchors(regressions(base, str(fixed), Path(head).parent)) == []
