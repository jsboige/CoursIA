"""Tests de ``scripts/notebook_tools/fix_hint_headings.py`` (#22477).

Le defaut couvert : le fixer ne voyait que le titre ATX **imbrique** dans une
puce ou une citation (``- # Indice : X``). Un commentaire d'exercice recopie
**nu** (``# Indice : X``) lui echappait, alors qu'il produit exactement le meme
degat au rendu CommonMark : un ``<h1>`` de la taille du titre de page la ou le
texte devrait etre du corps.

Deux conditions separent un commentaire recopie d'une vraie section, et la
seconde vient de la mesure, pas de l'intuition : le **deux-points** (marqueur +
corps), et le **niveau h1**. Sur les 1648 carnets du corpus, 142 titres de
marqueur nus sont candidats ; les 20 de niveau h2-h4 ont ete lus un a un et sont
TOUS de vraies sections (``### Solution : Plugins``, ``## Step 1: Load USDCAD
Price Data``, ``### Note : mode batch``, ``#### Etape 1 : creer un fichier Lean``).
Les backticker transformerait un titre de section en ligne de code -- le remede
serait pire que le defaut. Une section legitime du corpus (``### Indices`` dans
``QC-Py-02-Platform-Fundamentals``) doit rester intacte pour la meme raison.

L'invariant de round-trip est verifie comme une propriete, pas sur un cas
choisi : pour toute ligne modifiee, retirer les backticks redonne la ligne
d'origine a l'identique. C'est lui qui autorise ``process`` a ecrire.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from fix_hint_headings import _fix_line, process, scan_cell


# ---------------------------------------------------------------------------
# Branche nue (#22477) : ce qui doit etre repare
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "before, after",
    [
        ("# Indice : calculez X", "`# Indice` : calculez X"),
        ("# Etape 1 : ouvrir le fichier", "`# Etape 1` : ouvrir le fichier"),
        ("# Étape 2 : appliquez la formule", "`# Étape 2` : appliquez la formule"),
        ("# Note : valeur arrondie a 2 decimales", "`# Note` : valeur arrondie a 2 decimales"),
        ("# TODO : implementer le scoring", "`# TODO` : implementer le scoring"),
        ("# TODO: implementer le scoring", "`# TODO`: implementer le scoring"),
        ("# Astuce : utilisez numpy", "`# Astuce` : utilisez numpy"),
        ("# Hint : essayez un autre seed", "`# Hint` : essayez un autre seed"),
    ],
)
def test_naked_marker_heading_is_fixed(before, after):
    assert _fix_line(before) == after


@pytest.mark.parametrize(
    "line",
    [
        "### Indices",                 # section legitime (Principe / Objectif / Indices)
        "# Indices",
        "## Etape 2",                  # marqueur, mais aucun corps : titre de section
        "# Indice",
        "# Introduction : vue d'ensemble du probleme",   # deux-points, pas marqueur
        "# Resultat : 42",                                # deux-points, pas marqueur
        "Texte normal avec un deux-points : oui",
        "`# Indice` : calculez X",     # deja protege
        "`## Etape 2` : appliquez",    # deja protege
        "",                            # ligne vide
    ],
)
def test_untouched_lines(line):
    assert _fix_line(line) is None


# ---------------------------------------------------------------------------
# Le niveau h1 est la seconde condition (#22477) — mesurement, pas intuition
# ---------------------------------------------------------------------------

#: Les six formes reelles mesurees dans le corpus au niveau h2-h4 et lues une a
#: une comme des sections legitimes. Backticker l'une d'elles ne repare rien :
#: elle transforme un titre de section (ancre, table des matieres, hierarchie)
#: en ligne de code. C'est le faux positif qu'une regle « deux-points seul »
#: produirait sur 20 occurrences du corpus.
_MEASURED_LEGIT_SECTIONS = [
    "#### Etape 1 : creer un fichier Lean",              # Lean-01-Setup-Lean, cell#24
    "### Solution : Plugins",                            # Lean-09-SK-Multi-Agents, cell#7
    "### Solution : Shrinkage (Ledoit-Wolf)",            # QC-Py-21, cell#23
    "## Step 1: Load USDCAD Price Data",                 # quantbook research.ipynb, cell#3
    "### Note : mode batch",                             # fort-boyard-python, cell#1
    "### Note: batch mode",                              # fort-boyard-python_en, cell#1
]


@pytest.mark.parametrize("line", _MEASURED_LEGIT_SECTIONS)
def test_marker_heading_at_h2_or_deeper_is_a_section(line):
    assert _fix_line(line) is None, (
        "un titre de marqueur de niveau h2-h4 est une section, pas une fuite de "
        "commentaire : le backticker casserait le rendu"
    )


def test_minimal_h1_heading_without_colon_still_untouched():
    """Le niveau seul ne suffit pas non plus : sans corps, c'est un titre."""
    assert _fix_line("# Indice") is None
    assert _fix_line("# Solution") is None


# ---------------------------------------------------------------------------
# La branche conteneur ne doit pas regresser
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "before, after",
    [
        ("- # Indice : calculez X", "- `# Indice` : calculez X"),
        ("* ## Etape 1 : ouvrez le notebook", "* `## Etape 1` : ouvrez le notebook"),
        ("1. # Note : attention", "1. `# Note` : attention"),
        ("> # Solution : voir plus bas", "> `# Solution` : voir plus bas"),
    ],
)
def test_container_heading_still_fixed(before, after):
    assert _fix_line(before) == after


def test_container_already_protected_untouched():
    assert _fix_line("- `# Indice` : calculez X") is None


def test_container_non_marker_untouched():
    """Un titre imbrique qui n'est pas un marqueur n'est pas devine."""
    assert _fix_line("- # Cout de transaction : 5 bps") is None


# ---------------------------------------------------------------------------
# Invariant de round-trip : seuls des backticks sont inseres
# ---------------------------------------------------------------------------

_ROUND_TRIP_SAMPLE = [
    "# Indice : calculez X",
    "# Etape 2 : appliquez la formule",
    "- # Indice : calculez X",
    "  * ## Note : attention",
    "> # Solution : voir plus bas",
    # Espacement non canonique : c'est ici que la reconstruction fidele compte.
    # Un ``" : "`` dur transformerait la ligne, et ``process`` refuserait alors
    # d'ecrire le fichier au lieu de le corriger.
    "# Indice  :  calculez X",
    "# Indice: sans espace avant le deux-points",
    "# Note\t: tabulation avant le deux-points",
]


@pytest.mark.parametrize("line", _ROUND_TRIP_SAMPLE)
def test_round_trip_only_inserts_backticks(line):
    fixed = _fix_line(line)
    assert fixed is not None, f"ligne non reparee alors qu'elle devait l'etre : {line!r}"
    assert fixed.replace("`", "") == line.replace("`", ""), (
        f"le contenu a change au-dela des backticks : {line!r} -> {fixed!r}"
    )


def test_round_trip_preserves_non_canonical_spacing():
    assert _fix_line("# Indice  :  calculez X") == "`# Indice`  :  calculez X"


# ---------------------------------------------------------------------------
# scan_cell / process
# ---------------------------------------------------------------------------

def test_scan_cell_reports_line_index_and_pair():
    src = "Intro\n# Indice : calculez X\nSuite"
    hits = scan_cell(src)
    assert len(hits) == 1
    idx, before, after = hits[0]
    assert idx == 1
    assert before == "# Indice : calculez X"
    assert after == "`# Indice` : calculez X"


def test_scan_cell_ignores_legit_section():
    assert scan_cell("### Indices\n\n1. Principe\n2. Objectif\n3. Indices") == []


def _nb(cells: list[dict]) -> dict:
    return {
        "cells": cells,
        "metadata": {"kernelspec": {"name": "python3", "display_name": "Python 3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _md(text: str) -> dict:
    """Cellule markdown au format nbformat : chaque ligne porte son ``\\n`` sauf
    la derniere. ``split("\\n")`` nu produirait une cellule qui ne se re-joint
    pas -- et le test mesurerait alors le helper, pas le fixer."""
    parts = text.split("\n")
    return {
        "cell_type": "markdown",
        "metadata": {},
        "source": [l + "\n" for l in parts[:-1]] + [parts[-1]],
    }


def _write(tmp_path: Path, nb: dict) -> Path:
    p = tmp_path / "nb.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


def test_process_dry_run_changes_nothing(tmp_path):
    path = _write(tmp_path, _nb([_md("# Indice : calculez X")]))
    before = path.read_bytes()
    n, report = process(path, apply=False)
    assert n == 1
    assert len(report) == 1
    assert path.read_bytes() == before


def test_process_apply_fixes_and_spares_the_legit_section(tmp_path):
    path = _write(
        tmp_path,
        _nb([
            _md("# Indice : calculez X"),
            _md("### Indices\n\n1. Principe\n2. Objectif\n3. Indices"),
        ]),
    )
    n, _ = process(path, apply=True)
    assert n == 1
    nb = json.loads(path.read_text(encoding="utf-8"))
    assert "`# Indice` : calculez X" in "".join(nb["cells"][0]["source"])
    assert "".join(nb["cells"][1]["source"]) == (
        "### Indices\n\n1. Principe\n2. Objectif\n3. Indices"
    )


def test_process_ignores_code_cells(tmp_path):
    """Le meme texte dans une cellule de code est un commentaire Python legitime."""
    path = _write(
        tmp_path,
        _nb([{
            "cell_type": "code",
            "execution_count": 1,
            "metadata": {},
            "outputs": [],
            "source": ["# Indice : calculez X"],
        }]),
    )
    n, _ = process(path, apply=True)
    assert n == 0
    nb = json.loads(path.read_text(encoding="utf-8"))
    assert nb["cells"][0]["source"] == ["# Indice : calculez X"]


def test_process_apply_keeps_source_list_shape(tmp_path):
    """La cellule doit rester une liste de lignes, chaque ligne finissant par \\n
    sauf la derniere -- c'est la forme que nbformat ecrit."""
    path = _write(tmp_path, _nb([_md("# Indice : calculez X\nSuite sans saut final")]))
    process(path, apply=True)
    nb = json.loads(path.read_text(encoding="utf-8"))
    src = nb["cells"][0]["source"]
    assert isinstance(src, list)
    assert all(l.endswith("\n") for l in src[:-1])
    assert not src[-1].endswith("\n")
    assert "".join(src) == "`# Indice` : calculez X\nSuite sans saut final"


def test_process_reports_nothing_on_clean_notebook(tmp_path):
    path = _write(tmp_path, _nb([_md("### Indices\n\n1. Principe")]))
    n, report = process(path, apply=True)
    assert (n, report) == (0, [])


def test_apply_does_not_rewrite_the_file_in_crlf(tmp_path):
    """``write_text`` sans ``newline="\\n"`` reecrit tout le fichier en CRLF.

    Mesure du 2026-10-25 : 1955 lignes remplacees pour 4 lignes reparees sur
    ``GameTheory-04g-Supermodularite-Python.ipynb``. Le depot est en LF ; un
    diff de 2000 lignes noierait la reparation et le fichier partirait en CRLF.
    """
    nb = _nb([_md("# Indice : calculez X"), _md("Texte inchange")])
    original = json.dumps(nb, ensure_ascii=False, indent=1) + "\n"
    path = tmp_path / "nb.ipynb"
    path.write_bytes(original.encode("utf-8"))

    n, _ = process(path, apply=True)
    assert n == 1

    after = path.read_bytes()
    assert b"\r\n" not in after, "le fichier est reparti en CRLF"
    before_lines, after_lines = original.split("\n"), after.decode("utf-8").split("\n")
    assert len(before_lines) == len(after_lines), "le nombre de lignes a change"
    changed = [
        (b, a) for b, a in zip(before_lines, after_lines) if b != a
    ]
    assert len(changed) == 1, f"lignes modifiees inattendues : {changed}"
    b, a = changed[0]
    assert b.replace("`", "") == a.replace("`", "")
    assert "`# Indice` : calculez X" in a


def test_apply_leaves_a_clean_corpus_file_byte_identical(tmp_path):
    """Un carnet sans occurrence ne doit pas etre reecrit du tout."""
    nb = _nb([_md("### Indices\n\n1. Principe")])
    original = json.dumps(nb, ensure_ascii=False, indent=1) + "\n"
    path = tmp_path / "nb.ipynb"
    path.write_bytes(original.encode("utf-8"))
    process(path, apply=True)
    assert path.read_bytes() == original.encode("utf-8")
