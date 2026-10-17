"""Tests du garde #21006 : les inputs inexistants ne s'écartent plus en silence.

``scripts/translation/extract_cells_to_csv.py`` filtre ``args.input`` sur
``p.exists()`` avant tout traitement. Avant #21006, les chemins écartés
l'étaient SANS signal : une invocation aux chemins pollués (fichier de
cibles écrit en mode texte Windows, chemins tronqués) ne traitait qu'une
partie des cibles avec des compteurs plausibles — le traitement partiel se
lisait comme un traitement complet (mesure : lot #20997, rétraction c.123).

Contrat testé ici :

  1. un input inexistant parmi des valides -> WARNING sur stderr listant
     le chemin écarté VERBATIM, le run continue (exit 0) ;
  2. tous les inputs inexistants -> ERROR + exit 2 (comportement préexistant,
     gardé sous test) ;
  3. aucun input inexistant -> aucun WARNING émis.

Les notebooks sont synthétiques (tmp_path), CPU-only, stdlib + pytest —
même gabarit que ``test_translation_sync.py``.

Run with: pytest scripts/tests/test_extract_cells_inputs.py -v
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

# Le module sous test vit dans scripts/translation/, ce test dans scripts/tests/.
_TRANSLATION_DIR = Path(__file__).resolve().parent.parent / "translation"
sys.path.insert(0, str(_TRANSLATION_DIR))

import extract_cells_to_csv as t1  # noqa: E402


def _make_notebook(path: Path) -> Path:
    """Notebook synthétique minimal : une cellule code, une markdown."""
    nb = {
        "cells": [
            {
                "cell_type": "code",
                "id": "code-1",
                "execution_count": 1,
                "metadata": {},
                "outputs": [],
                "source": ["print('bonjour')"],
            },
            {
                "cell_type": "markdown",
                "id": "md-1",
                "metadata": {},
                "source": ["# Titre"],
            },
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return path


@pytest.fixture()
def valid_nb(tmp_path: Path) -> Path:
    return _make_notebook(tmp_path / "serie" / "NB-01.ipynb")


def _run_main(argv: list[str], tmp_path: Path, capsys) -> tuple[int, str]:
    """Invoque t1.main() avec argv contrôlé ; retourne (exit, stderr).

    ``--repo-root`` pointe sur ``tmp_path`` : ``extract_notebook`` calcule les
    chemins relatifs au repo-root (défaut = cwd), et les notebooks
    synthétiques vivent sous tmp_path.
    """
    out_csv = tmp_path / "out.csv"
    old_argv = sys.argv
    sys.argv = [
        "extract_cells_to_csv.py",
        *argv,
        "--output",
        str(out_csv),
        "--repo-root",
        str(tmp_path),
    ]
    try:
        rc = t1.main()
    finally:
        sys.argv = old_argv
    captured = capsys.readouterr()
    return rc, captured.err


def test_warning_lists_dropped_input_verbatim(
    tmp_path: Path, valid_nb: Path, capsys
) -> None:
    """Cas 1 : un input inexistant -> WARNING le nommant, run exit 0."""
    ghost = tmp_path / "nexiste" / "pas.ipynb"
    rc, err = _run_main([str(valid_nb), str(ghost)], tmp_path, capsys)
    assert rc == 0, f"run doit réussir avec au moins un input valide (stderr: {err})"
    assert "WARNING" in err
    assert str(ghost) in err, "le chemin écarté doit apparaître verbatim"


def test_all_invalid_inputs_fail(tmp_path: Path, capsys) -> None:
    """Cas 2 : tous inexistants -> ERROR + exit 2 (garde préexistante)."""
    ghost_a = tmp_path / "a.ipynb"
    ghost_b = tmp_path / "b.ipynb"
    rc, err = _run_main([str(ghost_a), str(ghost_b)], tmp_path, capsys)
    assert rc == 2
    assert "ERROR" in err


def test_no_warning_when_all_inputs_exist(
    tmp_path: Path, valid_nb: Path, capsys
) -> None:
    """Cas 3 : aucun écart -> aucun WARNING."""
    rc, err = _run_main([str(valid_nb)], tmp_path, capsys)
    assert rc == 0
    assert "WARNING" not in err


def test_two_dropped_inputs_both_listed(
    tmp_path: Path, valid_nb: Path, capsys
) -> None:
    """Chaque chemin écarté est listé, pas seulement le premier."""
    ghost_a = tmp_path / "gauche.ipynb"
    ghost_b = tmp_path / "droite.ipynb"
    rc, err = _run_main([str(ghost_a), str(valid_nb), str(ghost_b)], tmp_path, capsys)
    assert rc == 0
    assert str(ghost_a) in err and str(ghost_b) in err
