"""Tests de check_encoding_corruption.py (point 3 de #23021).

Contrôle positif obligatoire : le détecteur DOIT tirer sur un échantillon corrompu
connu, et ne DOIT PAS tirer sur du français sain (accents, tirets cadratins,
nbsp, `â` légitime de « château »).
"""
import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from notebook_tools.check_encoding_corruption import (  # noqa: E402
    count_in_notebook,
    count_in_text,
    main,
)

SCRIPT = Path(__file__).resolve().parents[1] / "check_encoding_corruption.py"


def _nb(cells: list[tuple[str, str]]) -> dict:
    return {
        "cells": [
            {"cell_type": t, "source": s.splitlines(keepends=True), "outputs": []}
            for t, s in cells
        ],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write_nb(tmp_path: Path, name: str, nb: dict) -> Path:
    p = tmp_path / name
    p.write_text(json.dumps(nb, ensure_ascii=False, indent=1), encoding="utf-8")
    return p


# --- contrôle positif : la famille est attrapée, compte exact ---------------

def test_positive_control_mojibake_family():
    # 3 bigrammes distincts de la famille, un de chaque classe.
    assert count_in_text("mÃ©taheuristique") == 1          # Ã + 2e octet
    assert count_in_text("cree â€” resultat") == 1          # E2 80
    assert count_in_text("separateur Â ") == 1         # Â + 2e octet (nbsp)
    assert count_in_text("Å€ signe") == 1                   # C5 80
    assert count_in_text("aÃ§a et lâ€œquoteâ€") == 3


# --- contrôle négatif : le français sain ne tire PAS -------------------------

def test_negative_control_french_clean():
    clean = (
        "métaheuristique — plateau château naïve à è ü "
        "µ ° ¢ · nbsp ici et Ångström Å suédois"
    )
    assert count_in_text(clean) == 0


def test_clean_notebook_passes(tmp_path):
    nb = _nb([
        ("markdown", "# Plateau — métaheuristiques à è ü\n"),
        ("code", "print('chateau naïve — ok')\n"),
    ])
    p = _write_nb(tmp_path, "clean.ipynb", nb)
    assert count_in_notebook(p) == 0
    assert main([str(p)]) == 0


def test_corrupted_notebook_detected(tmp_path):
    nb = _nb([
        ("markdown", "## mÃ©taheuristiques plateau Â \n"),
        ("code", "print('cree â€” graphe')\n"),
    ])
    p = _write_nb(tmp_path, "corrupt.ipynb", nb)
    assert count_in_notebook(p) == 3
    assert main([str(p)]) == 1


def test_directory_scan_ignores_markdown(tmp_path):
    # Le littéral Ã© est légitime dans la prose .md qui documente la classe :
    # le scan de répertoire ne regarde que les .ipynb.
    (tmp_path / "docs.md").write_text("Classe d'artefact : Ã©, â€”\n", encoding="utf-8")
    nb = _nb([("markdown", "# propre\n")])
    _write_nb(tmp_path, "ok.ipynb", nb)
    assert main([str(tmp_path)]) == 0


def test_non_notebook_file_is_usage_error(tmp_path):
    f = tmp_path / "notes.md"
    f.write_text("Ã©\n", encoding="utf-8")
    with pytest.raises(SystemExit) as ei:
        main([str(f)])
    assert ei.value.code == 2


# --- mode --base : seule la LIGNE AJOUTÉE bloque -----------------------------

def test_base_mode_added_line_only(tmp_path):
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "t@t"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "t"], cwd=tmp_path, check=True)
    # état de base : carnet propre, commité.
    _write_nb(tmp_path, "nb.ipynb", _nb([("markdown", "# propre\n")]))
    subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "base"], cwd=tmp_path, check=True)
    # l'HEAD ajoute une ligne saine : rien à signaler.
    _write_nb(tmp_path, "nb.ipynb", _nb([("markdown", "# propre\n\nligne saine — à\n")]))
    subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "clean-add"], cwd=tmp_path, check=True)
    r = subprocess.run(
        [sys.executable, str(SCRIPT), "--base", "HEAD~1"],
        cwd=tmp_path, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    assert r.returncode == 0, r.stdout + r.stderr
    # l'HEAD ajoute une ligne corrompue : bloquant.
    _write_nb(tmp_path, "nb.ipynb", _nb([("markdown", "# propre\n\nligne saine — à\n\nmÃ©ta\n")]))
    subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "corrupt-add"], cwd=tmp_path, check=True)
    r = subprocess.run(
        [sys.executable, str(SCRIPT), "--base", "HEAD~1"],
        cwd=tmp_path, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    assert r.returncode == 1
    assert "nb.ipynb" in r.stdout


def test_base_mode_existing_corruption_not_reblocked(tmp_path):
    # Un carnet déjà corrompu en base, touché par une ligne saine, ne re-bloque
    # PAS : seule la matière ajoutée compte.
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "t@t"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "t"], cwd=tmp_path, check=True)
    _write_nb(tmp_path, "nb.ipynb", _nb([("markdown", "mÃ©ta en base\n")]))
    subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "base-corrupt"], cwd=tmp_path, check=True)
    _write_nb(tmp_path, "nb.ipynb", _nb([("markdown", "mÃ©ta en base\n\najout sain — à\n")]))
    subprocess.run(["git", "add", "-A"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-q", "-m", "clean-touch"], cwd=tmp_path, check=True)
    r = subprocess.run(
        [sys.executable, str(SCRIPT), "--base", "HEAD~1"],
        cwd=tmp_path, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    assert r.returncode == 0, r.stdout + r.stderr


def test_self_test():
    assert main(["--self-test"]) == 0
