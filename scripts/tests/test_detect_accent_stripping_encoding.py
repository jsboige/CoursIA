"""Test unitaire -- detect_accent_stripping.py : encodage stdout UTF-8 (cp1252 safe).

Issue #15815 : sur Windows (cp1252 par defaut), detect_accent_stripping crashait
avec UnicodeEncodeError des qu'une cellule contenait un caractere hors-cp1252
(`↔` `→` `←` `⇔` `≡`), frequents en prose FR.

Le fix (3 lignes dans detect_accent_stripping.py) appelle sys.stdout.reconfigure
en utf-8 (avec hasattr pour compatibilite Python < 3.7). Ce test verifie que le
script tient sur un notebook stub contenant `↔`.
"""
import json
import subprocess
import sys
import tempfile
from pathlib import Path

import nbformat


def _make_notebook_with_double_arrow(path: Path) -> None:
    """Cree un notebook minimal dont la cellule markdown contient `↔`."""
    nb = nbformat.v4.new_notebook()
    md_cell = nbformat.v4.new_markdown_cell(
        source="Test pedagogique FR avec fleche double : from-scratch ↔ nashpy",
    )
    code_cell = nbformat.v4.new_code_cell(
        source="# variable normalisee → utilisation\nresultat = None",
    )
    nb.cells = [md_cell, code_cell]
    nbformat.write(nb, str(path))


def test_stdout_reconfigure_handles_double_arrow(tmp_path):
    """Le script ne doit pas crash sur une cellule markdown contenant `↔`."""
    nb_path = tmp_path / "test_arrow.ipynb"
    _make_notebook_with_double_arrow(nb_path)

    # On force un encoding cp1252 pour simuler la condition Windows par defaut.
    env = {
        "PYTHONIOENCODING": "cp1252",
        "PATH": "/usr/bin:/bin",
    }
    result = subprocess.run(
        [sys.executable, "scripts/notebook_tools/detect_accent_stripping.py", str(nb_path), "--check"],
        capture_output=True,
        encoding="utf-8",
        errors="replace",
        env=env,
        cwd=str(Path(__file__).resolve().parents[2]),
        timeout=60,
    )

    # La sortie peut contenir "hits" (le notebook stub contient "resultat" qui matche
    # le pattern), ou non. Le test ne verifie pas le verdict -- il verifie l'absence
    # d'UnicodeEncodeError, qui etait le bug.
    combined = (result.stdout or "") + (result.stderr or "")
    assert "UnicodeEncodeError" not in combined, (
        f"detect_accent_stripping a leve UnicodeEncodeError avec PYTHONIOENCODING=cp1252 :\n"
        f"stdout={result.stdout!r}\nstderr={result.stderr!r}"
    )
    assert "charmap" not in combined, (
        f"detect_accent_stripping a tente d'encoder en charmap (cp1252) :\n"
        f"stdout={result.stdout!r}\nstderr={result.stderr!r}"
    )


def test_stdout_reconfigure_handles_json_mode(tmp_path):
    """Le mode --json ne doit pas lever d'exception sur un notebook avec `↔`."""
    nb_path = tmp_path / "test_arrow_json.ipynb"
    _make_notebook_with_double_arrow(nb_path)

    env = {"PYTHONIOENCODING": "cp1252"}
    result = subprocess.run(
        [sys.executable, "scripts/notebook_tools/detect_accent_stripping.py", str(nb_path), "--json"],
        capture_output=True,
        encoding="utf-8",
        errors="replace",
        env=env,
        cwd=str(Path(__file__).resolve().parents[2]),
        timeout=60,
    )

    combined = (result.stdout or "") + (result.stderr or "")
    assert "UnicodeEncodeError" not in combined, (
        f"detect_accent_stripping --json a leve UnicodeEncodeError :\n"
        f"stdout={result.stdout!r}\nstderr={result.stderr!r}"
    )
    # Si la sortie est du JSON, il doit etre valide (le bug crashait json.dump avant fin).
    if result.stdout and result.stdout.strip().startswith("{"):
        try:
            json.loads(result.stdout)
        except json.JSONDecodeError as e:
            pytest.fail(f"Sortie --json invalide : {e}\n{result.stdout!r}")
