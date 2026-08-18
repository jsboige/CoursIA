"""Tests pour check_outputs_text_fragmentation.py (cf. #11667, c.354-L2).

Cas fondateur : output stream dont ``text`` est une liste de 778 strings
d'1 char chacune (au lieu de 9 strings avec \\n final). Le detecteur doit
flagger cette signature (mediane <= 2 chars) sans flagger les sorties
legitimes (lignes courtes, single-char items, etc.).
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

SCRIPT = Path(__file__).resolve().parents[1] / "check_outputs_text_fragmentation.py"


def _make_nb(tmp_path: Path, cell_outputs: list[dict]) -> Path:
    """Cree un notebook minimal avec les outputs specifiee dans la cellule 0."""
    nb = {
        "cells": [
            {
                "cell_type": "code",
                "execution_count": 1,
                "metadata": {},
                "outputs": cell_outputs,
                "source": ["print('hello')"],
            }
        ],
        "metadata": {"kernelspec": {"name": "python3", "display_name": "Python 3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    p = tmp_path / "test.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    return p


def _stream_output(text: list[str]) -> dict:
    return {"output_type": "stream", "name": "stdout", "text": text}


# --- Tests principaux ---


def test_founder_case_flagged(tmp_path: Path) -> None:
    """Cas fondateur c.354 : 9 lignes reelles -> items d'1 char -> FLAGGED."""
    # Reproduction exacte : 9 lignes, total ~800 chars, list() fragmente.
    # Chemin machine c.354 scrubbe en placeholder (categorie-A standing,
    # cf. secrets-and-coord-detail.md §1.6 : une fixture de test ne doit pas
    # embarquer de chemin absolu machine).
    content = (
        "Materiel de reference accessible : <path-redacted>\n"
        "\n"
        "Fichier                                syll   motion  flat%  span  verdict\n"
        "----------------------------------------------------------------------------------\n"
        "E_plat_registre_grave.wav               120    1.28st  52.9%  2.05st  DRONE\n"
        "F1_plat_registre_clair.wav             120    1.05st  56.7%  2.00st  DRONE\n"
        "G1_melodique_registre_grave.wav        120    3.06st  17.8%  5.84st  EXPRESSIVE\n"
        "L2_long_melodique_grave.wav            120    4.31st   8.3%  7.05st  EXPRESSIVE\n"
        "L3_long_melodique_grave.wav            120    3.87st  11.5%  6.43st  EXPRESSIVE\n"
    )
    text_fragmented = list(content)  # char-par-char
    assert len(text_fragmented) >= 100  # bien au-dessus de MIN_TEXT_ITEMS=10
    p = _make_nb(tmp_path, [_stream_output(text_fragmented)])
    res = subprocess.run(
        [sys.executable, str(SCRIPT), str(p), "--check"],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 1, f"devrait flagger, exit={res.returncode}, stderr={res.stderr}"
    assert "FRAGMENTED" in res.stdout


def test_normal_multiline_output_passes(tmp_path: Path) -> None:
    """Sortie multi-lignes normale (text = list of lines avec \\n) -> OK."""
    text = [
        "Materiel de reference accessible : G:\\Mon Drive\n",
        "\n",
        "Fichier                                syll   motion\n",
        "----------------------------------------------------------------------------------\n",
        "E_plat_registre_grave.wav               120    1.28st  52.9%  2.05st  DRONE\n",
        "F1_plat_registre_clair.wav             120    1.05st  56.7%  2.00st  DRONE\n",
        "G1_melodique_registre_grave.wav        120    3.06st  17.8%  5.84st  EXPRESSIVE\n",
        "L2_long_melodique_grave.wav            120    4.31st   8.3%  7.05st  EXPRESSIVE\n",
        "L3_long_melodique_grave.wav            120    3.87st  11.5%  6.43st  EXPRESSIVE\n",
    ]
    p = _make_nb(tmp_path, [_stream_output(text)])
    res = subprocess.run(
        [sys.executable, str(SCRIPT), str(p), "--check"],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0, f"ne devrait PAS flagger, stderr={res.stderr}"


def test_short_output_under_threshold_passes(tmp_path: Path) -> None:
    """Sortie < MIN_TEXT_ITEMS items : pas de faux positif."""
    # 5 items d'1 char = en-dessous du seuil MIN_TEXT_ITEMS=10
    text = list("hello")  # 5 chars
    p = _make_nb(tmp_path, [_stream_output(text)])
    res = subprocess.run(
        [sys.executable, str(SCRIPT), str(p), "--check"],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0, f"court OK, stderr={res.stderr}"


def test_single_long_line_passes(tmp_path: Path) -> None:
    """Une seule longue ligne (mediane elevee) : OK."""
    text = ["This is a single very long line of output without any newlines, " * 5 + "\n"]
    p = _make_nb(tmp_path, [_stream_output(text)])
    res = subprocess.run(
        [sys.executable, str(SCRIPT), str(p), "--check"],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0


def test_display_data_output_ignored(tmp_path: Path) -> None:
    """output_type=display_data (avec data:image/png) -> ignore, pas stream."""
    output = {
        "output_type": "display_data",
        "data": {"image/png": "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABAQMAAAAl21bKAAAAA1BMVEX/AAAZ4gk3AAAAAXRSTlMAQObYZgAAAApJREFUeJxjAAAAAgABz8g15QAAAABJRU5ErkJggg=="},
        "metadata": {},
    }
    p = _make_nb(tmp_path, [output])
    res = subprocess.run(
        [sys.executable, str(SCRIPT), str(p), "--check"],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0, f"display_data ignore, stderr={res.stderr}"


def test_markdown_cells_ignored(tmp_path: Path) -> None:
    """Les cellules markdown ne sont pas scannees."""
    nb = {
        "cells": [
            {
                "cell_type": "markdown",
                "metadata": {},
                "source": ["# Heading\n"],
            }
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    p = tmp_path / "test.ipynb"
    p.write_text(json.dumps(nb), encoding="utf-8")
    res = subprocess.run(
        [sys.executable, str(SCRIPT), str(p), "--check"],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0


def test_json_output_stable(tmp_path: Path) -> None:
    """Sortie --json structure stable avec findings + summary."""
    content = "x" * 100
    p = _make_nb(tmp_path, [_stream_output(list(content))])
    res = subprocess.run(
        [sys.executable, str(SCRIPT), str(p), "--json"],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0
    payload = json.loads(res.stdout)
    assert "findings" in payload
    assert "summary" in payload
    assert payload["summary"]["files_scanned"] == 1
    assert payload["summary"]["findings_total"] >= 1
    f = payload["findings"][0]
    assert f["severity"] == "FRAGMENTED"
    assert f["median_text_len"] <= 2
    assert f["n_text_items"] == 100


def test_multiple_outputs_mixed(tmp_path: Path) -> None:
    """Cellule avec 1 output stream OK + 1 output stream fragmented : 1 finding."""
    ok_text = ["normal output line 1\n", "normal output line 2\n", "normal output line 3\n"]
    frag_text = list("z" * 50)  # 50 items d'1 char
    p = _make_nb(tmp_path, [_stream_output(ok_text), _stream_output(frag_text)])
    res = subprocess.run(
        [sys.executable, str(SCRIPT), str(p), "--check"],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 1, "au moins 1 fragmented -> exit 1"
    # 1 seul finding (l'output OK n'est pas flague)
    findings = [line for line in res.stdout.splitlines() if line.startswith("[FRAGMENTED]")]
    assert len(findings) == 1


# --- Tests de mutation (cf. c.344-L1 ★★ : tester par faux negatifs) ---


def test_mutation_disable_threshold_caught(tmp_path: Path) -> None:
    """Si le seuil est desactive (mediane <= MEDIAN_THRESHOLD -> None),
    un notebook legerement au-dessus du seuil (mediane 3) doit etre capture
    par la perte de detection : c'est ce qui prouve que le seuil EST actif.
    """
    # MEDIAN_THRESHOLD=2 ; on construit un cas mediane=3 : 10 items "ab\n"
    # (3 chars) + 1 item "x"*100 (100 chars) -> 11 items, mediane entre
    # item 5 et 6 = (3+3)/2 = 3, au-dessus du seuil.
    text = ["ab\n"] * 10 + ["x" * 100 + "\n"]
    p = _make_nb(tmp_path, [_stream_output(text)])
    res = subprocess.run(
        [sys.executable, str(SCRIPT), str(p), "--check"],
        capture_output=True,
        text=True,
    )
    # mediane = 3 > seuil 2 -> PAS flagger (sinon MEDIAN_THRESHOLD serait mort)
    assert res.returncode == 0, f"mediane 3 > seuil 2 -> OK, stderr={res.stderr}"


def test_explain_mode() -> None:
    """--explain imprime le docstring et exit 0."""
    res = subprocess.run(
        [sys.executable, str(SCRIPT), "--explain"],
        capture_output=True,
        text=True,
    )
    assert res.returncode == 0
    assert "fragmentation" in res.stdout.lower() or "fragment" in res.stdout.lower()
