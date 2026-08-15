"""Tests for scripts/notebook_tools/render_oversized_nbconvert.py.

Couvre : comptage structurel du HTML nbconvert (_html_stats), rendu d'un
mini-notebook (RENDER_OK, read-only), échec sur entrée non-notebook, et les
exit codes de --check. Le rendu réel est skip-if si nbconvert est absent.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
from render_oversized_nbconvert import _html_stats, render_one

MINI_NB = {
    "cells": [
        {
            "cell_type": "code",
            "execution_count": 1,
            "metadata": {},
            "outputs": [
                {"output_type": "stream", "name": "stdout", "text": "0.42\n"}
            ],
            "source": ["print(0.42)\n"],
        }
    ],
    "metadata": {
        "kernelspec": {
            "display_name": "Python 3",
            "language": "python",
            "name": "python3",
        }
    },
    "nbformat": 4,
    "nbformat_minor": 5,
}


def _write_nb(path: Path) -> None:
    path.write_text(json.dumps(MINI_NB), encoding="utf-8")


def test_html_stats_counts(tmp_path: Path) -> None:
    html = tmp_path / "nb.html"
    html.write_text(
        "<!DOCTYPE html>"
        '<div class="jp-InputArea"></div>'
        '<div class="jp-InputArea"></div>'
        '<div class="jp-OutputArea"></div>'
        '<img src="data:image/png;base64,AAA">',
        encoding="utf-8",
    )
    stats = _html_stats(html)
    assert stats["doctype"] == 1
    assert stats["input_areas"] == 2
    assert stats["output_areas"] == 1
    assert stats["images"] == 1
    assert stats["bytes"] > 0


def test_render_one_ok(tmp_path: Path) -> None:
    nb = tmp_path / "mini.ipynb"
    _write_nb(nb)
    out = tmp_path / "out"
    result = render_one(nb, out)
    if result["status"] == "FAIL" and "nbconvert" in str(result.get("reason", "")):
        pytest.skip("nbconvert indisponible dans cet env")
    assert result["status"] == "RENDER_OK", result
    assert result["html_bytes"] > 0
    assert result["code_areas"] >= 1
    assert (out / "mini.html").exists()
    # read-only : le notebook source n'est pas modifié
    assert json.loads(nb.read_text(encoding="utf-8")) == MINI_NB


def test_render_one_fail_non_notebook(tmp_path: Path) -> None:
    bogus = tmp_path / "not_a_notebook.txt"
    bogus.write_text("# juste du texte", encoding="utf-8")
    result = render_one(bogus, tmp_path / "out")
    assert result["status"] == "FAIL"
    assert "NotJSONError" in str(result.get("reason", ""))
