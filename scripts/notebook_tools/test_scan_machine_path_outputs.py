#!/usr/bin/env python3
"""Tests du scanner #11725 (chemins machine dans les sorties commitees).

Prouvent les trois surfaces portees par l'issue (text, data['text/*'],
traceback), le silence sur les sources, le silence sur les notebook propres,
et le collapse des variantes de casse dans les prefixes.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from scan_machine_path_outputs import MACHINE_PATH_RE, scan_notebook, scan_tree


def make_notebook(outputs):
    return {
        "cells": [{"cell_type": "code", "outputs": outputs, "source": []}],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def write_notebook(root: Path, rel: str, nb) -> Path:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return path


def test_clean_notebook_has_no_hits(tmp_path):
    nb = make_notebook([
        {"output_type": "stream", "name": "stdout", "text": [" modele charge\n"]},
    ])
    path = write_notebook(tmp_path, "clean.ipynb", nb)
    assert scan_notebook(path) == []


def test_stream_output_text_counted(tmp_path):
    nb = make_notebook([
        {"output_type": "stream", "name": "stdout",
         "text": ["env_path=D:\\Dev\\CoursIA\\.env\n"]},
    ])
    path = write_notebook(tmp_path, "stream.ipynb", nb)
    hits = scan_notebook(path)
    assert len(hits) == 1
    assert hits[0]["prefix"] == "D:\\DEV"


def test_data_text_plain_counted(tmp_path):
    nb = make_notebook([
        {"output_type": "execute_result",
         "data": {"text/plain": ["WindowsPath('c:\\users\\jsboi\\models\\qwen')"]},
         "metadata": {}},
    ])
    path = write_notebook(tmp_path, "data.ipynb", nb)
    hits = scan_notebook(path)
    assert len(hits) == 1
    assert hits[0]["prefix"] == "C:\\USERS"


def test_data_binary_key_ignored(tmp_path):
    nb = make_notebook([
        {"output_type": "display_data",
         "data": {"image/png": ["D:\\Dev\\CoursIA\\img.png"]},
         "metadata": {}},
    ])
    path = write_notebook(tmp_path, "binary.ipynb", nb)
    assert scan_notebook(path) == []


def test_traceback_counted(tmp_path):
    nb = make_notebook([
        {"output_type": "error", "ename": "FileNotFoundError",
         "evalue": "missing",
         "traceback": ["FileNotFoundError: D:\\dev\\myia\\weights.bin introuvable"]},
    ])
    path = write_notebook(tmp_path, "tb.ipynb", nb)
    hits = scan_notebook(path)
    assert len(hits) == 1
    assert hits[0]["prefix"] == "D:\\DEV"


def test_source_path_not_counted(tmp_path):
    nb = make_notebook([])
    nb["cells"][0]["source"] = ["env_path = r'D:\\Dev\\CoursIA\\.env'"]
    path = write_notebook(tmp_path, "src.ipynb", nb)
    assert scan_notebook(path) == []


def test_case_variants_collapse_to_same_prefix(tmp_path):
    nb = make_notebook([
        {"output_type": "stream", "name": "stdout",
         "text": ["d:\\dev\\a\n", "D:\\Dev\\b\n", "d:\\Dev\\c\n"]},
    ])
    path = write_notebook(tmp_path, "case.ipynb", nb)
    hits = scan_notebook(path)
    assert len(hits) == 3
    assert {h["prefix"] for h in hits} == {"D:\\DEV"}


def test_non_code_cell_ignored(tmp_path):
    nb = {
        "cells": [
            {"cell_type": "markdown",
             "source": ["doc: fichier sous D:\\Dev\\CoursIA\\data"]},
        ],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }
    path = write_notebook(tmp_path, "md.ipynb", nb)
    assert scan_notebook(path) == []


def test_scan_tree_relative_paths_and_family(tmp_path):
    write_notebook(tmp_path, "Audio/x.ipynb", make_notebook([
        {"output_type": "stream", "name": "stdout", "text": ["D:\\Dev\\a\n"]},
    ]))
    write_notebook(tmp_path, "Audio/y.ipynb", make_notebook([]))
    write_notebook(tmp_path, "Texte/z.ipynb", make_notebook([
        {"output_type": "stream", "name": "stdout", "text": ["C:\\Users\\b\n"]},
    ]))
    inv = scan_tree(tmp_path)
    assert inv["scanned"] == 3
    assert inv["notebooks_with_hits"] == 2
    assert inv["occurrences"] == 2
    assert set(inv["notebooks"]) == {"Audio/x.ipynb", "Texte/z.ipynb"}
    assert inv["by_family"]["Audio"]["occurrences"] == 1


def test_scan_tree_skips_checkpoint_dirs(tmp_path):
    write_notebook(tmp_path, ".ipynb_checkpoints/w.ipynb", make_notebook([
        {"output_type": "stream", "name": "stdout", "text": ["D:\\Dev\\a\n"]},
    ]))
    inv = scan_tree(tmp_path)
    assert inv["scanned"] == 0
    assert inv["occurrences"] == 0


def test_regex_shape_matches_single_backslash_only():
    # Un seul antislash litteral doit matcher ; deux antislashs (chemin
    # echappe dans du JSON brut par exemple) ne matchent pas doublement.
    assert MACHINE_PATH_RE.search("D:\\Dev\\x")
    assert MACHINE_PATH_RE.search("c:\\users\\x")
    assert MACHINE_PATH_RE.search("D:\\MyIA\\x")
    assert not MACHINE_PATH_RE.search("D:\\Other\\x")
    assert not MACHINE_PATH_RE.search("D:Dev")


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
