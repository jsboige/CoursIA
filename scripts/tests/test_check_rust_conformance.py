#!/usr/bin/env python3
"""Temoins du harnais de conformite differentielle Rust (Pli 3, Epic Origami #26510).

Le pli exige DEUX controles :

- **positif** : le pilote `Sudoku/Sudoku-02-DancingLinks-Rust.ipynb` est
  conforme aux cotes declares ;
- **negatif** : une sortie alteree doit etre detectee.

Ces tests sont les temoins : ils rougissent sur un organe qui ne detecte pas
la divergence (controle negatif) ou qui declare conforme un pilote divergent
(controle positif).

Run: python -m pytest scripts/tests/test_check_rust_conformance.py -q
"""
import json
import shutil
import sys
from pathlib import Path

import pytest
import yaml

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts" / "notebook_tools"))

import check_rust_conformance as crc  # noqa: E402

REGISTRY = ROOT / "scripts" / "notebook_tools" / "rust_conformance.d"
PILOT_PY = "MyIA.AI.Notebooks/Sudoku/Sudoku-02-DancingLinks-Python.ipynb"
PILOT_CS = "MyIA.AI.Notebooks/Sudoku/Sudoku-02-DancingLinks-CSharp.ipynb"
PILOT_RS = "MyIA.AI.Notebooks/Sudoku/Sudoku-02-DancingLinks-Rust.ipynb"


def _write_registry(directory: Path, entries: list[dict]) -> Path:
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / "entries.yaml"
    path.write_text(yaml.safe_dump(entries, allow_unicode=True, sort_keys=False),
                    encoding="utf-8")
    return directory


def _mini_notebook(path: Path, output_text: str) -> Path:
    """Ecrit un carnet minimal : une cellule de code, une sortie texte."""
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": [{
            "cell_type": "code",
            "execution_count": 1,
            "metadata": {},
            "outputs": [{"name": "stdout", "output_type": "stream", "text": [output_text]}],
            "source": ["print(1)"],
        }],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb, ensure_ascii=False, indent=1), encoding="utf-8")
    return path


def _copy_pilot(root: Path) -> dict[str, str]:
    """Copie les trois carnets du pilote dans un depot jetable."""
    sides = {"python": PILOT_PY, "csharp": PILOT_CS, "rust": PILOT_RS}
    out = {}
    for side, rel in sides.items():
        target = root / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / rel, target)
        out[side] = rel
    return out


# --- controle POSITIF --------------------------------------------------------


def test_le_pilote_est_conforme():
    """Le pilote, tel qu'il est commite, est conforme : les deux grandeurs
    declarees coincident sur les cotes qui les publient."""
    rc, report = crc.run(REGISTRY, ROOT)
    assert rc == 0, f"pilote non conforme : {json.dumps(report, ensure_ascii=False)}"
    assert report["divergences"] == 0
    entry = report["entries"][0]
    assert entry["name"] == "Sudoku-02 DancingLinks"
    measures = {m["id"]: m for m in entry["measures"]}
    assert measures["solution_grid"]["status"] == "OK"
    assert measures["solution_grid"]["values"]["python"] == \
        measures["solution_grid"]["values"]["rust"]
    assert measures["resolution_ok"]["status"] == "OK"


def test_un_cote_absent_est_signale_sans_echouer():
    """Le cote C# ne materialise pas la grandeur : il est signale (motif lu),
    et sa declaration `absent` n'echoue pas -- l'absence est un fait
    DECLARE, pas une mesure manquante."""
    rc, report = crc.run(REGISTRY, ROOT)
    entry = report["entries"][0]
    grid = next(m for m in entry["measures"] if m["id"] == "solution_grid")
    assert "csharp" in grid["absent"]
    assert grid["absent"]["csharp"].strip()
    assert rc == 0


# --- controle NEGATIF --------------------------------------------------------


def test_une_sortie_alteree_est_detectee(tmp_path):
    """NEGATIF : la grille Rust alteree doit etre detectee.

    Le materiau est le pilote reel (copie dans un depot jetable) : on change un
    seul chiffre de la grille Rust, et l'organe doit signaler la divergence --
    c'est le controle que le pli demande explicitement.
    """
    root = tmp_path / "repo"
    paths = _copy_pilot(root)

    target = root / paths["rust"]
    nb = json.loads(target.read_text(encoding="utf-8"))
    cell = nb["cells"][4]
    text = "".join(
        "".join(o["text"]) for o in cell["outputs"] if "text" in o)
    assert "534678912" in text, "la cellule Rust ne porte pas la grille attendue"
    altered = text.replace("534678912", "534678913")
    cell["outputs"] = [{"name": "stdout", "output_type": "stream",
                        "text": [altered]}]
    target.write_text(json.dumps(nb, ensure_ascii=False, indent=1), encoding="utf-8")

    registry = _write_registry(tmp_path / "registry", [{
        "name": "Sudoku-02 DancingLinks",
        "python": paths["python"],
        "csharp": paths["csharp"],
        "rust": paths["rust"],
        "measures": [{
            "id": "solution_grid",
            "reference": "python",
            "tolerance": 0,
            "sides": {
                "python": {"cell": 16,
                           "pattern": r"Solution trouvee en [^\n]*:\n(.*?)Solution valide",
                           "transform": "digits"},
                "rust": {"cell": 4, "pattern": r"((?:\d{9}\n){9})",
                         "transform": "digits"},
            },
        }],
    }])

    rc, report = crc.run(registry, root)
    assert rc == 1, "la divergence doit etre detectee (rc=1)"
    entry = report["entries"][0]
    assert entry["status"] == "DIVERGENCE"
    grid = next(m for m in entry["measures"] if m["id"] == "solution_grid")
    assert grid["status"] == "DIVERGENCE"
    assert any("rust != python" in f for f in grid["failures"])


def test_une_extraction_illisible_est_un_finding(tmp_path):
    """fail-CLOSED : un cote declare SANS `absent` dont l'extraction echoue est
    un finding -- l'organe ne peut pas se taire sur une extraction vide."""
    root = tmp_path / "repo"
    _mini_notebook(root / "a.ipynb", "rien a voir\n")
    _mini_notebook(root / "b.ipynb", "rien a voir\n")
    registry = _write_registry(tmp_path / "registry", [{
        "name": "factice",
        "python": "a.ipynb",
        "rust": "b.ipynb",
        "measures": [{
            "id": "absente",
            "reference": "python",
            "sides": {
                "python": {"cell": 0, "pattern": "(pas-la)",
                           "transform": "text"},
                "rust": {"cell": 0, "pattern": "(pas-la)",
                         "transform": "text"},
            },
        }],
    }])
    rc, report = crc.run(registry, root)
    assert rc == 1
    failures = report["entries"][0]["measures"][0]["failures"]
    assert any("motif absent" in f for f in failures)


def test_une_cellule_sans_sortie_est_un_finding(tmp_path):
    """Une cellule vide n'est pas une valeur : l'organe le signale."""
    root = tmp_path / "repo"
    _mini_notebook(root / "a.ipynb", "")
    _mini_notebook(root / "b.ipynb", "")
    registry = _write_registry(tmp_path / "registry", [{
        "name": "factice",
        "python": "a.ipynb",
        "rust": "b.ipynb",
        "measures": [{
            "id": "vide",
            "reference": "python",
            "sides": {
                "python": {"cell": 0, "pattern": "(.*)", "transform": "text"},
                "rust": {"cell": 0, "pattern": "(.*)", "transform": "text"},
            },
        }],
    }])
    rc, report = crc.run(registry, root)
    assert rc == 1
    failures = report["entries"][0]["measures"][0]["failures"]
    assert any("sans sortie" in f for f in failures)


# --- la tolerance, unite -----------------------------------------------------


def test_la_tolerance_admise_un_ecart_et_le_refuse_au_dela(tmp_path):
    """La tolerance declaree s'applique aux grandeurs numeriques : sous la
    tolerance, conforme ; au-dela, divergence."""
    root = tmp_path / "repo"
    _mini_notebook(root / "a.ipynb", "valeur : 2.500\n")
    _mini_notebook(root / "b.ipynb", "valeur : 2.502\n")
    measure = {
        "id": "ecart",
        "reference": "python",
        "tolerance": 0.01,
        "sides": {
            "python": {"cell": 0, "pattern": r"valeur : ([\d.]+)", "transform": "float"},
            "rust": {"cell": 0, "pattern": r"valeur : ([\d.]+)", "transform": "float"},
        },
    }
    registry = _write_registry(tmp_path / "registry", [{
        "name": "factice", "python": "a.ipynb", "rust": "b.ipynb",
        "measures": [measure]}])

    rc, _report = crc.run(registry, root)
    assert rc == 0, "un ecart sous la tolerance doit etre accepte"

    measure["tolerance"] = 0.001
    registry = _write_registry(tmp_path / "registry2", [{
        "name": "factice", "python": "a.ipynb", "rust": "b.ipynb",
        "measures": [measure]}])
    rc, _report = crc.run(registry, root)
    assert rc == 1, "un ecart au-dela de la tolerance doit etre refuse"


def test_les_chaines_ignoreent_la_casse_si_demande(tmp_path):
    """`case_insensitive: true` compare sans distinguer la casse (les cotes
    n'ecrivent pas `true` de la meme facon)."""
    root = tmp_path / "repo"
    _mini_notebook(root / "a.ipynb", "resolu=True\n")
    _mini_notebook(root / "b.ipynb", "resolu=true\n")
    sides = {
        "python": {"cell": 0, "pattern": r"resolu=(\w+)", "transform": "text"},
        "rust": {"cell": 0, "pattern": r"resolu=(\w+)", "transform": "text"},
    }
    registry = _write_registry(tmp_path / "registry", [{
        "name": "factice", "python": "a.ipynb", "rust": "b.ipynb",
        "measures": [{"id": "ok", "reference": "python", "sides": sides}]}])
    assert crc.run(registry, root)[0] == 1, "sans case_insensitive, la casse compte"

    registry = _write_registry(tmp_path / "registry2", [{
        "name": "factice", "python": "a.ipynb", "rust": "b.ipynb",
        "measures": [{"id": "ok", "reference": "python",
                      "case_insensitive": True, "sides": sides}]}])
    assert crc.run(registry, root)[0] == 0


def test_un_carnet_absent_est_signale(tmp_path):
    """Un chemin declare qui n'existe pas est une anomalie du triplet, pas un
    silence."""
    root = tmp_path / "repo"
    _mini_notebook(root / "a.ipynb", "x\n")
    registry = _write_registry(tmp_path / "registry", [{
        "name": "factice", "python": "a.ipynb", "rust": "absent.ipynb",
        "measures": [{"id": "x", "reference": "python", "sides": {
            "python": {"cell": 0, "pattern": "(x)", "transform": "text"}}}]}])
    rc, report = crc.run(registry, root)
    assert rc == 1
    assert any("fichier absent" in m for m in report["entries"][0]["missing"])


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
