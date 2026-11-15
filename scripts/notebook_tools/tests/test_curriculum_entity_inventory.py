"""Contrat de l'inventaire et limites des localisateurs."""
import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from curriculum_entity_inventory import inventory


def write_nb(tmp_path, cells):
    path = tmp_path / "carnet.ipynb"
    path.write_text(json.dumps({"cells": cells}), encoding="utf-8")
    return path


def cell(kind, source, **extra):
    return {"cell_type": kind, "source": source.splitlines(keepends=True), "metadata": {}, **extra}


def test_grouped_exercises_and_credited_examples(tmp_path):
    path = write_nb(tmp_path, [
        cell("markdown", "## Exercices\n### Exercice 1\n### Exercice 2\n", id="groupe"),
        cell("code", "# Exercice 1\npass\n"),
        cell("markdown", "### Exemple guidé (crédité #123)\n", id="exemple"),
        cell("code", "# Exercice 3\npass\n"),
        cell("markdown", "### Exemple sans crédit\n"),
    ])
    result = inventory(path, "serie/carnet.ipynb")
    assert result["notebook"] == "serie/carnet.ipynb"
    assert result["exercises"] == [{"cell_index": 0, "cell_id": "groupe", "detected_by": "markdown_header", "count": 2}]
    assert result["credited_examples"] == [{"cell_index": 2, "cell_id": "exemple"}]
    assert result["schema_version"] == 1


def test_missing_ids_and_empty_carnet(tmp_path):
    path = write_nb(tmp_path, [cell("code", "# Exercice 1\npass\n")])
    result = inventory(path, "x.ipynb")
    assert result["exercises"][0]["cell_id"] is None
    path = write_nb(tmp_path, [])
    assert inventory(path, "x.ipynb")["exercises"] == []


def test_invalid_input_fails(tmp_path):
    path = tmp_path / "broken.ipynb"
    path.write_text("{", encoding="utf-8")
    with pytest.raises(json.JSONDecodeError):
        inventory(path, "broken.ipynb")
    with pytest.raises(FileNotFoundError):
        inventory(tmp_path / "absent.ipynb", "absent.ipynb")


@pytest.mark.parametrize("entrypoint", [
    ["-m", "scripts.notebook_tools.curriculum_entity_inventory"],
    ["scripts/notebook_tools/curriculum_entity_inventory.py"],
])
def test_cli_entrypoints_from_repo_root(tmp_path, entrypoint):
    path = write_nb(tmp_path, [cell("code", "# Exercice 1\npass\n")])
    repo = Path(__file__).resolve().parents[3]
    run = subprocess.run(
        [sys.executable, *entrypoint, str(path)], cwd=repo,
        check=True, capture_output=True, text=True,
    )
    result = json.loads(run.stdout)
    assert result["notebook"] == path.as_posix()
    assert sum(item["count"] for item in result["exercises"]) == 1
