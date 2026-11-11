"""Tests du comptage de classe du ratchet #24090."""

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_markdown_cell_schema_ratchet as ratchet


def notebook_bytes(cells):
    return json.dumps({"cells": cells}).encode("utf-8")


def markdown_cell(**extra):
    return {"cell_type": "markdown", "source": ["texte"], **extra}


def test_counts_only_markdown_execution_count_and_outputs():
    data = notebook_bytes([
        markdown_cell(execution_count=3),
        markdown_cell(outputs=[]),
        markdown_cell(metadata={"execution_count": 3}),
        {"cell_type": "code", "execution_count": 1, "outputs": []},
    ])

    defects = ratchet.defects_from_bytes(data, "temoin.ipynb")

    assert [(defect.index, defect.keys) for defect in defects] == [
        (0, ("execution_count",)), (1, ("outputs",)),
    ]


def test_clean_markdown_cell_is_a_negative_control():
    data = notebook_bytes([markdown_cell(), {"cell_type": "code", "outputs": []}])

    assert ratchet.defects_from_bytes(data, "temoin-propre.ipynb") == []


def test_git_base_legacy_count_is_tolerated_but_growth_fails(tmp_path, monkeypatch, capsys):
    monkeypatch.setattr(ratchet, "REPO_ROOT", tmp_path)
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.invalid"],
                   cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Ratchet test"],
                   cwd=tmp_path, check=True)
    path = "MyIA.AI.Notebooks/temoin.ipynb"
    notebook_path = tmp_path / path
    notebook_path.parent.mkdir(parents=True)
    notebook_path.write_bytes(notebook_bytes([markdown_cell(outputs=[])]))
    subprocess.run(["git", "add", path], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "base avec dette historique"],
                   cwd=tmp_path, check=True)
    base = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=tmp_path,
                                   text=True).strip()

    # Une cellule fautive preexistante au meme chemin ne bloque pas une PR.
    assert ratchet.check(base, [path]) == 0
    assert "1 -> 1" in capsys.readouterr().out

    # Une seconde cellule de la classe precise fait echouer le ratchet et nomme
    # le chemin ainsi que les indices de cellules concernes.
    notebook_path.write_bytes(notebook_bytes([
        markdown_cell(outputs=[]), markdown_cell(execution_count=2),
    ]))
    assert ratchet.check(base, [path]) == 1
    report = capsys.readouterr().out
    assert "temoin.ipynb" in report
    assert "1 -> 2" in report
    assert "cellules fautives: 0 (outputs), 1 (execution_count)" in report

    # Le meme mauvais HEAD ne doit pas etre lu comme une suppression quand
    # le checkout sparse n'a pas materialise le fichier suivi.
    subprocess.run(["git", "add", path], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "regression commitee"],
                   cwd=tmp_path, check=True)
    notebook_path.unlink()
    assert ratchet.check(base, [path]) == 1
    assert "1 -> 2" in capsys.readouterr().out

    # Une vraie suppression commitee, elle, reste acceptee.
    subprocess.run(["git", "rm", "--cached", path], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "suppression du carnet"],
                   cwd=tmp_path, check=True)
    assert ratchet.check(base, [path]) == 0
    assert "supprime dans HEAD" in capsys.readouterr().out
