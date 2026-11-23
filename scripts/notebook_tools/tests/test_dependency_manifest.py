"""Tests unitaires de l'organe manifeste des dependances (#27544).

On teste les fonctions pures (bornes, compatibilite, normalisation) et un
scenario de bout en bout sur un depot git temporaire : deux series, un
conflit de versions, un carnet GPU et une contrainte ``requires-python``.
"""

import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import dependency_manifest as dm


def test_norm_name_unifies_separators():
    assert dm._norm_name("Z3_Solver") == "z3-solver"
    assert dm._norm_name("Jupyter.Kernel") == "jupyter-kernel"


def test_specifier_bounds_extracts_operators():
    bounds = dm._specifier_bounds(">=1.24,<2.5")
    assert bounds["lower"] == "1.24"
    assert bounds["upper"] == "2.5"
    assert bounds["exact"] == ""


def test_specifier_bounds_exact_pin():
    bounds = dm._specifier_bounds("==2.24.0")
    assert bounds["exact"] == "2.24.0"


def test_norm_ver_collapses_equivalent_spellings():
    assert dm._norm_ver("1.0") == dm._norm_ver("1.0.0")
    assert dm._norm_ver("0.29") == dm._norm_ver("0.29.0")
    assert dm._norm_ver("2.0") != dm._norm_ver("2.1")


def test_specifiers_compatible_detects_empty_intersection():
    bornes = dm._specifier_bounds(">=2.0,<2.12")
    pin = dm._specifier_bounds("==2.14.0")
    assert not dm._specifiers_compatible(bornes, pin)


def test_specifiers_compatible_accepts_overlapping_ranges():
    lower = dm._specifier_bounds(">=1.11,<1.19")
    pin = dm._specifier_bounds("==1.14.1")
    assert dm._specifiers_compatible(lower, pin)


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _notebook(kernel: str, language: str, source: str) -> str:
    return json.dumps(
        {
            "cells": [
                {
                    "cell_type": "code",
                    "execution_count": 1,
                    "outputs": [],
                    "source": source,
                }
            ],
            "metadata": {"kernelspec": {"name": kernel, "language": language}},
        }
    )


@pytest.fixture()
def fake_repo(tmp_path: Path) -> Path:
    """Un depot git minimal : deux series, un conflit, un carnet GPU."""
    repo = tmp_path / "repo"
    repo.mkdir()
    (repo / "scripts/notebook_tools").mkdir(parents=True)
    _write(
        repo / dm.POLICY_RELPATH,
        (Path(dm.__file__).resolve().parent / "dependency_manifest_policy.json")
        .read_text(encoding="utf-8"),
    )
    _write(repo / "MyIA.AI.Notebooks/Search/requirements.txt", "numpy>=1.24\n")
    _write(
        repo / "MyIA.AI.Notebooks/Probas/requirements.txt",
        "numpy>=1.21,<2.0\nscikit-learn==1.5.2\ntorch==2.14.0\n",
    )
    _write(
        repo / "MyIA.AI.Notebooks/Search/A-01.ipynb",
        _notebook("python3", "python", "import numpy\n"),
    )
    _write(
        repo / "MyIA.AI.Notebooks/Probas/A-02.ipynb",
        _notebook("python3", "python", "import numpy\nimport torch\n"),
    )
    _write(
        repo / "MyIA.AI.Notebooks/Probas/A-03.ipynb",
        _notebook("python3", "python", "x = torch.zeros(3).cuda()\n"),
    )
    _write(
        repo / "MyIA.AI.Notebooks/IIT/ICT-Series/pyproject.toml",
        "[project]\nname = \"ict\"\nrequires-python = \">=3.9,<3.10\"\n",
    )
    _write(
        repo / "MyIA.AI.Notebooks/IIT/ICT-Series/A-04.ipynb",
        _notebook("python3", "python", "import torch\nprint('ict')\n"),
    )
    subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True)
    subprocess.run(
        ["git", "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "init"],
        cwd=repo,
        check=True,
    )
    return repo


def test_end_to_end_conflicts_and_verdicts(fake_repo: Path):
    manifest = dm.build_manifest(fake_repo)

    packages = {conflict["package"] for conflict in manifest["conflicts"]}
    assert "numpy" in packages, "le conflit numpy doit etre nomme"
    numpy_conflict = next(
        conflict for conflict in manifest["conflicts"] if conflict["package"] == "numpy"
    )
    assert numpy_conflict["class"] == "specifier_divergent"
    assert numpy_conflict["resolution"]["version"]

    groups = {group["group"]: group for group in manifest["groups"]}
    probas = groups["MyIA.AI.Notebooks/Probas"]
    assert probas["verdict"] == "exclu"
    assert any(motif["policy"] == "gpu" for motif in probas["motifs"])
    assert any(motif["policy"] == "heavy_distributions" for motif in probas["motifs"])

    ict = groups["MyIA.AI.Notebooks/IIT/ICT-Series"]
    assert ict["requires_python"] == ">=3.9,<3.10"
    assert any("conflit de versions d'interpreteur" in m["text"] for m in ict["motifs"])

    consolidated = {
        record["package"]: record for record in manifest["consolidated_manifest"]
    }
    assert "numpy" in consolidated
    assert consolidated["numpy"]["conflict"] is True


def test_end_to_end_reports_declaration_gap(fake_repo: Path):
    manifest = dm.build_manifest(fake_repo)
    groups = {group["group"]: group for group in manifest["groups"]}
    # torch est importe par un carnet d'IIT mais declare par aucun fichier de
    # dependances de la serie : lacune mesuree.
    assert "torch" in groups["MyIA.AI.Notebooks/IIT/ICT-Series"]["gaps"]


def test_render_markdown_mentions_origine_des_motifs(fake_repo: Path):
    manifest = dm.build_manifest(fake_repo)
    markdown = dm.render_markdown(manifest)
    assert "Origine des motifs" in markdown
    assert "mesure" in markdown and "declaration" in markdown
