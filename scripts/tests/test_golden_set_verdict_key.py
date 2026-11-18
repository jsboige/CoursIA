#!/usr/bin/env python3
"""Tests de la cle de verdict du golden-set (#22468, tranche 1).

La cle est ce qui autorise a REUTILISER un verdict vert au lieu de rejouer la
suite : elle doit donc bouger des qu'une des entrees qui influent sur le
verdict bouge, et seulement la. Ces tests pinnent les deux moities du
contrat -- la stabilite (meme arbre, meme cle) et la sensibilite (un octet de
carnet, une dependance ou une version de Python differents donnent une autre
cle), plus la transparence sur un carnet declare mais absent.

Run: python -m pytest scripts/tests/test_golden_set_verdict_key.py
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import golden_set_verdict_key as gk  # noqa: E402


def _fixture(tmp_path: Path):
    """Arbre minimal : manifeste, lockfile, implementation, workflow et carnets."""
    (tmp_path / "nb").mkdir()
    (tmp_path / "nb" / "a.ipynb").write_text('{"cells": [], "v": 1}', encoding="utf-8")
    (tmp_path / "nb" / "b.ipynb").write_text('{"cells": [], "v": 2}', encoding="utf-8")
    manifest = tmp_path / "golden_set.yml"
    manifest.write_text(
        "meta:\n  python_pin: '3.12'\nnotebooks:\n"
        "  - path: nb/a.ipynb\n    series: A\n"
        "  - path: nb/b.ipynb\n    series: B\n",
        encoding="utf-8",
    )
    lockfile = tmp_path / "golden_set.lock.txt"
    lockfile.write_text("numpy==2.2.6\n", encoding="utf-8")
    implementation = tmp_path / "notebook_tools.py"
    implementation.write_text("# executeur\n", encoding="utf-8")
    workflow = tmp_path / "workflow.yml"
    workflow.write_text("run: python notebook_tools.py\n", encoding="utf-8")
    return manifest, lockfile, implementation, workflow


def _key(tmp_path, manifest, lockfile, implementation, workflow, python_version="3.12"):
    return gk.compute_key(
        tmp_path, manifest, lockfile, implementation, workflow, python_version
    )


def test_manifest_lists_every_declared_notebook(tmp_path):
    manifest, _, _, _ = _fixture(tmp_path)
    assert gk.manifest_notebooks(manifest.read_text(encoding="utf-8")) == [
        "nb/a.ipynb",
        "nb/b.ipynb",
    ]


def test_key_is_stable_for_an_identical_tree(tmp_path):
    manifest, lockfile, implementation, workflow = _fixture(tmp_path)
    first = _key(tmp_path, manifest, lockfile, implementation, workflow)
    second = _key(tmp_path, manifest, lockfile, implementation, workflow)
    assert first["key"] == second["key"]
    assert first["components"]["notebook_count"] == 2
    assert first["missing_notebooks"] == []


def test_key_moves_when_a_notebook_byte_changes(tmp_path):
    manifest, lockfile, implementation, workflow = _fixture(tmp_path)
    before = _key(tmp_path, manifest, lockfile, implementation, workflow)["key"]
    (tmp_path / "nb" / "b.ipynb").write_text('{"cells": [], "v": 3}', encoding="utf-8")
    after = _key(tmp_path, manifest, lockfile, implementation, workflow)["key"]
    assert after != before


def test_key_moves_when_the_lockfile_changes(tmp_path):
    manifest, lockfile, implementation, workflow = _fixture(tmp_path)
    before = _key(tmp_path, manifest, lockfile, implementation, workflow)["key"]
    lockfile.write_text("numpy==2.4.2\n", encoding="utf-8")
    assert _key(tmp_path, manifest, lockfile, implementation, workflow)["key"] != before


def test_key_moves_when_the_executor_changes(tmp_path):
    manifest, lockfile, implementation, workflow = _fixture(tmp_path)
    before = _key(tmp_path, manifest, lockfile, implementation, workflow)["key"]
    implementation.write_text("# executeur, corrige\n", encoding="utf-8")
    assert _key(tmp_path, manifest, lockfile, implementation, workflow)["key"] != before


def test_key_moves_when_the_python_version_changes(tmp_path):
    manifest, lockfile, implementation, workflow = _fixture(tmp_path)
    a = _key(tmp_path, manifest, lockfile, implementation, workflow, "3.12")["key"]
    b = _key(tmp_path, manifest, lockfile, implementation, workflow, "3.11")["key"]
    assert a != b


def test_key_moves_when_the_workflow_changes(tmp_path):
    """Le contrat appelant fait partie de l'empreinte du verdict réutilisé."""
    manifest, lockfile, implementation, workflow = _fixture(tmp_path)
    before = _key(tmp_path, manifest, lockfile, implementation, workflow)
    workflow.write_text("run: python notebook_tools.py --strict\n", encoding="utf-8")
    after = _key(tmp_path, manifest, lockfile, implementation, workflow)
    assert after["key"] != before["key"]
    assert (
        after["components"]["workflow_sha256"]
        != before["components"]["workflow_sha256"]
    )


def test_key_ignores_files_outside_the_verdict_inputs(tmp_path):
    """Un fichier sans lien avec le gate ne doit pas vider le cache du verdict."""
    manifest, lockfile, implementation, workflow = _fixture(tmp_path)
    before = _key(tmp_path, manifest, lockfile, implementation, workflow)["key"]
    (tmp_path / "unrelated.txt").write_text("documentation\n", encoding="utf-8")
    assert _key(tmp_path, manifest, lockfile, implementation, workflow)["key"] == before


def test_workflow_passes_its_own_path_to_the_key_and_rebuilds_main_cache():
    """Le caller explicite le workflow empreinté et relance le producteur main."""
    root = Path(__file__).resolve().parents[2]
    workflow = (root / ".github/workflows/notebook-execution-required.yml").read_text(
        encoding="utf-8"
    )
    assert "--workflow .github/workflows/notebook-execution-required.yml" in workflow
    push_paths = workflow.split("  push:\n", 1)[1].split("  workflow_dispatch:", 1)[0]
    assert "- '.github/workflows/notebook-execution-required.yml'" in push_paths


def test_missing_notebook_is_reported_not_silently_dropped(tmp_path):
    """Un carnet declare mais absent ne doit pas rendre une cle « verte ».

    Il est nomme : la cle reste calculable (le job la consomme avant tout
    acces au carnet) mais l'appelant voit la liste, et le workflow la remonte
    en avertissement.
    """
    manifest, lockfile, implementation, workflow = _fixture(tmp_path)
    (tmp_path / "nb" / "b.ipynb").unlink()
    result = _key(tmp_path, manifest, lockfile, implementation, workflow)
    assert result["missing_notebooks"] == ["nb/b.ipynb"]
    assert result["components"]["notebook_count"] == 1
