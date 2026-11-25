"""Tests for scripts/notebook_tools/check_twin_execution_heritage.py (#27992).

Ce que ce fichier pinle
------------------------
1. **Le predicat** -- deux carnets d'une meme famille qui portent un bloc de
   metadata d'execution **identique** sont signales (heritage d'execution) ;
   deux carnets executes separement ne le sont pas ; deux carnets **sans**
   metadata ne le sont pas non plus (c'est le faux positif que l'artefact
   « metadonnees vides » produisait : deux carnets jamais executes se
   ressemblent, sans que rien n'ait ete copie).
2. **Le mode diff** -- seules les familles touchees par la PR sont examinees.
3. **Le compte** -- le finding nomme le nombre de cellules heritees et le
   nombre de cellules dont les sorties sont identiques a celles du jumeau.

Ce que ce fichier ne pinle pas
-------------------------------
Le nombre de familles du depot : le corpus evolue. Ce qui est pinle, c'est
l'absence de faux positif et la capacite du predicat a tomber.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_twin_execution_heritage as organ  # noqa: E402


def _cell(source: str = "print(1)", metadata: dict | None = None) -> dict:
    return {
        "cell_type": "code",
        "execution_count": 1,
        "metadata": metadata or {},
        "outputs": [],
        "source": [source],
    }


def _notebook(cells: list[dict]) -> dict:
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _block(stamp: str) -> dict:
    return {
        "execution": {
            "iopub.execute_input": f"2026-11-22T06:15:56.{stamp}Z",
            "iopub.status.idle": f"2026-11-22T06:15:57.{stamp}Z",
        },
        "papermill": {
            "start_time": f"2026-11-22T06:15:56.{stamp}+00:00",
            "end_time": f"2026-11-22T06:15:57.{stamp}+00:00",
            "duration": 1.0,
            "exception": False,
            "status": "completed",
        },
    }


def _write(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False), encoding="utf-8")


def _family(root: Path, name: str, python_cells: list[dict], csharp_cells: list[dict]) -> None:
    registry = root / "scripts/notebook_tools/twin_pairs.d"
    registry.mkdir(parents=True, exist_ok=True)
    (registry / f"{name}.yaml").write_text(
        "- name: {name}\n"
        "  family: Test\n"
        "  python: notebooks/{name}-Python.ipynb\n"
        "  csharp: notebooks/{name}-CSharp.ipynb\n".format(name=name),
        encoding="utf-8",
    )
    _write(root / "notebooks" / f"{name}-Python.ipynb", _notebook(python_cells))
    _write(root / "notebooks" / f"{name}-CSharp.ipynb", _notebook(csharp_cells))


def test_heritage_detecte(tmp_path: Path) -> None:
    """Un carnet qui herite les blocs d'execution de son jumeau est signale."""
    _family(
        tmp_path, "demo",
        [_cell(metadata=_block("100"))],
        [_cell(metadata=_block("100"))],
    )
    findings = organ.examine(tmp_path, organ.families(tmp_path)[0])
    assert len(findings) == 1
    assert findings[0]["blocs_partages"] == 1
    assert findings[0]["cellules_heritees"] == 1


def test_executions_separees_propre(tmp_path: Path) -> None:
    """Deux carnets executes separement ne partagent aucun bloc."""
    _family(
        tmp_path, "demo",
        [_cell(metadata=_block("100"))],
        [_cell(metadata=_block("200"))],
    )
    assert organ.examine(tmp_path, organ.families(tmp_path)[0]) == []


def test_sans_metadata_propre(tmp_path: Path) -> None:
    """Deux carnets sans metadata d'execution ne sont pas signales."""
    _family(tmp_path, "demo", [_cell()], [_cell()])
    assert organ.examine(tmp_path, organ.families(tmp_path)[0]) == []


def test_membre_absent_ignore(tmp_path: Path) -> None:
    """Une famille dont un membre est absent de l'arbre ne produit aucun finding."""
    _family(tmp_path, "demo", [_cell(metadata=_block("100"))], [_cell(metadata=_block("100"))])
    (tmp_path / "notebooks/demo-CSharp.ipynb").unlink()
    findings = []
    for family in organ.families(tmp_path):
        findings.extend(organ.examine(tmp_path, family))
    assert findings == []


def test_cellules_memes_sorties_comptees(tmp_path: Path) -> None:
    """Le finding compte les cellules dont les sorties sont identiques."""
    cell_a = _cell(metadata=_block("100"))
    cell_a["outputs"] = [{"output_type": "stream", "text": ["42\n"]}]
    cell_b = _cell(metadata=_block("100"))
    cell_b["outputs"] = [{"output_type": "stream", "text": ["42\n"]}]
    _family(tmp_path, "demo", [cell_a], [cell_b])
    findings = organ.examine(tmp_path, organ.families(tmp_path)[0])
    assert findings[0]["cellules_memes_sorties"] == 1


def test_mode_diff_n_examine_que_les_familles_touchees(tmp_path: Path) -> None:
    """--diff limite l'examen aux familles touchees par la PR."""
    _family(tmp_path, "touchee", [_cell(metadata=_block("100"))], [_cell(metadata=_block("100"))])
    _family(tmp_path, "intacte", [_cell(metadata=_block("300"))], [_cell(metadata=_block("400"))])

    def git(*args: str) -> None:
        subprocess.run(["git", "-C", str(tmp_path), *args], check=True, capture_output=True)

    git("init", "-q")
    git("config", "user.email", "test@example.invalid")
    git("config", "user.name", "test")
    git("add", "-A")
    git("commit", "-q", "-m", "base")
    base = subprocess.run(["git", "-C", str(tmp_path), "rev-parse", "HEAD"],
                          check=True, capture_output=True, text=True,
                          encoding="utf-8", errors="replace").stdout.strip()
    _write(tmp_path / "notebooks/touchee-CSharp.ipynb",
           _notebook([_cell(source="print(2)", metadata=_block("100"))]))
    git("add", "-A")
    git("commit", "-q", "-m", "pr")
    head = subprocess.run(["git", "-C", str(tmp_path), "rev-parse", "HEAD"],
                          check=True, capture_output=True, text=True,
                          encoding="utf-8", errors="replace").stdout.strip()

    touched = organ.touched_families(tmp_path, base, head)
    assert [family["famille"] for family in touched] == ["touchee.yaml"]
    findings = []
    for family in touched:
        findings.extend(organ.examine(tmp_path, family))
    assert len(findings) == 1


def test_code_de_sortie_incident(tmp_path: Path) -> None:
    """Un registre illisible est un incident (2), jamais un vert muet."""
    registry = tmp_path / "scripts/notebook_tools/twin_pairs.d"
    registry.mkdir(parents=True, exist_ok=True)
    (registry / "casse.yaml").write_text("- name: [non: valide\n", encoding="utf-8")
    code = organ.main(["--census", "--repo-root", str(tmp_path), "--json"])
    assert code == 2
