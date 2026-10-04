#!/usr/bin/env python3
"""guard_test_root : une derive de forme du workflow doit faire echouer la garde (#19026).

Ce que ce fichier garde
-----------------------
`guard_test_root.py` lit les chemins collectes par pytest dans le bloc pytest
de scripts-tests.yml via PYTEST_BLOCK_RE. Avant #19026, un bloc devenu
introuvable (retrait du `-n `, reformatage des continuations) rendait une
liste vide, donc find_violations([]) = [], donc rc=0 sans un seul message :
la garde etait aveugle sans le dire -- un vert silencieux exactement egal a
une garde retiree.

Les deux cas doivent rester distingues :

1. **Aucune correspondance** (forme derivee) : rc=2 + message nommant
   PYTEST_BLOCK_RE, sur stderr.
2. **Correspondance trouvee, aucune violation** : rc=0, comme toujours.

Le controle positif du cas 1 rejoue la derive REELLE sur le workflow du
depot : le vrai scripts-tests.yml prive de son `-n ` (mutation citee par
l'issue, celle qui casse la regex aujourd'hui).
"""

import os
import sys
from pathlib import Path

import pytest

sys.path.insert(0, os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
    "scripts", "ci"))

import guard_test_root as gtr  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
REAL_WORKFLOW = ROOT / ".github" / "workflows" / "scripts-tests.yml"

# Bloc pytest minimal qui matche PYTEST_BLOCK_RE : des lignes de chemins
# terminees par `\`, puis `-n `. Sert de forme canonique aux tests sur arbre
# synthetique (monkeypatch du REPO_ROOT de la garde vers tmp_path).
_WORKFLOW_TEMPLATE = """\
name: scripts-tests
on: [push]
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - run: |
          pytest \\
            {paths} \\
            -n 4 --dist loadscope --tb=short -q
"""


def _write_workflow(root: Path, paths_line: str) -> Path:
    wf_dir = root / ".github" / "workflows"
    wf_dir.mkdir(parents=True, exist_ok=True)
    wf = wf_dir / "scripts-tests.yml"
    wf.write_text(_WORKFLOW_TEMPLATE.format(paths=paths_line), encoding="utf-8")
    return wf


def _make_tree(tmp_path: Path) -> Path:
    """Arbre synthetique : scripts/notebook_tools/tests collecte, racine du module sous scope."""
    nt = tmp_path / "scripts" / "notebook_tools"
    (nt / "tests").mkdir(parents=True, exist_ok=True)
    (nt / "tests" / "test_present.py").write_text("def test_x():\n    pass\n", encoding="utf-8")
    return nt


def _patch_repo(monkeypatch, tmp_path: Path) -> None:
    """Bascule REPO_ROOT ET DEFAULT_WORKFLOW (constante derivee a l'import) vers tmp_path."""
    monkeypatch.setattr(gtr, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(gtr, "DEFAULT_WORKFLOW", tmp_path / ".github" / "workflows" / "scripts-tests.yml")
    monkeypatch.setattr(gtr, "DEFAULT_WORKFLOW", tmp_path / ".github" / "workflows" / "scripts-tests.yml")


def test_real_workflow_still_matches():
    """Controle vivant : sur le workflow REEL d'aujourd'hui, le bloc pytest est trouve."""
    paths = gtr.parse_collected_paths(REAL_WORKFLOW)
    assert paths is not None, (
        "PYTEST_BLOCK_RE ne matche plus scripts-tests.yml : la garde est "
        "aveugle sur le depot tel quel (mettre a jour la regex)"
    )
    assert "scripts/tests" in paths


def test_drifted_real_workflow_fails_loud(tmp_path, capsys, monkeypatch):
    """Cas 1 de l'issue : le vrai workflow prive de son `-n ` => rc=2 + message PYTEST_BLOCK_RE."""
    drifted = REAL_WORKFLOW.read_text(encoding="utf-8").replace(
        " -n 4 --dist loadscope", " --dist loadscope")
    assert " -n " not in drifted, "mutation de test sans effet"
    wf = tmp_path / "drifted.yml"
    wf.write_text(drifted, encoding="utf-8")

    _patch_repo(monkeypatch, tmp_path)
    rc = gtr.main(["--workflow", str(wf)])
    assert rc == 2
    err = capsys.readouterr().err
    assert "PYTEST_BLOCK_RE" in err, f"message sans nom de la regex : {err!r}"
    assert "derivee de la forme du workflow" in err


def test_drifted_workflow_json_reports_error(tmp_path, capsys, monkeypatch):
    """Mode --json : la derive se voit (ok=false + error), pas un ok muet."""
    drifted = _WORKFLOW_TEMPLATE.format(paths="scripts/notebook_tools/tests").replace(
        "-n 4 --dist loadscope", "--dist loadscope")
    wf = tmp_path / "wf.yml"
    wf.write_text(drifted, encoding="utf-8")

    _patch_repo(monkeypatch, tmp_path)
    rc = gtr.main(["--workflow", str(wf), "--json"])
    assert rc == 2
    out = capsys.readouterr().out
    assert '"error": "pytest_block_not_found"' in out
    assert '"ok": false' in out


def test_match_without_violation_is_green(tmp_path, capsys, monkeypatch):
    """Cas 2 de l'issue : bloc trouve, arbre propre => rc=0 (comportement inchangue)."""
    _make_tree(tmp_path)
    wf = _write_workflow(tmp_path, "scripts/notebook_tools/tests")

    _patch_repo(monkeypatch, tmp_path)
    rc = gtr.main(["--workflow", str(wf)])
    assert rc == 0
    assert "OK" in capsys.readouterr().out


def test_violation_still_detected(tmp_path, capsys, monkeypatch):
    """Non-regression du chemin nominal : test_*.py hors chemin collecte => rc=1."""
    nt = _make_tree(tmp_path)
    (nt / "test_racine.py").write_text("def test_y():\n    pass\n", encoding="utf-8")
    wf = _write_workflow(tmp_path, "scripts/notebook_tools/tests")

    _patch_repo(monkeypatch, tmp_path)
    rc = gtr.main(["--workflow", str(wf)])
    assert rc == 1
    out = capsys.readouterr().out
    assert "test_racine.py" in out
