"""Tests du DIAGNOSTIC de fragmentation du Scan (#4363).

Le Scan de `setup_shared_mathlib.ps1` groupait les lacs par TOUT le graphe de
dependances transitives et affichait ensuite un simple "[isole]" pour un groupe
d'un seul membre. Ce rapport ne disait pas POURQUOI le groupe etait isole, donc
l'economie perdue restait invisible et la decision "faut-il aligner les manifests
?" (#2611 etape 2) ne se prenait pas.

Le diagnostic ajoute un regroupement secondaire par (toolchain, revision
mathlib) -- l'artefact reellement partage -- et nomme l'ecart entre groupes :

- DRIFT                : meme jeu de dependances, une revision diverge ;
- DEPENDANCES REELLES  : les jeux de dependances different (une dependance
                         locale "path" absente d'un groupe, une dependance
                         externe "git" absente de l'autre) ;
- ECART MIXTE          : les deux a la fois.

Les tests executent le VRAI script en mode Scan sur une fixture git minimale
(4 projets fictifs) et verifient le rapport. Un test de motif se valide par ses
faux negatifs : le controle negatif (tous les projets identiques) verifie que le
diagnostic ne se déclenche PAS quand il n'y a rien a signaler.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

# pwsh (script #Requires -Version 7.0) : les runners Linux sautent.
requires_pwsh = pytest.mark.skipif(
    shutil.which("pwsh") is None,
    reason="pwsh requis pour executer le script Scan (#4363)",
)

REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "lean" / "setup_shared_mathlib.ps1"

MATHLIB_REV = "0df444a360eaa60ab8c11dca51a86af692955474"
BATTERIES_R1 = "1111111111111111111111111111111111111111"
BATTERIES_R2 = "2222222222222222222222222222222222222222"


def _pkg(name: str, rev: str, url: str = "https://example.invalid/pkg.git",
         pkg_type: str = "git") -> dict:
    return {
        "url": url,
        "type": pkg_type,
        "subDir": None,
        "scope": "",
        "rev": rev,
        "name": name,
        "manifestFile": "lake-manifest.json",
        "inputRev": rev,
        "inherited": False,
        "configFile": "lakefile.lean",
    }


def _make_project(root: Path, name: str, packages: list[dict],
                  toolchain: str = "leanprover/lean4:v4.33.1") -> Path:
    proj = root / name
    proj.mkdir(parents=True, exist_ok=True)
    (proj / "lake-manifest.json").write_text(
        json.dumps({"version": "1.2.0", "packages": packages}), encoding="utf-8"
    )
    (proj / "lean-toolchain").write_text(toolchain + "\n", encoding="utf-8")
    return proj


def _run_scan(root: Path) -> str:
    proc = subprocess.run(
        ["pwsh", "-NoProfile", "-NonInteractive", "-File", str(SCRIPT), "-Mode", "Scan"],
        cwd=root, capture_output=True, text=True, encoding="utf-8",
        errors="replace", timeout=300,
    )
    assert proc.returncode == 0, f"Scan en echec:\n{proc.stdout}\n{proc.stderr}"
    return proc.stdout


@pytest.fixture()
def fragmented_repo(tmp_path: Path) -> Path:
    """5 projets, 4 groupes de manifests, une MEME revision mathlib.

    - projA / projB : manifests identiques -> groupe MUTUALISABLE (2 membres).
    - projC         : + dependance LOCALE (path) -> groupe distinct.
    - projD         : batteries a une autre revision (git) -> groupe distinct.
    - projE         : + dependance EXTERNE (git) propre -> groupe distinct.
    """
    root = tmp_path / "repo"
    root.mkdir()
    subprocess.run(["git", "init", "-q"], cwd=root, check=True,
                   capture_output=True, text=True, encoding="utf-8", errors="replace")

    base = [_pkg("mathlib", MATHLIB_REV, "https://github.com/leanprover-community/mathlib4.git"),
            _pkg("batteries", BATTERIES_R1)]
    _make_project(root, "projA", base)
    _make_project(root, "projB", base)
    _make_project(root, "projC", base + [_pkg("sibling_lean", "", pkg_type="path")])
    _make_project(root, "projD", [
        _pkg("mathlib", MATHLIB_REV, "https://github.com/leanprover-community/mathlib4.git"),
        _pkg("batteries", BATTERIES_R2),
    ])
    _make_project(root, "projE", base + [_pkg("extra_git", BATTERIES_R1)])
    return root


@requires_pwsh
def test_scan_names_the_fragments_and_the_divergent_dependencies(fragmented_repo: Path) -> None:
    out = _run_scan(fragmented_repo)

    assert "Diagnostic : revision mathlib partagee par plusieurs groupes" in out

    # La revision mathlib est portee par 4 groupes de manifests distincts.
    assert "4 groupes de manifests distincts" in out

    # projA / projB restent un groupe MUTUALISABLE : le diagnostic n'y touche pas.
    assert "MUTUALISABLE" in out
    assert "projA" in out and "projB" in out

    # L'ecart avec projC est nomme, et la dependance LOCALE (path) est
    # distinguee d'une dependance externe (git).
    assert "DEPENDANCES REELLES" in out
    assert "sibling_lean" in out
    assert "dependances LOCALES (path) absentes du groupe" in out
    # projE porte une dependance externe absente du groupe des projA/projB.
    assert "extra_git" in out
    assert "dependances EXTERNES absentes du groupe" in out

    # L'ecart avec projD est un DRIFT de revision, nomme avec ses revs.
    assert "DRIFT" in out
    assert "batteries" in out
    assert BATTERIES_R1[:8] in out and BATTERIES_R2[:8] in out


@requires_pwsh
def test_scan_does_not_report_fragmentation_when_groups_are_identical(tmp_path: Path) -> None:
    """Controle NEGATIF : sans divergence, le diagnostic ne doit rien signaler."""
    root = tmp_path / "repo"
    root.mkdir()
    subprocess.run(["git", "init", "-q"], cwd=root, check=True,
                   capture_output=True, text=True, encoding="utf-8", errors="replace")

    base = [_pkg("mathlib", MATHLIB_REV, "https://github.com/leanprover-community/mathlib4.git"),
            _pkg("batteries", BATTERIES_R1)]
    for name in ("projA", "projB", "projC"):
        _make_project(root, name, base)

    out = _run_scan(root)
    assert "MUTUALISABLE" in out
    assert "Diagnostic : revision mathlib partagee par plusieurs groupes" not in out
    assert "DEPENDANCES REELLES" not in out
    assert "DRIFT" not in out
