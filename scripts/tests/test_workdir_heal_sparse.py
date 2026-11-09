"""Tests hors ligne du heal du work dir reutilise (#15387, #24959).

Le bloc HEAL est porté par chaque workflow qui travaille sur le pool de
runners (le work dir est réutilisé d'un job à l'autre) : ces tests le
LIENT depuis les fichiers du dépôt -- ils ne recopient pas le script --,
le verrouillent sur ses propriétés, et le rejouent sur un dépôt local.

Trois propriétés sont exigées, dans cet ordre :

1. un état sparse **armé** (`core.sparseCheckout` à vrai) purge le work dir,
   parce que le checkout suivant matérialiserait l'arbre entier ;
2. un **unshallow explicite** est tenté et **vérifié** avant tout clone neuf ;
3. le graphe incomplet reste le repli.

Ces propriétés ne sont pas des détails d'implémentation : chacune est un
défaut mesuré (voir les commentaires des workflows).
"""
from __future__ import annotations

import os
import subprocess
from pathlib import Path

import pytest

from ._bash_resolution import resolve_bash

ROOT = Path(__file__).resolve().parents[2]
WORKFLOWS = (
    "always-on-commenters.yml",
    "always-on-guards.yml",
    "always-on-guards-body.yml",
    "always-on-metadata-guards.yml",
)
STEP_MARKER = '- name: "Purger un work dir reutilise au graphe incomplet (#15387)"'
BASH = resolve_bash()


def _heal_script(workflow: str) -> str:
    """Extrait le corps `run:` de l'étape HEAL du workflow donne."""
    text = (ROOT / ".github" / "workflows" / workflow).read_text(encoding="utf-8")
    lines = text.splitlines()
    start = next((i for i, ln in enumerate(lines) if STEP_MARKER in ln), None)
    assert start is not None, f"{workflow} : etape HEAL introuvable"
    run_at = next(
        (i for i in range(start, len(lines)) if lines[i].strip() == "run: |"),
        None,
    )
    assert run_at is not None, f"{workflow} : bloc `run:` introuvable"
    body: list[str] = []
    for raw in lines[run_at + 1:]:
        if raw.strip() and (len(raw) - len(raw.lstrip())) < 10:
            break
        body.append(raw[10:] if raw.startswith(" " * 10) else raw)
    script = "\n".join(body).rstrip("\n") + "\n"
    assert script.strip(), f"{workflow} : bloc HEAL vide"
    return script


def _git(cwd: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", "-C", str(cwd), *args],
        check=check,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )


@pytest.fixture
def origin(tmp_path):
    """Un dépôt source, son miroir bare, et un clone shallow de référence."""
    source = tmp_path / "source"
    source.mkdir()
    _git(source, "init", "--quiet", "-b", "main")
    _git(source, "config", "user.email", "test@example.invalid")
    _git(source, "config", "user.name", "test")
    for index in range(4):
        (source / "history.txt").write_text(f"commit {index}\n", encoding="utf-8")
        _git(source, "add", "history.txt")
        _git(source, "commit", "--quiet", "-m", f"commit {index}")
    bare = tmp_path / "origin.git"
    _git(tmp_path, "clone", "--quiet", "--bare", str(source), str(bare))
    return bare


def _shallow_clone(tmp_path: Path, bare: Path, name: str = "clone") -> Path:
    clone = tmp_path / name
    subprocess.run(
        ["git", "clone", "--quiet", "--depth=1", "--branch", "main", bare.as_uri(), str(clone)],
        check=True,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert _git(clone, "rev-parse", "--is-shallow-repository").stdout.strip() == "true"
    return clone


def _run_heal(workflow: str, clone: Path, tmp_path: Path) -> subprocess.CompletedProcess:
    script = tmp_path / f"heal_{workflow}.sh"
    script.write_text(_heal_script(workflow), encoding="utf-8")
    env = dict(os.environ, GITHUB_WORKSPACE=str(clone))
    return subprocess.run(
        [BASH, str(script)],
        env=env,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=60,
    )


@pytest.mark.parametrize("workflow", WORKFLOWS)
def test_le_bloc_heal_porte_les_trois_gardes(workflow):
    script = _heal_script(workflow)
    assert "core.sparseCheckout" in script, "l'etat sparse n'est pas lu"
    assert "git fetch --unshallow origin" in script, "l'unshallow explicite est absent"
    assert "rev-list --all --count" in script, "la verification du graphe est absente"
    # L'ordre est une exigence : l'etat sparse casse la materialisation, donc
    # il se traite avant le graphe ; et l'unshallow est tente AVANT la purge
    # de repli (la derniere des purges, celle du graphe incomplet).
    assert script.index("core.sparseCheckout") < script.index("git fetch --unshallow origin")
    assert script.index("git fetch --unshallow origin") < script.rindex("rm -rf .git")


@pytest.mark.skipif(BASH is None, reason="bash absent de cet hote")
@pytest.mark.parametrize("workflow", WORKFLOWS)
def test_sparse_arme_purge_le_work_dir(workflow, origin, tmp_path):
    clone = _shallow_clone(tmp_path, origin)
    _git(clone, "config", "core.sparseCheckout", "true")
    (clone / ".git" / "info").mkdir(parents=True, exist_ok=True)
    (clone / ".git" / "info" / "sparse-checkout").write_text("/scripts/\n", encoding="utf-8")

    result = _run_heal(workflow, clone, tmp_path)

    assert result.returncode == 0, result.stderr
    assert "SPARSE arme" in result.stdout
    assert not (clone / ".git").exists()


@pytest.mark.skipif(BASH is None, reason="bash absent de cet hote")
@pytest.mark.parametrize("workflow", WORKFLOWS)
def test_motifs_sparse_inertes_conservent_le_work_dir(workflow, origin, tmp_path):
    clone = _shallow_clone(tmp_path, origin)
    (clone / ".git" / "info").mkdir(parents=True, exist_ok=True)
    (clone / ".git" / "info" / "sparse-checkout").write_text("/scripts/\n", encoding="utf-8")

    result = _run_heal(workflow, clone, tmp_path)

    assert result.returncode == 0, result.stderr
    assert "motifs sparse inertes" in result.stdout
    assert (clone / ".git").is_dir(), "un motif inerte ne doit pas purger le clone"
    assert not (clone / ".git" / "info" / "sparse-checkout").exists()


@pytest.mark.skipif(BASH is None, reason="bash absent de cet hote")
@pytest.mark.parametrize("workflow", WORKFLOWS)
def test_unshallow_reussi_conserve_le_work_dir(workflow, origin, tmp_path):
    clone = _shallow_clone(tmp_path, origin)

    result = _run_heal(workflow, clone, tmp_path)

    assert result.returncode == 0, result.stderr
    assert "unshallow explicite reussi" in result.stdout
    assert (clone / ".git").is_dir()
    assert not (clone / ".git" / "shallow").exists()
    assert _git(clone, "rev-list", "--all", "--count").stdout.strip() == "4"


@pytest.mark.skipif(BASH is None, reason="bash absent de cet hote")
@pytest.mark.parametrize("workflow", WORKFLOWS)
def test_unshallow_en_echec_purge_le_work_dir(workflow, origin, tmp_path):
    clone = _shallow_clone(tmp_path, origin)
    _git(clone, "remote", "set-url", "origin", (tmp_path / "absent.git").as_uri())

    result = _run_heal(workflow, clone, tmp_path)

    assert result.returncode == 0, result.stderr
    assert "unshallow impossible ou graphe incomplet" in result.stdout
    assert not (clone / ".git").exists()


@pytest.mark.skipif(BASH is None, reason="bash absent de cet hote")
@pytest.mark.parametrize("workflow", WORKFLOWS)
def test_work_dir_complet_est_reutilise(workflow, origin, tmp_path):
    clone = _shallow_clone(tmp_path, origin, name="complete")
    _git(clone, "fetch", "--unshallow", "origin")

    result = _run_heal(workflow, clone, tmp_path)

    assert result.returncode == 0, result.stderr
    assert "work dir complet -- reutilisation" in result.stdout
    assert (clone / ".git").is_dir()
