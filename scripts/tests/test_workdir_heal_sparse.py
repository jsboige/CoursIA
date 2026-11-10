"""Tests hors ligne du heal du work dir reutilise (#15387, #24959).

Le bloc HEAL est porté par chaque workflow qui travaille sur le pool de
runners (le work dir est réutilisé d'un job à l'autre) : ces tests le
LIENT depuis les fichiers du dépôt -- ils ne recopient pas le script --,
le verrouillent sur ses propriétés, et le rejouent sur un dépôt local.

Quatre propriétés sont exigées, dans cet ordre :

1. un état sparse **armé** (`core.sparseCheckout` à vrai) purge le work dir,
   parce que le checkout suivant matérialiserait l'arbre entier ;
2. un fichier de **motifs sparse** seul est inerte : il est retiré, le work
   dir est conservé ;
3. un work dir **shallow** est purgé -- c'est le repli historique, et il ne
   s'essaie plus de le réparer sur place ;
4. le graphe incomplet reste le repli.

Ces propriétés ne sont pas des détails d'implémentation : chacune est un
défaut mesuré (voir les commentaires des workflows).

La forme (b) de la review ai-01 du 2026-11-09 a retiré l'`unshallow`
explicite : sans mesure sur un runner, on ne répare pas un work dir
shallow sur place -- on le purge. Le test qui vérifie l'absence de cette
tentative est donc partie du contrat.
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
def test_le_bloc_heal_porte_les_quatre_gardes(workflow):
    script = _heal_script(workflow)
    assert "core.sparseCheckout" in script, "l'etat sparse n'est pas lu"
    assert "sparse-checkout" in script, "le retrait des motifs inertes est absent"
    assert ".git/shallow" in script, "l'etat shallow n'est pas lu"
    assert "rev-list --all --count" in script, "la verification du graphe est absente"
    # L'ordre est une exigence : l'etat sparse casse la materialisation, donc
    # il se traite avant le graphe, et le shallow se purge avant la purge de
    # repli du graphe incomplet.
    assert script.index("core.sparseCheckout") < script.index(".git/shallow")
    assert script.index(".git/shallow") < script.rindex("rm -rf .git")


@pytest.mark.parametrize("workflow", WORKFLOWS)
def test_le_bloc_heal_ne_tente_pas_d_unshallow(workflow):
    # Forme (b) de la review ai-01 : le work dir shallow est purge, il n'est
    # pas repare sur place. Une tentative d'unshallow sans filtre de clone
    # partiel ni timeout rechargerait le graphe entier -- c'est exactement le
    # poste que la P1 de #25510 mesure.
    script = _heal_script(workflow)
    assert "git fetch --unshallow" not in script
    assert "--unshallow" not in script


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
    # Le work dir est **complet** ici : c'est le seul etat ou le retrait des
    # motifs inertes est decide seul. Sur un work dir shallow, la purge
    # shallow passerait avant (c'est le repli historique, cf le test
    # dedicated) -- l'observation des motifs ne serait pas isolee.
    clone = _shallow_clone(tmp_path, origin, name="complet")
    _git(clone, "fetch", "--unshallow", "origin")
    (clone / ".git" / "info").mkdir(parents=True, exist_ok=True)
    (clone / ".git" / "info" / "sparse-checkout").write_text("/scripts/\n", encoding="utf-8")

    result = _run_heal(workflow, clone, tmp_path)

    assert result.returncode == 0, result.stderr
    assert "motifs sparse inertes" in result.stdout
    assert (clone / ".git").is_dir(), "un motif inerte ne doit pas purger le clone"
    assert not (clone / ".git" / "info" / "sparse-checkout").exists()


@pytest.mark.skipif(BASH is None, reason="bash absent de cet hote")
@pytest.mark.parametrize("workflow", WORKFLOWS)
def test_work_dir_shallow_est_purge(workflow, origin, tmp_path):
    # Forme (b) : le work dir shallow n'est pas repare sur place, il est purge
    # et le checkout fera un clone neuf.
    clone = _shallow_clone(tmp_path, origin)

    result = _run_heal(workflow, clone, tmp_path)

    assert result.returncode == 0, result.stderr
    assert "SHALLOW reutilise" in result.stdout
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
