# -*- coding: utf-8 -*-
"""Tests du garde anti-drift du README grothendieck_lean (#17512).

Le defaut fondateur : le garde mesurait ``origin/main`` au lieu de la tete
testee, fabriquant un decalage d'une unite sur toute PR ajoutant un module
(l'auteur alignait la prose sur le compte de main pour faire taire l'organe,
puis main heritait du sous-compte apres merge). Les controles ci-dessous
prouvent que la tete est l'arbre de mesure par defaut, que le scenario
fondateur rougit desormais, et que ``--ref`` garde la comparaison amont
explicite disponible.
"""
import json
import subprocess
import sys

from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "lean"))

import check_grothendieck_readme as mod  # noqa: E402


TOOLCHAIN = "leanprover/lean4:v4.33.0"


def _commit_all(repo: Path, msg: str) -> str:
    subprocess.run(["git", "add", "-A"], cwd=repo, check=True,
                   capture_output=True, encoding="utf-8")
    proc = subprocess.run(
        ["git", "-c", "user.email=t@t", "-c", "user.name=t",
         "commit", "-q", "-m", msg],
        cwd=repo, check=True, capture_output=True, encoding="utf-8")
    assert proc.returncode == 0
    sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, check=True,
                         capture_output=True, encoding="utf-8").stdout.strip()
    return sha


def _write_lake(repo: Path, n_modules: int, claimed: int) -> None:
    """Ecrit un lake minimal : umbrella + n_modules paires FR/EN + READMEs.

    ``claimed`` controle le compte annonce dans la prose (independant du
    disque — c'est le parametre qui fabrique ou non le drift).
    """
    lake = repo / "lake"
    ns = lake / "Grok"
    ns.mkdir(parents=True, exist_ok=True)
    (lake / "Grok.lean").write_text("import Grok.Foo1\n", encoding="utf-8")
    (lake / "lean-toolchain").write_text(TOOLCHAIN + "\n", encoding="utf-8")
    rows = []
    for i in range(1, n_modules + 1):
        (ns / f"Foo{i}.lean").write_text(f"-- Foo{i}\n", encoding="utf-8")
        (ns / f"Foo{i}_en.lean").write_text(f"-- Foo{i} en\n", encoding="utf-8")
        rows.append(f"| {i} | `Grok/Foo{i}.lean` | `Foo{i}_en.lean` | ok |")
    table = "\n".join(rows)
    for name in ("README.md", "README.en.md"):
        (lake / name).write_text(
            f"Le lake expose **{claimed} modules leaf** ({claimed} paires FR/EN),"
            f" toolchain `{TOOLCHAIN}`.\n\n"
            f"| # | FR | EN | etat |\n|---|---|---|---|\n{table}\n",
            encoding="utf-8")


def _make_repo(tmp_path: Path, n_modules: int, claimed: int) -> Path:
    repo = tmp_path / "repo"
    repo.mkdir()
    subprocess.run(["git", "init", "-q"], cwd=repo, check=True,
                   capture_output=True, encoding="utf-8")
    _write_lake(repo, n_modules, claimed)
    _commit_all(repo, "fixture lake")
    return repo


def test_head_is_the_default_measured_tree(tmp_path, monkeypatch):
    """Defaut = tete testee : prose alignee sur la tete, aucun drift bloquant."""
    repo = _make_repo(tmp_path, n_modules=5, claimed=5)
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    rpt = mod.check_lake(repo / "lake")
    assert rpt.ref == "HEAD"
    assert rpt.leaf_count_disk_fr == 5
    assert rpt.leaf_count_disk_en == 5
    assert rpt.leaf_count_umbrella == 1
    assert not rpt.blocking


def test_negative_control_added_module_stale_prose_blocks(tmp_path, monkeypatch):
    """Le scenario fondateur de #17512 rougit : module ajoute, prose restee
    au compte de main (l'ancienne mesure origin/main laissait passer vert)."""
    repo = _make_repo(tmp_path, n_modules=5, claimed=5)
    # La PR : ajoute Foo6 (+ table), laisse la prose a 5 (compte de "main").
    _write_lake(repo, n_modules=6, claimed=5)
    _commit_all(repo, "add Foo6, prose stale")
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    rpt = mod.check_lake(repo / "lake")
    under = [d for d in rpt.drifts if d.kind == "UNDERCOUNT"]
    assert under, f"UNDERCOUNT attendu, drifts = {[d.kind for d in rpt.drifts]}"
    assert under[0].expected == 6
    assert under[0].actual == 5
    assert rpt.blocking


def test_ref_option_measures_the_named_tree(tmp_path, monkeypatch):
    """--ref garde la comparaison amont : mesure au premier commit, la prose
    a 5 correspond au disque d'alors (5) — pas de UNDERCOUNT."""
    repo = _make_repo(tmp_path, n_modules=5, claimed=5)
    first_sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo,
                               check=True, capture_output=True,
                               encoding="utf-8").stdout.strip()
    _write_lake(repo, n_modules=6, claimed=5)
    _commit_all(repo, "add Foo6, prose stale")
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    rpt = mod.check_lake(repo / "lake", ref=first_sha)
    assert rpt.ref == first_sha
    assert rpt.leaf_count_disk_fr == 5
    assert not [d for d in rpt.drifts if d.kind == "UNDERCOUNT"]
    # La table lue (working tree, 6 lignes) depasse l'arbre mesure (5) :
    # ORPHAN advisory honnete, non bloquant.
    kinds = {d.kind for d in rpt.drifts}
    assert "ORPHAN_IN_TABLE" in kinds
    assert not rpt.blocking


def test_cli_ref_flag_lands_in_report(tmp_path, monkeypatch, capsys):
    """Plomberie CLI : le --ref par defaut (HEAD) remonte dans le JSON."""
    repo = _make_repo(tmp_path, n_modules=5, claimed=5)
    monkeypatch.setattr(mod, "REPO_ROOT", repo)
    monkeypatch.setattr(sys, "argv", [
        "check_grothendieck_readme.py", "--json",
        "--path", str(repo / "lake"),
    ])
    rc = mod.main()
    out = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert out["ref"] == "HEAD"
    assert out["leaf_count_disk_fr"] == 5
