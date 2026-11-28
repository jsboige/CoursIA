"""Regression #28910 : la geometrie de la REF DE FUSION ne vaut pas celle de la PR.

En CI, `actions/checkout` pose `refs/pull/N/merge` : un commit de fusion dont
le premier parent est la tete de la branche de la PR et le second la pointe de
la base. Comparer CETTE ref a la base attribue a la PR tout ce que la base a
recu depuis le `base.sha` de l'evenement -- renommages de `main` compris.

Mesure fondatrice (issue #28910, deux PRs de po-2024) : une PR qui ne touche
ni la serie ni le baseline sortait `WARN: 1 LOST_KEY`, avec 55 renommages
imputes a la PR alors qu'ils venaient de `main`. La comparaison se fait desor-
mais sur la TETE de la PR (cf `pedagogy_density._pr_head_ref`).

Le second maillon est l'appariement de `git diff -M` : quand l'ancien chemin
a un jumeau `-output-...` de contenu presque identique, git apparie l'ancien
chemin a ce jumeau plutot qu'a la declinaison qui porte vraiment la cle. La
cle n'est alors pas perdue -- elle a change de declinaison -- et l'organe le
lisait comme une perte (`_key_prolonged`).

Les fixtures ci-dessous rejouent les DEUX maillons, et le temoin negatif
(c) prouve que l'organe n'a pas ete desarme : un renommage qui SUPPRIME
reellement une cle reste rouge.
"""

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import pedagogy_density as pd

import pytest


SERIES = "MyIA.AI.Notebooks/SymbolicLearning"
OLD = f"{SERIES}/SL-12c-PavlovDLS-Reproduction.ipynb"
NEW = f"{SERIES}/SL-12c-PavlovDLS-Reproduction-Python.ipynb"
TWIN = f"{SERIES}/SL-12c-PavlovDLS-Reproduction-output-Python.ipynb"
RENAMED = f"{SERIES}/SL-12c-PavlovDLS-Reproduction-v2.ipynb"

#: Contenu de l'ancien carnet ET de son jumeau ``-output`` : identiques,
#: donc ``git diff -M`` apparie l'ancien chemin au jumeau (100 % de similarite)
#: plutot qu'a la declinaison qui porte la cle.
CONTENT_A = '{"cells": [], "kind": "source"}\n'
#: Contenu de la declinaison qui porte reellement la cle : different, donc
#: ``-M`` ne la propose pas comme appariement de l'ancien chemin.
CONTENT_B = '{"cells": [], "kind": "python-declinaison"}\n'


def _git(repo: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", "-C", str(repo), "-c", "user.email=t@t", "-c", "user.name=t", *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace", check=check,
    )


def _write(repo: Path, rel: str, text: str) -> None:
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_baseline(tools: Path, notebooks: dict) -> None:
    (tools / "pedagogy_density_baseline.json").write_text(
        json.dumps({
            "_comment": "fixture #28910",
            "metric": "prose_chars / code_cells",
            "count": len(notebooks),
            "notebooks": notebooks,
        }),
        encoding="utf-8",
    )


def _commit(repo: Path, message: str) -> str:
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", message)
    return _git(repo, "rev-parse", "HEAD").stdout.strip()


@pytest.fixture
def merge_ref_repo(tmp_path):
    """Depot reproduisant la geometrie de la CI.

        c1 (fork == base.sha de l'evenement)
         \\
          \\--- c2 (main avance : renomme le carnet, ajoute son jumeau -output)
           \\
            M (ref de fusion : parent 1 = tete de la PR, parent 2 = pointe de main)

    La PR ne touche RIEN : tout ce que la comparaison voit vient de `main`.
    """
    repo = tmp_path / "repo"
    tools = repo / "scripts" / "notebook_tools"
    tools.mkdir(parents=True)
    _git(repo, "init", "-q")
    _git(repo, "checkout", "-q", "-b", "main")

    # c1 : le carnet d'origine, cle au baseline.
    _write(repo, OLD, CONTENT_A)
    _write_baseline(tools, {OLD: 2000.0})
    fork = _commit(repo, "c1 fork, le carnet est keye")

    # La branche de la PR ne change rien : c'est ce qui rend le rouge MESURABLE.
    _git(repo, "checkout", "-q", "-b", "pr", fork)
    pr_head = _git(repo, "rev-parse", "HEAD").stdout.strip()

    # main avance : il renomme le carnet et ajoute son jumeau `-output`.
    _git(repo, "checkout", "-q", "main")
    _git(repo, "mv", OLD, NEW)
    _write(repo, NEW, CONTENT_B)
    _write(repo, TWIN, CONTENT_A)
    _write_baseline(tools, {NEW: 2000.0})
    base_tip = _commit(repo, "c2 main renomme le carnet")

    # La ref de fusion : premier parent = tete de la PR, second = pointe de main.
    _git(repo, "checkout", "-q", "--detach", pr_head)
    _git(repo, "merge", "-q", "--no-ff", "-m", "merge ref", base_tip)
    merge_ref = _git(repo, "rev-parse", "HEAD").stdout.strip()
    _git(repo, "checkout", "-q", "--detach", merge_ref)

    return {
        "repo": repo, "tools": tools, "fork": fork,
        "pr_head": pr_head, "base_tip": base_tip, "merge_ref": merge_ref,
    }


def _wire(monkeypatch, tools: Path):
    monkeypatch.setattr(pd, "_TOOLS_DIR", tools)
    monkeypatch.setattr(pd, "BASELINE_FILE", tools / "pedagogy_density_baseline.json")


class TestMergeRefGeometry:
    """Maillon 1 : comparer la REF DE FUSION attribue a la PR ce que `main` a recu."""

    def test_head_is_a_merge_commit_in_this_geometry(self, merge_ref_repo):
        """Preuve de la geometrie : sans elle, le test ne rien prouverait."""
        repo = merge_ref_repo["repo"]
        parents = _git(repo, "rev-list", "--parents", "-n", "1", "HEAD").stdout.split()
        assert len(parents) == 3, "HEAD n'est pas un commit de fusion"
        assert parents[1] == merge_ref_repo["pr_head"], "le parent 1 n'est pas la tete de la PR"
        assert parents[2] == merge_ref_repo["base_tip"], "le parent 2 n'est pas la pointe de main"
        assert merge_ref_repo["base_tip"] != merge_ref_repo["fork"], (
            "le cote base doit etre en avance sur le base.sha de l'evenement"
        )

    def test_no_lost_key_for_a_rename_made_by_the_base(
        self, merge_ref_repo, monkeypatch, capsys
    ):
        """Le renommage vient de `main` : la PR ne peut pas l'avoir cause.

        Avant le correctif : `WARN: 1 LOST_KEY` avec 55 renommages (mesure
        #28910). Apres : 0 LOST_KEY, et la note dit QUOI a ete compare.
        """
        fixture = merge_ref_repo
        _wire(monkeypatch, fixture["tools"])
        assert pd._check_orphans(fixture["fork"]) == 0
        out = capsys.readouterr().out
        assert "0 LOST_KEY" in out
        assert "WARN" not in out
        # La note nomme le merge-base ET la tete de la PR comparee : un verdict
        # qui ne dit pas ce qu'il a compare ne prouve rien (#16122, review).
        assert f"LOST_KEY evalue contre {fixture['fork']}" in out
        assert "ref de fusion : compare a la tete de la PR" in out
        assert fixture["pr_head"] in out

    def test_organ_compares_the_pr_head_not_the_merge_ref(
        self, merge_ref_repo, monkeypatch
    ):
        """Le controle structurel : la comparaison porte sur la tete de la PR.

        Sans cette assertion, un correctif qui neutraliserait le finding
        (au lieu de comparer la bonne reference) passerait le test du dessus.
        """
        _wire(monkeypatch, merge_ref_repo["tools"])
        assert pd._pr_head_ref() == merge_ref_repo["pr_head"]
        assert pd._pr_head_ref() != merge_ref_repo["merge_ref"]


class TestProlongedKey:
    """Maillon 2 : `git diff -M` apparie l'ancien chemin au jumeau `-output`."""

    def test_radical_ignores_the_kind_marker(self):
        assert pd._radical(OLD) == pd._radical(NEW)
        assert pd._radical(OLD) == pd._radical(TWIN)
        assert pd._radical(NEW) != pd._radical(f"{SERIES}/Autre.ipynb")

    def test_a_key_moved_to_a_declination_is_not_a_loss(self):
        """La cle de base prolongee par une cle NEUVELLE de meme radical."""
        base = {OLD: 2000.0}
        head = {NEW: 2000.0}
        assert pd._key_prolonged(OLD, base, head) is True

    def test_a_key_that_was_already_there_prolongs_nothing(self):
        """Une cle deja presente appartient a un autre carnet : elle ne dit rien."""
        base = {OLD: 2000.0, NEW: 2000.0}
        head = {OLD: 2000.0, NEW: 2000.0}
        assert pd._key_prolonged(OLD, base, head) is False

    def test_pr_rename_paired_with_the_output_twin_is_not_a_loss(
        self, merge_ref_repo, monkeypatch, capsys
    ):
        """La PR renomme elle-meme, et git apparie l'ancien chemin au jumeau.

        La cle suit la declinaison qui porte le contenu : elle n'est pas
        perdue. Sans `_key_prolonged`, l'organe la lirait comme une perte.
        """
        fixture = merge_ref_repo
        repo, tools = fixture["repo"], fixture["tools"]
        _git(repo, "checkout", "-q", "-B", "pr-rename", fixture["fork"])
        _git(repo, "mv", OLD, NEW)
        _write(repo, NEW, CONTENT_B)
        _write(repo, TWIN, CONTENT_A)
        _write_baseline(tools, {NEW: 2000.0})
        _commit(repo, "la PR renomme le carnet et deplace la cle")
        _git(repo, "checkout", "-q", "--detach", "HEAD")

        _wire(monkeypatch, tools)
        assert pd._check_orphans(fixture["fork"]) == 0
        out = capsys.readouterr().out
        assert "0 LOST_KEY" in out

    def test_negative_control_a_rename_that_drops_the_key_still_fails(
        self, merge_ref_repo, monkeypatch, capsys
    ):
        """Témoin negatif : l'organe n'est pas desarme.

        La PR renomme le carnet et SUPPRIME la cle : c'est la regression
        #15917, elle doit rester rouge.
        """
        fixture = merge_ref_repo
        repo, tools = fixture["repo"], fixture["tools"]
        _git(repo, "checkout", "-q", "-B", "pr-keyloss", fixture["fork"])
        _git(repo, "mv", OLD, RENAMED)
        _write(repo, RENAMED, CONTENT_A)
        _write_baseline(tools, {})  # ... et la cle est simplement perdue
        _commit(repo, "la PR renomme le carnet et perd la cle")
        _git(repo, "checkout", "-q", "--detach", "HEAD")

        _wire(monkeypatch, tools)
        assert pd._check_orphans(fixture["fork"]) == 1
        out = capsys.readouterr().out
        assert "1 LOST_KEY" in out
        assert f"LOST_KEY {OLD} ->" in out
