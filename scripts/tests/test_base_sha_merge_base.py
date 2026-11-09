#!/usr/bin/env python3
"""Controles de la base de comparaison des gardes de PR (residu de #10403).

Un garde qui compare l'etat de la base a la tete de la PR doit le faire en
TROIS points (`base...head`, soit `merge-base..head`), et lire l'etat
partage au merge-base, jamais a la pointe de la base.

Mesure fondatrice : sur une PR empilee dont la base etait en retard de 521
commits, les lectures en deux points ont fait "auditer" 287 carnets pour une
PR d'un seul, dont 3 faux positifs MD_REWRITE sur des carnets byte-identiques
a `origin/main`.

Chaque controle ci-dessous construit un depot git jetable ou la base a gagne
des commits depuis le fork, puis exige que le site ne rapporte QUE l'apport
de la PR. Tous rougissent sur la forme en deux points et passent sur la forme
en trois points -- c'est le controle negatif du defaut, pas une relecture du
code.
"""

from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
NOTEBOOK_TOOLS = REPO_ROOT / "scripts" / "notebook_tools"


def _load(name: str):
    """Charge un script de `scripts/notebook_tools/` par chemin explicite.

    Meme rationale que test_check_cell_source_parses : l'ambiguité de paquet
    d'espace de noms sur `scripts/notebook_tools/` differe entre un pytest
    local et la collecte combinee de la CI, donc on nomme le fichier.
    L'enregistrement dans `sys.modules` est requis par `@dataclass` sous
    `from __future__ import annotations` (dataclasses relit `cls.__module__`).
    """
    spec = importlib.util.spec_from_file_location(
        name, str(NOTEBOOK_TOOLS / f"{name}.py"))
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


# --------------------------------------------------------------------------
# Depot jetable : la base a gagne des commits depuis le fork
# --------------------------------------------------------------------------

SERIES = "MyIA.AI.Notebooks/Series"
#: Notebook modifie par `main` APRES le fork, jamais touche par la PR.
TOUCHED_ON_MAIN = f"{SERIES}/A.ipynb"
#: Notebook modifie par la PR : le seul apport imputable.
TOUCHED_BY_PR = f"{SERIES}/C.ipynb"
#: Notebook renomme par `main` APRES le fork, jamais touche par la PR.
RENAMED_ON_MAIN = f"{SERIES}/Rename/orig.ipynb"
RENAMED_ON_MAIN_NEW = f"{SERIES}/Rename/renamed.ipynb"


def _git(repo: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", "-C", str(repo), "-c", "user.email=t@t", "-c", "user.name=t",
         *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        check=check,
    )


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _commit(repo: Path, message: str) -> str:
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", message)
    return _git(repo, "rev-parse", "HEAD").stdout.strip()


@pytest.fixture
def stale_base_repo(tmp_path):
    """Depot a trois commits ou la base a avance depuis le fork.

        c1 --- c2   (main, pointe de la base : A.ipynb modifie,
         \\           Rename/orig.ipynb renomme)
          \\
           c3       (PR : C.ipynb modifie)

    `c2` est la pointe de la base, `c3` la tete de la PR, `c1` le merge-base.
    La forme en deux points (c2..c3) voit donc trois fichiers de plus que
    l'apport reel de la PR (c1..c3), qui est un seul carnet.
    """
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    _git(repo, "checkout", "-q", "-b", "main")

    _write(repo / TOUCHED_ON_MAIN, "{\"cells\": []}\n")
    _write(repo / TOUCHED_BY_PR, "{\"cells\": []}\n")
    _write(repo / RENAMED_ON_MAIN, "{\"cells\": [], \"probe\": \"rename\"}\n")
    c1 = _commit(repo, "c1 fork")

    # La base avance : un carnet modifie, un carnet renomme. La PR n'y touche pas.
    _write(repo / TOUCHED_ON_MAIN, "{\"cells\": [\"derive de main\"]}\n")
    _git(repo, "mv", RENAMED_ON_MAIN, RENAMED_ON_MAIN_NEW)
    c2 = _commit(repo, "c2 base avance")

    # La PR part du fork et ne touche qu'un carnet.
    _git(repo, "checkout", "-q", "-b", "pr", c1)
    _write(repo / TOUCHED_BY_PR, "{\"cells\": [\"apport de la PR\"]}\n")
    c3 = _commit(repo, "c3 apport de la PR")

    return {
        "repo": repo, "fork": c1, "base": c2, "head": c3,
    }


# --------------------------------------------------------------------------
# Sites 4, 5, 6 -- `git diff --name-only base head` (deux points)
# --------------------------------------------------------------------------


def _assert_pr_apport_only(files, repo, expected_name):
    """Un seul fichier imputable a la PR ; la derive de `main` est exclue."""
    names = set()
    for f in files:
        p = Path(f)
        names.add(p.relative_to(repo).as_posix() if p.is_absolute() else p.as_posix())
    assert sorted(names) == [expected_name], (
        "la lecture en deux points attribue a la PR la derive de `main` : "
        f"{sorted(names)}"
    )


class TestCheckCellSourceParsesDiffRange:
    """Site 4 : `check_cell_source_parses._diff_range` (deux points)."""

    def test_scope_is_the_pr_apport_only(self, stale_base_repo, monkeypatch):
        module = _load("check_cell_source_parses")
        monkeypatch.setattr(module, "REPO_ROOT", stale_base_repo["repo"])
        names = list(module._diff_range(
            stale_base_repo["base"], stale_base_repo["head"]))
        _assert_pr_apport_only(names, stale_base_repo["repo"], TOUCHED_BY_PR)

    def test_negative_control_up_to_date_base_is_unchanged(self, stale_base_repo):
        """Depot sain : base = fork, les deux formes rendent la meme chose."""
        repo = stale_base_repo["repo"]
        three_point = _git(repo, "diff", "--name-only",
                           f"{stale_base_repo['fork']}...{stale_base_repo['head']}")
        two_point = _git(repo, "diff", "--name-only",
                         f"{stale_base_repo['fork']}..{stale_base_repo['head']}")
        assert three_point.stdout == two_point.stdout
        assert three_point.stdout.strip() == TOUCHED_BY_PR


class TestMergeRefHeadIsUnchangedByTheFix:
    """La troisieme forme ne change rien quand HEAD est la ref de fusion.

    `actions/checkout` pose `refs/pull/N/merge` par defaut : la base est alors
    un ANCETRE de HEAD, donc `base..HEAD` et `base...HEAD` rendent le meme
    diff. Le defaut ne mord que lorsque HEAD est la ref de TETE -- ref de
    fusion indisponible (conflit), ou declencheur qui ne la construit pas --
    ce que la fixture `stale_base_repo` reproduit. Ce controle negatif prouve
    que le correctif ne retrecit pas le perimetre dans le regime nominal.
    """

    def test_merge_commit_makes_both_forms_equivalent(
            self, stale_base_repo, monkeypatch):
        repo = stale_base_repo["repo"]
        _git(repo, "checkout", "-q", "--detach", stale_base_repo["base"])
        _git(repo, "merge", "-q", "--no-ff", "-m", "merge ref",
             stale_base_repo["head"])
        merge_ref = _git(repo, "rev-parse", "HEAD").stdout.strip()

        two_point = _git(repo, "diff", "--name-only",
                         f"{stale_base_repo['base']}..{merge_ref}").stdout
        three_point = _git(repo, "diff", "--name-only",
                           f"{stale_base_repo['base']}...{merge_ref}").stdout
        assert two_point == three_point
        assert two_point.strip() == TOUCHED_BY_PR

        module = _load("check_math_render")
        monkeypatch.setattr(module, "REPO_ROOT", repo)
        assert module.pr_diff_files(
            stale_base_repo["base"], merge_ref) == [repo / TOUCHED_BY_PR]


class TestCheckLatexControlCharsDiff:
    """Site 5 : `check_latex_control_chars.pr_diff_files` (deux points)."""

    def test_scope_is_the_pr_apport_only(self, stale_base_repo, monkeypatch):
        module = _load("check_latex_control_chars")
        monkeypatch.setattr(module, "REPO_ROOT", stale_base_repo["repo"])
        files = module.pr_diff_files(
            stale_base_repo["base"], stale_base_repo["head"])
        _assert_pr_apport_only(files, stale_base_repo["repo"], TOUCHED_BY_PR)


class TestCheckMathRenderDiff:
    """Site 6 : `check_math_render.pr_diff_files` (deux points)."""

    def test_scope_is_the_pr_apport_only(self, stale_base_repo, monkeypatch):
        module = _load("check_math_render")
        monkeypatch.setattr(module, "REPO_ROOT", stale_base_repo["repo"])
        files = module.pr_diff_files(
            stale_base_repo["base"], stale_base_repo["head"])
        _assert_pr_apport_only(files, stale_base_repo["repo"], TOUCHED_BY_PR)


# --------------------------------------------------------------------------
# Sites 1 et 2 -- `git diff --name-status --find-renames base head`
# --------------------------------------------------------------------------


class TestReadmeLinkRenameEvidence:
    """Sites 1 et 2 : `diff_readme_link_violations._git_rename_evidence`.

    En deux points, le renommage fait par `main` apparait EN MIROIR
    (`renamed -> orig`) : une preuve de renommage que la PR n'a jamais
    produite, et `_pair_renames` reclasse alors en MOVED des liens qu'elle
    n'a pas deplaces.
    """

    def test_no_phantom_rename_from_the_base(self, stale_base_repo, monkeypatch):
        module = _load("diff_readme_link_violations")
        monkeypatch.chdir(stale_base_repo["repo"])
        file_renames, dir_renames = module._git_rename_evidence(
            stale_base_repo["base"], stale_base_repo["head"])
        assert file_renames == {}, (
            "renommage fantome attribue a la PR : " f"{file_renames}"
        )
        assert dir_renames == {}

    def test_positive_control_pr_rename_still_reported(
            self, stale_base_repo, monkeypatch):
        """Le renommage de la PR, lui, doit rester prouve (pas de mutisme)."""
        repo = stale_base_repo["repo"]
        # Renommage pur depuis l'etat du fork : la PR ne touche a rien d'autre.
        _git(repo, "checkout", "-q", "-B", "pr-rename", stale_base_repo["fork"])
        _git(repo, "mv", TOUCHED_BY_PR, f"{SERIES}/C-pr.ipynb")
        head = _commit(repo, "c4 renommage de la PR")
        module = _load("diff_readme_link_violations")
        monkeypatch.chdir(repo)
        file_renames, _dir_renames = module._git_rename_evidence(
            stale_base_repo["base"], head)
        assert file_renames == {TOUCHED_BY_PR: f"{SERIES}/C-pr.ipynb"}

    def test_unresolvable_base_says_so_instead_of_falling_back(
            self, stale_base_repo, monkeypatch, capsys):
        """Merge-base indeterminable : aucun repli silencieux en deux points."""
        module = _load("diff_readme_link_violations")
        monkeypatch.chdir(stale_base_repo["repo"])
        missing = "0" * 40
        assert module._git_rename_evidence(
            missing, stale_base_repo["head"]) == ({}, {})
        err = capsys.readouterr().err
        assert "diff trois points" in err
        assert "fail-closed" in err


# --------------------------------------------------------------------------
# Site 3 -- `.github/workflows/h1-hygiene-advisory.yml`
# --------------------------------------------------------------------------


class TestH1HygieneWorkflowDiff:
    """Site 3 : la ligne shell du workflow, une step bash non importable.

    Le controle est donc structurel : il lit la ligne et exige la forme en
    trois points. Il rougissait sur `"$BASE_SHA"..HEAD`.
    """

    WORKFLOW = REPO_ROOT / ".github" / "workflows" / "h1-hygiene-advisory.yml"

    def _added_line(self) -> str:
        lines = [
            line for line in self.WORKFLOW.read_text(encoding="utf-8").splitlines()
            if "--diff-filter=A" in line and "BASE_SHA" in line
        ]
        assert len(lines) == 1, f"ligne de diff introuvable ou ambigue : {lines}"
        return lines[0]

    def test_uses_three_point_diff(self):
        line = self._added_line()
        assert '"$BASE_SHA"...HEAD' in line
        assert '"$BASE_SHA"..HEAD' not in line


# --------------------------------------------------------------------------
# Site 7 -- `pedagogy_density._baseline_at` lu a la pointe de la base
# --------------------------------------------------------------------------

GEOMETRY = "MyIA.AI.Notebooks/GameTheory"
PD_OLD = f"{GEOMETRY}/Geometry-01-Intro.ipynb"
PD_OLD_RENAMED = f"{GEOMETRY}/Geometry-01-Intro-v2.ipynb"


def _write_baseline(tools: Path, notebooks: dict) -> None:
    import json

    (tools / "pedagogy_density_baseline.json").write_text(
        json.dumps({
            "_comment": "fixture",
            "metric": "prose_chars / code_cells",
            "count": len(notebooks),
            "notebooks": notebooks,
        }),
        encoding="utf-8",
    )


@pytest.fixture
def lost_key_false_positive_repo(tmp_path):
    """La base a acquis une cle APRES le fork ; la PR renomme ce carnet.

        c1 (fork)  : Geometry-01-Intro.ipynb suivi, baseline SANS sa cle
        c2 (base)  : la base regenerеe AJOUTE la cle (main a avance)
         \\
          c3 (PR) : la PR renomme le carnet en -v2, sans toucher au baseline

    La cle `Geometry-01-Intro.ipynb` n'existait pas au fork : la PR ne peut
    donc pas l'avoir perdue. Lue a la pointe de la base, la cle existe et la
    comparaison fabrique un LOST_KEY que la PR n'a pas cause.
    """
    repo = tmp_path / "repo"
    tools = repo / "scripts" / "notebook_tools"
    tools.mkdir(parents=True)
    _git(repo, "init", "-q")
    _git(repo, "checkout", "-q", "-b", "main")

    _write(repo / PD_OLD, "{\"cells\": []}\n")
    _write(repo / f"{GEOMETRY}/Setup-01-Env.ipynb", "{\"cells\": []}\n")
    _write_baseline(tools, {})
    c1 = _commit(repo, "c1 fork, baseline sans cle")

    # La base avance : son baseline est regenere et se met a cle le carnet.
    _write_baseline(tools, {PD_OLD: 2000.0})
    c2 = _commit(repo, "c2 la base keye le carnet")

    # La PR part du fork et renomme le carnet ; elle ne touche pas au baseline.
    _git(repo, "checkout", "-q", "-b", "pr", c1)
    _git(repo, "mv", PD_OLD, PD_OLD_RENAMED)
    c3 = _commit(repo, "c3 la PR renomme le carnet")

    return {"repo": repo, "tools": tools, "fork": c1, "base": c2, "head": c3}


class TestPedagogyDensityBaselineReadAtMergeBase:
    """Site 7 : l'etat partage se lit au merge-base, pas a la pointe de base."""

    def _wire(self, monkeypatch, tools: Path):
        module = _load("pedagogy_density")
        monkeypatch.setattr(module, "_TOOLS_DIR", tools)
        monkeypatch.setattr(
            module, "BASELINE_FILE",
            tools / "pedagogy_density_baseline.json")
        return module

    def test_no_lost_key_for_a_key_the_fork_did_not_hold(
            self, lost_key_false_positive_repo, monkeypatch, capsys):
        fixture = lost_key_false_positive_repo
        module = self._wire(monkeypatch, fixture["tools"])
        assert module._check_orphans(fixture["base"]) == 0
        out = capsys.readouterr().out
        assert "0 LOST_KEY" in out
        assert f"LOST_KEY {PD_OLD}" not in out, (
            "la cle acquise par la base apres le fork est imputee a la PR"
        )

    def test_note_names_the_merge_base(self, lost_key_false_positive_repo,
                                       monkeypatch, capsys):
        fixture = lost_key_false_positive_repo
        module = self._wire(monkeypatch, fixture["tools"])
        module._check_orphans(fixture["base"])
        out = capsys.readouterr().out
        assert f"LOST_KEY evalue contre {fixture['base']}, au merge-base " in out
        assert fixture["fork"] in out

    def test_negative_control_real_lost_key_still_fails(
            self, lost_key_false_positive_repo, monkeypatch, capsys):
        """Un renommage qui SUPPRIME une cle presente au fork reste rouge."""
        fixture = lost_key_false_positive_repo
        repo, tools = fixture["repo"], fixture["tools"]
        # On repart du fork pour que la cle EXISTE au merge-base.
        _git(repo, "checkout", "-q", "-B", "pr-keyed", fixture["fork"])
        _write_baseline(tools, {PD_OLD: 2000.0})
        fork_keyed = _commit(repo, "fork avec la cle")
        _git(repo, "mv", PD_OLD, PD_OLD_RENAMED)
        _write_baseline(tools, {})  # ... et la cle est simplement perdue
        _commit(repo, "renommage qui perd la cle")

        module = self._wire(monkeypatch, tools)
        assert module._check_orphans(fork_keyed) == 1
        out = capsys.readouterr().out
        assert f"LOST_KEY {PD_OLD} -> {PD_OLD_RENAMED}" in out

    def test_unresolvable_base_reports_not_evaluated(
            self, lost_key_false_positive_repo, monkeypatch, capsys):
        fixture = lost_key_false_positive_repo
        module = self._wire(monkeypatch, fixture["tools"])
        module._check_orphans("0" * 40)
        out = capsys.readouterr().out
        assert "LOST_KEY non evalue" in out
        assert "merge-base" in out
