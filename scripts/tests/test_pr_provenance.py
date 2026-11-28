#!/usr/bin/env python3
"""Tests de `scripts/pr_provenance.py` -- provenance Git des tetes de PR (#21436).

Le module est extrait de `check_lane_claim.py`. Ces tests epinglent son
contrat, le nombre de processus Git qu'il lance et ses memoires, sur des
depots reels construits dans `tmp_path` (la ref `origin/main` y est posee a
la main, sans distant). La configuration Git globale et systeme est masquee
pendant chaque test : les listes de commandes attendues ne dependent pas du
poste qui les joue.

Contrat sous test, inchange depuis l'extraction :

* `None` = provenance non etablie -- l'appelant garde les chemins de l'API
  (fail-CLOSED) ; une sortie de `git` illisible vaut `None`, jamais une liste
  amputee ;
* `[]` = la PR ne touche aucun chemin hors `main` ;
* une fusion hors `main` apporte le diff contre son parent de comparaison :
  celui deja sur `main`, le premier sinon, et la tete de `main` quand
  plusieurs parents y sont deja.

Run: python -m pytest scripts/tests/test_pr_provenance.py
"""
from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pr_provenance as pp  # noqa: E402

MERGE, P1, P2 = "1" * 40, "2" * 40, "3" * 40


class _Repo:
    """Un depot reel ; `git()` rend la sortie standard, blanchie aux extremites."""

    def __init__(self, root: Path) -> None:
        self.root = root
        root.mkdir()
        self.git("init", "-q", "-b", "main")
        self.git("config", "user.name", "Local test")
        self.git("config", "user.email", "test@example.invalid")

    def git(self, *args: str) -> str:
        return subprocess.run(
            ["git", *args], cwd=self.root, check=True, capture_output=True,
            text=True, encoding="utf-8", errors="replace",
        ).stdout.strip()

    def write(self, rel: str, text: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def commit(self, *paths: str, message: str = "commit") -> str:
        self.git("add", "--", *paths)
        self.git("commit", "-q", "-m", message, "--", *paths)
        return self.oid()

    def oid(self, ref: str = "HEAD") -> str:
        return self.git("rev-parse", ref)

    def set_main(self, ref: str) -> None:
        self.git("update-ref", "refs/remotes/origin/main", ref)


def _base(repo: _Repo) -> str:
    """Un commit de base sur `main` ; rend son oid, aussi tete de `origin/main`."""
    repo.write("base.txt", "base\n")
    base = repo.commit("base.txt", message="base")
    repo.set_main(base)
    return base


def _plain(repo: _Repo) -> str:
    """Une PR sans fusion : un commit propre, depuis la base."""
    base = _base(repo)
    repo.git("checkout", "-q", "-b", "pr", base)
    repo.write("own/a.txt", "a\n")
    return repo.commit("own/a.txt", message="a")


def _stacked(repo: _Repo) -> tuple[str, str, str, str]:
    """`main` avance, une PR le rattrape par une fusion, puis continue.

    Rend (base, tete de `main`, fusion, tete de la PR). Un seul parent de la
    fusion est sur `main` : c'est le parent de comparaison.
    """
    base = _base(repo)
    repo.git("checkout", "-q", "-b", "pr", base)
    repo.write("own/before.txt", "before\n")
    repo.commit("own/before.txt", message="before")
    repo.git("checkout", "-q", "main")
    repo.write("inherited.txt", "main\n")
    tip = repo.commit("inherited.txt", message="main update")
    repo.set_main(tip)
    repo.git("checkout", "-q", "pr")
    repo.git("merge", "--no-edit", "-q", "main")
    merge = repo.oid()
    repo.write("own/after.txt", "after\n")
    head = repo.commit("own/after.txt", message="after")
    return base, tip, merge, head


def _proc(args: tuple, rc: int = 0, out: bytes = b"",
          err: bytes = b"") -> subprocess.CompletedProcess:
    return subprocess.CompletedProcess(
        args=["git", *args], returncode=rc, stdout=out, stderr=err)


class _Calls(list):
    """Les commandes Git lancees pendant le test ; `inputs` porte leur entree."""

    inputs: list[bytes | None]


@pytest.fixture(autouse=True)
def _memoires_vides(monkeypatch):
    # Ni configuration globale ni systeme : `diff.renames` n'y est pas posee.
    monkeypatch.setenv("GIT_CONFIG_GLOBAL", os.devnull)
    monkeypatch.setenv("GIT_CONFIG_NOSYSTEM", "1")
    pp.reset_memos()
    yield
    pp.reset_memos()


@pytest.fixture
def calls(monkeypatch) -> _Calls:
    """Les commandes Git lancees pendant le test, dans l'ordre."""
    seen = _Calls()
    seen.inputs = []
    real = subprocess.run

    def run(cmd, *args, **kwargs):
        seen.append(tuple(cmd))
        seen.inputs.append(kwargs.get("input"))
        return real(cmd, *args, **kwargs)

    monkeypatch.setattr(pp.subprocess, "run", run)
    return seen


def _verbs(calls: list[tuple[str, ...]]) -> list[str]:
    return [cmd[1] for cmd in calls]


# Cle `diff.renames` non posee : la plomberie recoit l'option de la porcelaine.
CONFIG = ("git", "config", "--get", "diff.renames")
DIFF_TREE = ("git", "diff-tree", "-M", "-r", "--name-status", "-z", "--stdin")
WITH_MERGES = ["rev-parse", "log", "rev-list", "config", "diff-tree"]


# --- le calcul, sur un depot reel ---------------------------------------------


def test_merge_free_branch_costs_two_git_processes(tmp_path, monkeypatch, calls):
    repo = _Repo(tmp_path / "repo")
    _plain(repo)
    repo.write("b.txt", "b\n")
    head = repo.commit("b.txt", message="b")
    monkeypatch.chdir(repo.root)
    calls.clear()
    del calls.inputs[:]

    assert pp.files_against_main({"number": 1, "headRefOid": head}) == [
        "b.txt", "own/a.txt"]
    assert calls == [
        ("git", "rev-parse", "--verify", "origin/main"),
        ("git", "log", "--first-parent", "--format=%x01%H%x02%P", "--name-only",
         "-z", f"origin/main..{head}", "--"),
    ]


def test_merge_of_main_counts_the_pr_work_and_not_the_import_of_main(
        tmp_path, monkeypatch, calls):
    repo = _Repo(tmp_path / "repo")
    _base, _tip, _merge, head = _stacked(repo)
    monkeypatch.chdir(repo.root)
    calls.clear()

    assert pp.files_against_main({"number": 1, "headRefOid": head}) == [
        "own/after.txt", "own/before.txt"]
    # La tete, le log, les ancetres de `main`, la cle de renommage, UN
    # `diff-tree` : la lecture d'origine lancait huit processus pour cette
    # histoire.
    assert _verbs(calls) == WITH_MERGES
    assert "merge-base" not in _verbs(calls)
    assert calls[-1] == DIFF_TREE


def test_merge_equal_to_its_main_parent_brings_no_path(
        tmp_path, monkeypatch, calls):
    # Fusion sans diff contre son parent de `main` : le lot n'emet aucun bloc
    # pour ce couple, ce qui vaut contribution vide.
    repo = _Repo(tmp_path / "repo")
    base = _base(repo)
    repo.git("checkout", "-q", "-b", "pr", base)
    repo.git("commit", "-q", "--allow-empty", "-m", "metadata")
    repo.git("checkout", "-q", "main")
    repo.write("inherited.txt", "main\n")
    tip = repo.commit("inherited.txt", message="main update")
    repo.set_main(tip)
    repo.git("checkout", "-q", "pr")
    repo.git("merge", "--no-edit", "-q", "main")
    head = repo.oid()
    monkeypatch.chdir(repo.root)
    calls.clear()
    del calls.inputs[:]

    assert pp.files_against_main({"number": 1, "headRefOid": head}) == []
    assert _verbs(calls) == WITH_MERGES
    # La ligne lue est `<fusion> <parent de comparaison>`.
    assert calls.inputs[-1] == f"{head} {tip}\n".encode("ascii")


@pytest.mark.parametrize("resolution, expected", [
    ("PR merge resolution\n", ["shared.txt"]),  # une resolution propre
    ("left side\n", ["shared.txt"]),            # egale un parent deja sur main
    ("main resolution\n", []),                  # egale la tete de main
])
def test_merge_whose_parents_are_all_on_main_is_compared_with_main_tip(
        tmp_path, monkeypatch, calls, resolution, expected):
    repo = _Repo(tmp_path / "repo")
    repo.write("shared.txt", "base\n")
    base = repo.commit("shared.txt", message="base")

    def merge_conflict(branch: str) -> None:
        proc = subprocess.run(
            ["git", "merge", "--no-commit", branch], cwd=repo.root,
            capture_output=True, text=True, encoding="utf-8", errors="replace")
        assert proc.returncode == 1, proc.stdout + proc.stderr

    repo.git("checkout", "-q", "-b", "right", base)
    repo.write("shared.txt", "right side\n")
    repo.commit("shared.txt", message="right side")
    repo.git("checkout", "-q", "main")
    repo.write("shared.txt", "left side\n")
    left = repo.commit("shared.txt", message="left side")
    merge_conflict("right")
    repo.write("shared.txt", "main resolution\n")
    repo.git("add", "shared.txt")
    repo.git("commit", "-q", "-m", "main merge resolution")
    repo.set_main("HEAD")

    # Les deux parents de cette fusion sont deja sur `main` : la comparaison
    # se fait contre la tete de `main`, qui n'est l'un ni l'autre.
    repo.git("checkout", "-q", "-b", "pr", left)
    merge_conflict("right")
    repo.write("shared.txt", resolution)
    repo.git("add", "shared.txt")
    repo.git("commit", "-q", "-m", "PR merge resolution")
    head = repo.oid()
    tip = repo.oid("origin/main")
    monkeypatch.chdir(repo.root)
    calls.clear()
    del calls.inputs[:]

    assert pp.files_against_main({"number": 1, "headRefOid": head}) == expected
    assert _verbs(calls) == WITH_MERGES
    assert calls.inputs[-1] == f"{head} {tip}\n".encode("ascii")


def test_octopus_merge_is_compared_with_its_first_parent(
        tmp_path, monkeypatch, calls):
    repo = _Repo(tmp_path / "repo")
    base = _base(repo)
    for branch, name in (("one", "one.txt"), ("two", "two.txt")):
        repo.git("checkout", "-q", "-b", branch, base)
        repo.write(name, name + "\n")
        repo.commit(name, message=branch)
    repo.git("checkout", "-q", "-b", "pr", base)
    repo.write("pr.txt", "pr\n")
    repo.commit("pr.txt", message="pr")     # sans lui, `git merge one two` avance
    #                                    la branche sur `one` et ne fusionne que
    #                                    `two` : deux parents, pas trois.
    pr_tip = repo.oid()
    repo.git("merge", "--no-edit", "-q", "one", "two")
    head = repo.oid()
    monkeypatch.chdir(repo.root)
    calls.clear()
    del calls.inputs[:]

    # Aucun parent n'est sur `main` : le premier sert de comparaison, et le
    # `diff-tree` ne demande que ce couple-la.
    assert pp.files_against_main({"number": 1, "headRefOid": head}) == [
        "one.txt", "pr.txt", "two.txt"]
    assert _verbs(calls) == WITH_MERGES
    assert calls.inputs[-1] == f"{head} {pr_tip}\n".encode("ascii")


def test_two_merges_compared_with_the_same_parent_share_one_read(
        tmp_path, monkeypatch, calls):
    # L'en-tete d'un bloc est l'oid de la fusion : deux fusions comparees a
    # la meme tete de `main` tiennent dans un seul `diff-tree`.
    repo = _Repo(tmp_path / "repo")
    _base(repo)
    repo.write("m1.txt", "1\n")
    first = repo.commit("m1.txt", message="m1")
    repo.write("m2.txt", "2\n")
    tip = repo.commit("m2.txt", message="m2")
    repo.set_main(tip)
    tree_first = repo.git("rev-parse", first + "^{tree}")
    tree_tip = repo.git("rev-parse", tip + "^{tree}")
    older = repo.git("commit-tree", tree_first, "-p", first, "-p", tip, "-m", "older")
    head = repo.git("commit-tree", tree_tip, "-p", older, "-p", first, "-p", tip,
                    "-m", "newer")
    monkeypatch.chdir(repo.root)
    calls.clear()
    del calls.inputs[:]

    assert pp.files_against_main({"number": 1, "headRefOid": head}) == ["m2.txt"]
    assert _verbs(calls) == WITH_MERGES
    # Les deux couples dans UNE entree, dans l'ordre du log (premier parent).
    assert calls.inputs[-1] == (f"{head} {tip}\n{older} {tip}\n").encode("ascii")


def test_a_rename_carried_by_the_merge_alone_keeps_its_new_name(
        tmp_path, monkeypatch):
    # Mesure du 27/11 sur #26601 : la ligne `<parent> <fusion>` fait lire le
    # diff a l'envers, et le renommage rend alors l'ANCIEN nom -- la PR
    # perdrait celui qu'elle cree. Ici le renommage n'existe que dans la
    # fusion : aucun commit ordinaire ne peut le rattraper.
    repo = _Repo(tmp_path / "repo")
    repo.write("old.txt", "ligne un\nligne deux\nligne trois\n")
    base = repo.commit("old.txt", message="base")
    repo.set_main(base)
    repo.git("checkout", "-q", "-b", "pr", base)
    repo.write("own.txt", "own\n")
    repo.commit("own.txt", message="own")
    repo.git("checkout", "-q", "main")
    repo.write("main.txt", "main\n")
    tip = repo.commit("main.txt", message="main update")
    repo.set_main(tip)
    repo.git("checkout", "-q", "pr")
    repo.git("merge", "--no-edit", "-q", "--no-commit", "main")
    repo.git("mv", "old.txt", "new.txt")
    repo.git("commit", "-q", "-m", "merge then rename")
    head = repo.oid()
    assert repo.git("rev-list", "--parents", "-n", "1", head).split()[1:] == [
        repo.git("rev-parse", "pr~1"), tip], "la tete est bien la fusion"
    monkeypatch.chdir(repo.root)

    assert pp.files_against_main({"number": 1, "headRefOid": head}) == [
        "new.txt", "own.txt"]


@pytest.mark.parametrize("renames, option", [
    (None, "-M"),            # cle non posee : la porcelaine detecte les renommages
    ("true", "-M"),
    ("copies", "-C"),
    ("false", "--no-renames"),
])
def test_a_merge_contribution_reads_like_the_isolated_diff_whatever_the_config(
        tmp_path, monkeypatch, calls, renames, option):
    # Le lot (`diff-tree`, plomberie) et le `git diff` isole qu'il remplace
    # (porcelaine) doivent rendre les memes noms, y compris sur un renommage.
    repo = _Repo(tmp_path / "repo")
    if renames is not None:
        repo.git("config", "diff.renames", renames)
    repo.write("old.txt", "ligne un\nligne deux\nligne trois\n")
    base = repo.commit("old.txt", message="base")
    repo.set_main(base)
    repo.git("checkout", "-q", "-b", "pr", base)
    repo.git("mv", "old.txt", "new.txt")     # le renommage est deja indexe
    repo.write("new.txt", "ligne un\nligne deux\nligne trois modifiee\n")
    repo.git("add", "--", "new.txt")
    repo.git("commit", "-q", "-m", "rename")  # sans chemin : la suppression suit
    repo.git("checkout", "-q", "main")
    repo.write("main.txt", "main\n")
    tip = repo.commit("main.txt", message="main update")
    repo.set_main(tip)
    repo.git("checkout", "-q", "pr")
    repo.git("merge", "--no-edit", "-q", "main")
    head = repo.oid()
    monkeypatch.chdir(repo.root)
    calls.clear()

    isolated = set(subprocess.run(
        ["git", "diff", "--name-only", "-z", tip, head, "--"], cwd=repo.root,
        check=True, capture_output=True,
    ).stdout.decode("utf-8").split("\0")) - {""}
    assert isolated, "le renommage est un changement apporte par la fusion"
    assert "main.txt" not in isolated, "importe de main, pas apporte"
    assert set(pp.files_against_main({"number": 1, "headRefOid": head})) == isolated
    assert calls[-1] == ("git", "diff-tree", option, "-r", "--name-status", "-z",
                         "--stdin")


def test_files_changed_against_main_is_the_three_dot_diff(
        tmp_path, monkeypatch, calls):
    repo = _Repo(tmp_path / "repo")
    _base, _tip, _merge, head = _stacked(repo)
    monkeypatch.chdir(repo.root)
    calls.clear()
    del calls.inputs[:]
    pr = {"number": 1, "headRefOid": head}

    assert pp.files_changed_against_main(pr) == [
        "own/after.txt", "own/before.txt"]
    assert pp.files_changed_against_main(pr) == [
        "own/after.txt", "own/before.txt"]
    # La tete est etablie une fois ; le diff, jamais memoise, se rejoue.
    assert _verbs(calls) == ["cat-file", "diff", "diff"]


# --- memoires -----------------------------------------------------------------


def test_an_established_result_is_memoised_until_main_moves(
        tmp_path, monkeypatch, calls):
    repo = _Repo(tmp_path / "repo")
    head = _plain(repo)
    monkeypatch.chdir(repo.root)
    pr = {"number": 1, "headRefOid": head}

    first = pp.files_against_main(pr)
    assert first == ["own/a.txt"]
    first.append("mutated.txt")       # la liste rendue est une copie
    calls.clear()
    del calls.inputs[:]
    assert pp.files_against_main(pr) == ["own/a.txt"]
    # La cle de memoire porte la tete de `main` : elle se relit, mais le
    # parcours ne se rejoue pas.
    assert _verbs(calls) == ["rev-parse"]

    repo.set_main(head)               # `main` rejoint la tete : plus rien hors de lui
    calls.clear()
    del calls.inputs[:]
    assert pp.files_against_main(pr) == []
    assert _verbs(calls) == ["rev-parse", "log"]


def test_a_failed_walk_is_not_memoised(tmp_path, monkeypatch):
    repo = _Repo(tmp_path / "repo")
    head = _plain(repo)
    monkeypatch.chdir(repo.root)
    pr = {"number": 1, "headRefOid": head}
    real = pp._git

    def failing(*args, timeout, data=None):
        if args[0] == "log":
            return _proc(args, rc=128, err=b"fatal: lecture impossible\n")
        return real(*args, timeout=timeout, data=data)

    with monkeypatch.context() as patch:
        patch.setattr(pp, "_git", failing)
        assert pp.files_against_main(pr) is None
    assert pp._FILES_MEMO == {}, "un echec n'entre pas en memoire"
    assert pp.files_against_main(pr) == ["own/a.txt"]


def test_reset_memos_empties_the_four_memoires(tmp_path, monkeypatch):
    repo = _Repo(tmp_path / "repo")
    _base, _tip, _merge, head = _stacked(repo)
    monkeypatch.chdir(repo.root)
    assert pp.files_against_main({"number": 1, "headRefOid": head}) == [
        "own/after.txt", "own/before.txt"]
    pp.head_commit({"number": 1, "headRefOid": head})
    assert len(pp._HEAD_MEMO) == len(pp._FILES_MEMO) == 1
    assert len(pp._ANCESTORS_MEMO) == len(pp._RENAMES_MEMO) == 1

    pp.reset_memos()
    assert pp._HEAD_MEMO == {} and pp._FILES_MEMO == {}
    assert pp._ANCESTORS_MEMO == {} and pp._RENAMES_MEMO == {}


# --- provenance non etablie ---------------------------------------------------


def test_a_head_of_unexpected_shape_is_none_without_any_git_process(monkeypatch):
    def forbidden(*args, timeout, data=None):
        raise AssertionError("aucun processus Git attendu")

    monkeypatch.setattr(pp, "_git", forbidden)
    assert pp.files_against_main({"number": 1, "headRefOid": "abc"}) is None
    assert pp.files_against_main({"number": 1}) is None
    assert pp.head_commit({"number": 1, "headRefOid": "a" * 39}) is None


def test_a_missing_head_object_stays_none_even_with_a_pull_number(
        tmp_path, monkeypatch, calls):
    # Le depot n'a pas de distant : la recuperation par la ref de pull echoue.
    repo = _Repo(tmp_path / "repo")
    _plain(repo)
    monkeypatch.chdir(repo.root)
    calls.clear()

    pr = {"number": 1, "headRefOid": "0" * 40}
    assert pp.files_against_main(pr) is None
    assert _verbs(calls) == ["rev-parse", "log", "cat-file", "fetch"]
    assert pp._FILES_MEMO == {} and pp._HEAD_MEMO == {}


def test_a_failed_walk_on_a_present_head_never_fetches(tmp_path, monkeypatch):
    repo = _Repo(tmp_path / "repo")
    head = _plain(repo)
    monkeypatch.chdir(repo.root)
    seen: list[tuple] = []

    def failing(*args, timeout, data=None):
        seen.append(args)
        if args[0] == "log":
            return _proc(args, rc=128)
        return _proc(args)

    monkeypatch.setattr(pp, "_git", failing)
    assert pp.files_against_main({"number": 7, "headRefOid": head}) is None
    assert [step[0] for step in seen] == ["rev-parse", "log", "cat-file"]


def test_head_commit_fetches_the_pull_ref_of_a_missing_object(monkeypatch):
    head = "a" * 40
    answers = {
        ("cat-file", "-e", head + "^{commit}"): _proc((), rc=1),
        ("fetch", "--no-tags", "origin", "refs/pull/7/head"): _proc(()),
        ("rev-parse", "--verify", "FETCH_HEAD"): _proc(
            (), out=head.upper().encode("ascii") + b"\n"),
    }
    seen: list[tuple] = []

    def fake(*args, timeout, data=None):
        seen.append(args)
        return answers[args]

    monkeypatch.setattr(pp, "_git", fake)
    pr = {"number": 7, "headRefOid": head}
    assert pp.head_commit(pr) == head.upper()
    assert pp.head_commit(pr) == head.upper(), "un succes est memoise"
    assert seen == [
        ("cat-file", "-e", head + "^{commit}"),
        ("fetch", "--no-tags", "origin", "refs/pull/7/head"),
        ("rev-parse", "--verify", "FETCH_HEAD"),
    ]


def test_head_commit_is_none_when_the_pull_ref_brings_another_commit(monkeypatch):
    head = "a" * 40
    seen: list[tuple] = []

    def fake(*args, timeout, data=None):
        seen.append(args)
        if args[0] == "cat-file":
            return _proc(args, rc=1)
        if args[0] == "fetch":
            return _proc(args)
        return _proc(args, out=(("b" * 40) + "\n").encode("ascii"))

    monkeypatch.setattr(pp, "_git", fake)
    pr = {"number": 7, "headRefOid": head}
    assert pp.head_commit(pr) is None
    assert pp.head_commit(pr) is None, "un echec se retente"
    assert [step[0] for step in seen] == [
        "cat-file", "fetch", "rev-parse", "cat-file", "fetch", "rev-parse"]
    assert pp._HEAD_MEMO == {}


def test_a_stale_head_is_none_even_when_the_pull_ref_answers(tmp_path, monkeypatch):
    # La tete annoncee n'existe pas dans le depot local et la ref de pull en
    # ramene une AUTRE (la PR a ete repoussee entre la lecture de l'API et
    # cet appel) : la provenance n'est pas etablie, le parcours n'est pas
    # rejoue sur un commit que la PR n'a pas annonce, et rien n'entre en
    # memoire.
    repo = _Repo(tmp_path / "repo")
    tip = _plain(repo)
    monkeypatch.chdir(repo.root)
    real = pp._git
    seen: list[tuple] = []

    def pull_ref(*args, timeout, data=None):
        seen.append(args)
        if args[0] == "fetch":
            return _proc(args)                    # ce depot n'a aucun distant
        if args[0] == "rev-parse" and args[-1] == "FETCH_HEAD":
            return _proc(args, out=(tip + "\n").encode("ascii"))
        return real(*args, timeout=timeout, data=data)

    monkeypatch.setattr(pp, "_git", pull_ref)
    stale = "a" * 40
    assert pp.files_against_main({"number": 1, "headRefOid": stale}) is None
    assert [step[0] for step in seen] == [
        "rev-parse", "log", "cat-file", "fetch", "rev-parse"]
    assert pp._FILES_MEMO == {} and pp._HEAD_MEMO == {}


# --- sorties illisibles : fail-CLOSED -----------------------------------------


def test_parse_log_reads_the_three_marked_fields():
    raw = (b"\x01" + b"a" * 40 + b"\x02" + b"b" * 40 + b" " + b"c" * 40
           + b"\x00\none.txt\0dir/two.txt\0"
           + b"\x01" + b"d" * 40 + b"\x02\x00\nthree.txt\0")
    assert pp._parse_log(raw) == [
        ("a" * 40, ["b" * 40, "c" * 40], ["one.txt", "dir/two.txt"]),
        ("d" * 40, [], ["three.txt"]),
    ]
    assert pp._parse_log(b"") == []


@pytest.mark.parametrize("raw", [
    b"garbage\n",
    b"\x01" + b"a" * 40 + b"\x02" + b"b" * 40,     # en-tete sans NUL final
    b"\x01\x00name\0",                              # oid absent
    b"\x01" + b"a" * 40 + b"\x00name\0",            # marqueur des parents absent
])
def test_parse_log_refuses_an_unexpected_shape(raw):
    assert pp._parse_log(raw) is None


MERGE2 = "4" * 40
# Deux fusions (MERGE, MERGE2), chacune comparee a son parent (P1, P2).
PAIRS = [(MERGE, P1), (MERGE2, P2)]


def _lot(monkeypatch, out: bytes, rc: int = 0):
    """Joue `_pair_diffs` sur un `git` factice ; rend (resultat, entrees recues)."""
    stdin: list[bytes | None] = []

    def fake(*args, timeout, data=None):
        if args[0] == "config":
            return _proc(args, rc=1)                # cle `diff.renames` non posee
        stdin.append(data)
        return _proc(args, rc=rc, out=out)

    monkeypatch.setattr(pp, "_git", fake)
    return pp._pair_diffs(PAIRS, timeout=5), stdin


def test_pair_diffs_reads_merge_then_parent_and_labels_blocks_by_merge(monkeypatch):
    # Une ligne `<fusion> <parent de comparaison>` : Git y compare la fusion a
    # ce parent. Dans l'autre sens, le diff sort a l'envers.
    out = (f"{MERGE}\0M\0a.txt\0D\0dir/b.txt\0{MERGE2}\0A\0c.txt\0").encode("ascii")
    blocks, stdin = _lot(monkeypatch, out)
    assert blocks == {MERGE: {"a.txt", "dir/b.txt"}, MERGE2: {"c.txt"}}
    assert stdin == [f"{MERGE} {P1}\n{MERGE2} {P2}\n".encode("ascii")]


def test_a_pair_without_difference_emits_no_block(monkeypatch):
    blocks, _stdin = _lot(monkeypatch, f"{MERGE}\0M\0a.txt\0".encode("ascii"))
    assert blocks == {MERGE: {"a.txt"}}, "le second couple est absent du resultat"


def test_pair_diffs_keeps_the_new_name_of_a_rename_and_the_copy_destination(
        monkeypatch):
    out = (f"{MERGE}\0R100\0old.txt\0new.txt\0C75\0src.txt\0dst.txt\0T\0plain\0"
           f"M\0kept.txt\0").encode("ascii")
    blocks, _stdin = _lot(monkeypatch, out)
    assert blocks == {MERGE: {"new.txt", "dst.txt", "plain", "kept.txt"}}


@pytest.mark.parametrize("bad", [
    b"loose.txt\0",                                         # nom avant tout en-tete
    f"{'9' * 40}\0M\0a.txt\0".encode("ascii"),              # en-tete hors du lot
    f"{P1}\0M\0a.txt\0".encode("ascii"),                    # en-tete = un parent : lu a l'envers
    f"{MERGE}\0M\0a.txt\0{MERGE}\0M\0b.txt\0".encode("ascii"),  # en-tete repeatee
    f"{MERGE}\0Q\0a.txt\0".encode("ascii"),                 # statut inconnu
    f"{MERGE}\0M100\0a.txt\0".encode("ascii"),              # score sur un statut simple
    f"{MERGE}\0M\0".encode("ascii"),                        # chemin absent
    f"{MERGE}\0R\0old.txt\0new.txt\0".encode("ascii"),      # score absent
    f"{MERGE}\0R100\0old.txt\0".encode("ascii"),            # nouveau nom absent
    f"{MERGE}\0R100\0old.txt\0\0".encode("ascii"),          # nouveau nom vide
    b"\xff\0a.txt\0" + b"\0",                               # statut indecodable
])
def test_pair_diffs_refuses_an_unexpected_shape(monkeypatch, bad):
    assert _lot(monkeypatch, bad)[0] is None, bad


def test_pair_diffs_is_none_when_git_fails(monkeypatch):
    blocks, _stdin = _lot(monkeypatch, b"", rc=128)
    assert blocks is None


def test_an_unreadable_lot_output_is_none_on_a_real_merge(tmp_path, monkeypatch):
    repo = _Repo(tmp_path / "repo")
    _base, _tip, _merge, head = _stacked(repo)
    monkeypatch.chdir(repo.root)
    real = pp._git

    def lying(*args, timeout, data=None):
        if "diff-tree" in args:
            return _proc(args, out=b"loose.txt\0")
        return real(*args, timeout=timeout, data=data)

    monkeypatch.setattr(pp, "_git", lying)
    assert pp.files_against_main({"number": 1, "headRefOid": head}) is None
    assert pp._FILES_MEMO == {}


def test_a_failed_lot_is_none_on_a_real_merge(tmp_path, monkeypatch):
    repo = _Repo(tmp_path / "repo")
    _base, _tip, _merge, head = _stacked(repo)
    monkeypatch.chdir(repo.root)
    real = pp._git

    def failing(*args, timeout, data=None):
        if "diff-tree" in args:
            return _proc(args, rc=128)
        return real(*args, timeout=timeout, data=data)

    monkeypatch.setattr(pp, "_git", failing)
    assert pp.files_against_main({"number": 1, "headRefOid": head}) is None
    assert pp._FILES_MEMO == {}


# --- la cle `diff.renames` : traduite pour la plomberie ------------------------


@pytest.mark.parametrize("rc, out, expected", [
    (1, b"", ("-M",)),                   # cle non posee : defaut de la porcelaine
    (0, b"true\n", ("-M",)),
    (0, b"Yes\n", ("-M",)),
    (0, b"COPIES\n", ("-C",)),
    (0, b"copy\n", ("-C",)),
    (0, b"false\n", ("--no-renames",)),
    (0, b"off\n", ("--no-renames",)),
    (0, b"\n", ("-M",)),                 # cle posee sans valeur
    (0, b"zut\n", None),                 # la porcelaine refuserait de meme
    (128, b"", None),
])
def test_renames_args_translates_the_config_key(monkeypatch, rc, out, expected):
    seen: list[tuple] = []

    def fake(*args, timeout, data=None):
        seen.append(args)
        return _proc(args, rc=rc, out=out)

    monkeypatch.setattr(pp, "_git", fake)
    assert pp._renames_args(timeout=5) == expected
    assert seen == [("config", "--get", "diff.renames")]
    if expected is None:
        assert pp._RENAMES_MEMO == {}, "un echec n'entre pas en memoire"
        assert pp._renames_args(timeout=5) is None
        assert len(seen) == 2, "un echec se retente"
    else:
        assert pp._renames_args(timeout=5) == expected
        assert len(seen) == 1, "une decision est memoisee pour le processus"
        assert len(pp._RENAMES_MEMO) == 1


# --- ancestralite : une lecture pour tout le processus ------------------------


def test_ancestors_of_main_are_read_once_and_serve_every_head(
        tmp_path, monkeypatch, calls):
    repo = _Repo(tmp_path / "repo")
    base, _tip, _merge, head = _stacked(repo)
    repo.git("checkout", "-q", "-b", "pr2", base)
    repo.write("other/own.txt", "other\n")
    repo.commit("other/own.txt", message="other")
    repo.git("merge", "--no-edit", "-q", "main")
    head2 = repo.oid()
    monkeypatch.chdir(repo.root)
    calls.clear()
    del calls.inputs[:]

    assert pp.files_against_main({"number": 1, "headRefOid": head}) == [
        "own/after.txt", "own/before.txt"]
    assert _verbs(calls) == WITH_MERGES
    calls.clear()
    # Les ancetres de `main` et la cle de renommage servent a la seconde tete
    # sans etre relus.
    assert pp.files_against_main({"number": 2, "headRefOid": head2}) == ["other/own.txt"]
    assert _verbs(calls) == ["rev-parse", "log", "diff-tree"]
    assert len(pp._ANCESTORS_MEMO) == 1 and len(pp._RENAMES_MEMO) == 1

    # `main` avance : ses ancetres se relisent, et une seule entree reste.
    repo.set_main(head2)
    calls.clear()
    del calls.inputs[:]
    assert pp._ancestors(head2, timeout=5) is not None
    assert head2 in next(iter(pp._ANCESTORS_MEMO.values()))
    assert len(pp._ANCESTORS_MEMO) == 1
    assert _verbs(calls) == ["rev-list"]


def test_a_failed_ancestors_read_is_none_and_is_not_memoised(
        tmp_path, monkeypatch):
    repo = _Repo(tmp_path / "repo")
    _base, _tip, _merge, head = _stacked(repo)
    monkeypatch.chdir(repo.root)
    real = pp._git

    def failing(*args, timeout, data=None):
        if args[0] == "rev-list":
            return _proc(args, rc=128)
        return real(*args, timeout=timeout, data=data)

    with monkeypatch.context() as patch:
        patch.setattr(pp, "_git", failing)
        assert pp.files_against_main({"number": 1, "headRefOid": head}) is None
    assert pp._ANCESTORS_MEMO == {} and pp._FILES_MEMO == {}
    assert pp.files_against_main({"number": 1, "headRefOid": head}) == [
        "own/after.txt", "own/before.txt"]


# --- le lecteur de claims delegue sous les noms d'origine ----------------------


def test_claims_reader_delegates_under_the_original_names(monkeypatch):
    import check_lane_claim as clc

    sentinel = ["sentinel.txt"]
    seen: list[str] = []

    def spy(name):
        def fake(pr, timeout):
            seen.append(name)
            return sentinel if name == "files_against_main" else "ab"
        return fake

    for name in ("head_commit", "files_changed_against_main", "files_against_main"):
        monkeypatch.setattr(pp, name, spy(name))
    pr = {"number": 1, "headRefOid": "a" * 40}

    assert clc._pr_head_commit(pr) == "ab"
    assert clc._pr_files_changed_against_main(pr) == "ab"
    assert clc._pr_files_against_main(pr) is sentinel
    assert seen == ["head_commit", "files_changed_against_main",
                    "files_against_main"]
