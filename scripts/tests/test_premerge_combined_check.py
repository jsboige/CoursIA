"""Tests de l'organe premerge_combined_check.

Deux familles : un runner scripte pour chaque verdict (aucun git, aucun
pytest reel), puis un depot git jetable qui reproduit le cas fondateur --
deux changements verts chacun de leur cote, rouges une fois fusionnes.
"""

import importlib.util
import re
import subprocess
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ORGAN_PATH = HERE.parent / "coordination" / "premerge_combined_check.py"
_spec = importlib.util.spec_from_file_location("premerge_under_test", ORGAN_PATH)
pc = importlib.util.module_from_spec(_spec)
sys.modules["premerge_under_test"] = pc
_spec.loader.exec_module(pc)

BASE = "b" * 40
HEAD = "h" * 40
TREE = "a" * 40
MERGE = "c" * 40


class FakeRunner:
    """Rejoue chaque etape du geste ; ``pytest`` rend ce qu'on lui dit."""

    def __init__(self, *, fetch_rc=0, merge_tree_rc=0, worktree_add_rc=0,
                 pytest_rc=0, pytest_out="", pytest_timeout=False,
                 worktree_remove_rc=0):
        self.fetch_rc = fetch_rc
        self.merge_tree_rc = merge_tree_rc
        self.worktree_add_rc = worktree_add_rc
        self.pytest_rc = pytest_rc
        self.pytest_out = pytest_out
        self.pytest_timeout = pytest_timeout
        self.worktree_remove_rc = worktree_remove_rc
        self.calls: list[list[str]] = []

    def run(self, cmd, cwd=None, env=None, timeout=None):
        self.calls.append(list(cmd))
        if cmd[0] == "git":
            verb = cmd[3]
            if verb == "fetch":
                return pc.RunResult(self.fetch_rc, "", "")
            if verb == "rev-parse":
                ref = cmd[-1].split("^")[0]
                return pc.RunResult(0, {"base": BASE, "head": HEAD}[ref] + "\n", "")
            if verb == "merge-tree":
                out = TREE + "\n" if self.merge_tree_rc == 0 else TREE + "\nCONFLICT"
                return pc.RunResult(self.merge_tree_rc, out, "")
            if verb == "commit-tree":
                return pc.RunResult(0, MERGE + "\n", "")
            if verb == "worktree" and cmd[4] == "add":
                return pc.RunResult(self.worktree_add_rc, "", "")
            if verb == "worktree" and cmd[4] == "remove":
                return pc.RunResult(self.worktree_remove_rc, "", "")
        if "pytest" in cmd:
            if self.pytest_timeout:
                return pc.RunResult(124, "", "timeout", timed_out=True)
            return pc.RunResult(self.pytest_rc, self.pytest_out, "")
        raise AssertionError("commande non scriptee : " + " ".join(cmd))

    def verbs(self):
        return [" ".join(c[3:5]) if c[0] == "git" else "pytest" for c in self.calls]


def _worktree_with(tmp_path, *tests):
    wt = tmp_path / "wt"
    for rel in tests:
        path = wt / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("", encoding="utf-8")
    return wt


def _check(runner, tmp_path, tests=("t/test_a.py",), pr=None, present=None):
    wt = _worktree_with(tmp_path, *(tests if present is None else present))
    return pc.check(runner, tmp_path, base="base", head="head", worktree=wt,
                    tests=tuple(tests), workers=0, timeout_s=5, pr=pr)


def test_green_when_tests_pass_and_worktree_is_removed(tmp_path):
    runner = FakeRunner()
    v = _check(runner, tmp_path)
    assert v.verdict == "GREEN" and v.exit_code == 0
    assert v.merge_commit == MERGE and v.tests == ["t/test_a.py"]
    assert runner.verbs()[-1] == "worktree remove"
    assert not any("--force" in c for c in runner.calls)


def test_red_names_the_failing_tests(tmp_path):
    out = "FAILED t/test_a.py::test_unique - AssertionError\nERROR t/test_a.py::test_x\n"
    v = _check(FakeRunner(pytest_rc=1, pytest_out=out), tmp_path)
    assert v.verdict == "RED" and v.exit_code == 1
    assert v.failed == ["t/test_a.py::test_unique", "t/test_a.py::test_x"]


def test_textual_conflict_stops_before_any_worktree(tmp_path):
    runner = FakeRunner(merge_tree_rc=1)
    v = _check(runner, tmp_path)
    assert v.verdict == "CONFLICT" and v.exit_code == 1
    assert "worktree add" not in runner.verbs()


def test_fetch_failure_is_unreadable_not_green(tmp_path):
    runner = FakeRunner(fetch_rc=128)
    v = _check(runner, tmp_path, pr=123)
    assert v.verdict == "UNREADABLE" and v.reason == "fetch" and v.exit_code == 2
    assert runner.calls[0][3:] == ["fetch", "--quiet", "origin", "main", "pull/123/head"]


def test_timeout_is_unreadable_and_still_removes_the_worktree(tmp_path):
    runner = FakeRunner(pytest_timeout=True)
    v = _check(runner, tmp_path)
    assert v.verdict == "UNREADABLE" and v.reason == "timeout"
    assert runner.verbs()[-1] == "worktree remove"


def test_pytest_out_of_contract_is_unreadable(tmp_path):
    v = _check(FakeRunner(pytest_rc=4), tmp_path)
    assert v.verdict == "UNREADABLE" and v.reason == "pytest-rc-4"


def test_no_test_present_in_the_tree_is_unreadable(tmp_path):
    runner = FakeRunner()
    v = _check(runner, tmp_path, present=())
    assert v.verdict == "UNREADABLE" and v.reason == "no-tests-present"
    assert "pytest" not in runner.verbs()


def test_only_present_tests_are_run(tmp_path):
    runner = FakeRunner()
    v = _check(runner, tmp_path, tests=("t/test_a.py", "t/test_gone.py"),
               present=("t/test_a.py",))
    assert v.tests == ["t/test_a.py"]
    pytest_call = next(c for c in runner.calls if "pytest" in c)
    assert "t/test_gone.py" not in pytest_call


def test_worktree_git_refuses_to_remove_is_reported_not_forced(tmp_path):
    runner = FakeRunner(worktree_remove_rc=1)
    v = _check(runner, tmp_path)
    assert v.verdict == "GREEN" and v.worktree_left is not None
    assert not any("--force" in c for c in runner.calls)


def test_parse_failed_dedupes_and_keeps_order():
    out = "FAILED a::x - boom\nFAILED a::x - boom\n  FAILED b::y\nfoo FAILED c::z\n"
    assert pc.parse_failed(out) == ["a::x", "b::y"]


def test_integrity_list_points_at_existing_files():
    root = HERE.parents[1]
    missing = [t for t in pc.INTEGRITY_TESTS if not (root / t).is_file()]
    assert missing == []


# --- depot jetable : le conflit semantique du 04/11 en miniature ---------------


def _git_supports_write_tree() -> bool:
    out = subprocess.run(["git", "--version"], capture_output=True, text=True,
                         encoding="utf-8", errors="replace", check=False).stdout
    m = re.search(r"(\d+)\.(\d+)", out)
    return bool(m) and (int(m.group(1)), int(m.group(2))) >= (2, 38)


def _git(repo, *args):
    return subprocess.run(
        ["git", "-C", str(repo), "-c", "user.name=t", "-c", "user.email=t@t",
         "-c", "commit.gpgsign=false", *args],
        check=True, capture_output=True, text=True, encoding="utf-8",
        errors="replace",
    ).stdout.strip()


TEST_SRC = (
    "from pathlib import Path\n\n"
    "def test_registry_indexes_are_unique():\n"
    "    root = Path(__file__).resolve().parents[1]\n"
    "    vals = [p.read_text().strip() for p in sorted((root / 'reg').glob('*.txt'))]\n"
    "    assert len(vals) == len(set(vals)), vals\n"
)


@pytest.mark.skipif(not _git_supports_write_tree(),
                    reason="git merge-tree --write-tree exige git >= 2.38")
def test_semantic_conflict_is_red_only_on_the_merged_tree(tmp_path):
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q", "-b", "main")
    (repo / "reg").mkdir()
    (repo / "reg" / "a.txt").write_text("idx=1\n", encoding="utf-8")
    (repo / "tests_int").mkdir()
    (repo / "tests_int" / "test_reg.py").write_text(TEST_SRC, encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "base")
    base = _git(repo, "rev-parse", "HEAD")
    # main recoit une entree idx=2 ...
    (repo / "reg" / "b.txt").write_text("idx=2\n", encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "main adds idx=2")
    main_tip = _git(repo, "rev-parse", "HEAD")
    # ... et la PR, partie de la base, ajoute AUSSI idx=2 dans un autre fichier.
    _git(repo, "checkout", "-q", "-b", "pr", base)
    (repo / "reg" / "c.txt").write_text("idx=2\n", encoding="utf-8")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-q", "-m", "pr adds idx=2")
    pr_tip = _git(repo, "rev-parse", "HEAD")

    tests = ("tests_int/test_reg.py",)
    runner = pc.Runner()
    alone = pc.check(runner, repo, base=base, head=pr_tip,
                     worktree=tmp_path / "wt1", tests=tests, workers=0,
                     timeout_s=120)
    assert alone.verdict == "GREEN", alone
    merged = pc.check(runner, repo, base=main_tip, head=pr_tip,
                      worktree=tmp_path / "wt2", tests=tests, workers=0,
                      timeout_s=120)
    assert merged.verdict == "RED", merged
    assert merged.failed == ["tests_int/test_reg.py::test_registry_indexes_are_unique"]
    # Aucune ref creee ni deplacee, aucun worktree laisse.
    assert _git(repo, "rev-parse", "main") == main_tip
    assert _git(repo, "rev-parse", "pr") == pr_tip
    assert merged.worktree_left is None and alone.worktree_left is None
    assert "wt2" not in _git(repo, "worktree", "list")
