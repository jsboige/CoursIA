"""Tests for scripts/lean/check_mathlib_cache.py — Mathlib .olean cache checker.

Covers the filesystem-composable helpers:
- ``find_lakes``: lakefile discovery (SKIP_DIRS pruning, .claude worktree exclusion)
- ``count_oleans``: recursive .olean counting under a path
- ``declares_mathlib``: case-insensitive ``mathlib`` detection in lakefile
- ``analyse_lake``: per-lake verdict (status ok/partial/cold/absent/no_mathlib_dep,
  cache dedup via realpath, floor threshold)

Builds synthetic lake trees under ``tmp_path`` (no real .lake/packages, no
junctions, no network). Zero source churn.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from check_mathlib_cache import (  # noqa: E402
    MATHLIB_OLEAN_FLOOR,
    SKIP_DIRS,
    analyse_lake,
    count_oleans,
    declares_mathlib,
    find_lakes,
    main,
)


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

def _write(path: Path, text: str = "") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _make_lake(root: Path, name: str, lakefile: str = "lakefile.lean",
               body: str = "") -> Path:
    lake = root / name
    _write(lake / lakefile, body)
    return lake


# ---------------------------------------------------------------------------
# constants
# ---------------------------------------------------------------------------

def test_floor_is_1000():
    assert MATHLIB_OLEAN_FLOOR == 1000


def test_skip_dirs_excludes_build_dirs():
    for d in (".git", "node_modules", ".lake", ".mathlib-cache", "packages"):
        assert d in SKIP_DIRS


# ---------------------------------------------------------------------------
# declares_mathlib
# ---------------------------------------------------------------------------

class TestDeclaresMathlib:
    def test_lean_with_mathlib(self, tmp_path):
        lake = _make_lake(tmp_path, "L", body='require mathlib from git')
        assert declares_mathlib(lake) is True

    def test_case_insensitive(self, tmp_path):
        lake = _make_lake(tmp_path, "L", body='require MathLib from git')
        assert declares_mathlib(lake) is True

    def test_toml_lakefile(self, tmp_path):
        lake = _make_lake(tmp_path, "L", lakefile="lakefile.toml",
                          body='[[require]]\nname = "mathlib"')
        assert declares_mathlib(lake) is True

    def test_no_mathlib_dep(self, tmp_path):
        lake = _make_lake(tmp_path, "L", body='require batteries from git')
        assert declares_mathlib(lake) is False

    def test_no_lakefile(self, tmp_path):
        # Neither lakefile.lean nor lakefile.toml present.
        (tmp_path / "L").mkdir()
        assert declares_mathlib(tmp_path / "L") is False

    def test_mathlib_in_comment_still_detected(self, tmp_path):
        # The check is a plain substring match (content-based, not parsed) --
        # a comment mentioning mathlib counts. Pin the real behavior.
        lake = _make_lake(tmp_path, "L", body='-- TODO add mathlib dependency')
        assert declares_mathlib(lake) is True


# ---------------------------------------------------------------------------
# count_oleans
# ---------------------------------------------------------------------------

class TestCountOleans:
    def test_empty_dir(self, tmp_path):
        assert count_oleans(tmp_path) == 0

    def test_counts_only_olean(self, tmp_path):
        _write(tmp_path / "A.olean")
        _write(tmp_path / "B.olean")
        _write(tmp_path / "C.txt")
        _write(tmp_path / "D.lean")
        assert count_oleans(tmp_path) == 2

    def test_recursive(self, tmp_path):
        _write(tmp_path / "a.olean")
        _write(tmp_path / "sub" / "b.olean")
        _write(tmp_path / "sub" / "deep" / "c.olean")
        assert count_oleans(tmp_path) == 3

    def test_extension_exact(self, tmp_path):
        # ".oleanfoo" is not ".olean".
        _write(tmp_path / "x.oleanfoo")
        _write(tmp_path / "y.olean")
        assert count_oleans(tmp_path) == 1


# ---------------------------------------------------------------------------
# find_lakes
# ---------------------------------------------------------------------------

class TestFindLakes:
    def test_finds_lean_lakefile(self, tmp_path):
        _make_lake(tmp_path, "L1")
        assert find_lakes(tmp_path) == [tmp_path / "L1"]

    def test_finds_toml_lakefile(self, tmp_path):
        _make_lake(tmp_path, "L1", lakefile="lakefile.toml")
        assert find_lakes(tmp_path) == [tmp_path / "L1"]

    def test_sorted_multiple(self, tmp_path):
        _make_lake(tmp_path, "B")
        _make_lake(tmp_path, "A")
        assert find_lakes(tmp_path) == [tmp_path / "A", tmp_path / "B"]

    def test_skips_skip_dirs(self, tmp_path):
        # A lakefile buried under .lake (a SKIP_DIR) must not be found.
        _write(tmp_path / ".lake" / "packages" / "mathlib" / "lakefile.lean")
        assert find_lakes(tmp_path) == []

    def test_excludes_claude_worktrees_by_default(self, tmp_path):
        _write(tmp_path / ".claude" / "worktrees" / "wt1" / "proj" / "lakefile.lean")
        assert find_lakes(tmp_path) == []

    def test_includes_claude_worktrees_when_asked(self, tmp_path):
        lake = tmp_path / ".claude" / "worktrees" / "wt1" / "proj"
        _write(lake / "lakefile.lean")
        assert lake in find_lakes(tmp_path, include_worktrees=True)

    def test_no_lakes_returns_empty(self, tmp_path):
        _write(tmp_path / "notebook.ipynb")
        assert find_lakes(tmp_path) == []


# ---------------------------------------------------------------------------
# analyse_lake
# ---------------------------------------------------------------------------

class TestAnalyseLake:
    def test_no_mathlib_dep(self, tmp_path):
        lake = _make_lake(tmp_path, "L", body='require batteries from git')
        r = analyse_lake(lake, {})
        assert r["declares_mathlib"] is False
        assert r["status"] == "no_mathlib_dep"
        assert r["oleans"] == 0

    def test_absent_when_declared_but_missing(self, tmp_path):
        lake = _make_lake(tmp_path, "L", body='require mathlib from git')
        # no .lake/packages/mathlib dir created
        r = analyse_lake(lake, {})
        assert r["declares_mathlib"] is True
        assert r["status"] == "absent"
        assert r["oleans"] == 0

    def test_cold_when_zero_oleans(self, tmp_path):
        lake = _make_lake(tmp_path, "L", body='require mathlib from git')
        _write(lake / ".lake" / "packages" / "mathlib" / ".gitkeep")
        r = analyse_lake(lake, {})
        assert r["status"] == "cold"
        assert r["oleans"] == 0

    def test_ok_when_above_floor(self, tmp_path):
        lake = _make_lake(tmp_path, "L", body='require mathlib from git')
        mlib = lake / ".lake" / "packages" / "mathlib"
        for i in range(MATHLIB_OLEAN_FLOOR):
            _write(mlib / f"f{i}.olean")
        r = analyse_lake(lake, {})
        assert r["status"] == "ok"
        assert r["oleans"] == MATHLIB_OLEAN_FLOOR

    def test_partial_when_between_zero_and_floor(self, tmp_path):
        lake = _make_lake(tmp_path, "L", body='require mathlib from git')
        mlib = lake / ".lake" / "packages" / "mathlib"
        for i in range(10):
            _write(mlib / f"f{i}.olean")
        r = analyse_lake(lake, {})
        assert r["status"] == "partial"
        assert r["oleans"] == 10

    def test_cache_dedups_by_realpath(self, tmp_path):
        # Two lakes whose mathlib realpath resolves identically (here: the same
        # physical dir) share one count via the cache -> computed once.
        cache = {}
        shared = tmp_path / "shared_mathlib"
        _write(shared / "x.olean")
        for name in ("L1", "L2"):
            lake = _make_lake(tmp_path, name, body='require mathlib from git')
            mlib = lake / ".lake" / "packages" / "mathlib"
            mlib.parent.mkdir(parents=True, exist_ok=True)
            # symlink so realpath converges on the shared store
            try:
                mlib.symlink_to(shared, target_is_directory=True)
            except (OSError, NotImplementedError):
                pytest.skip("symlinks not supported on this platform")
            r = analyse_lake(lake, cache)
            assert r["oleans"] == 1
        # cache holds exactly one entry for the shared realpath
        assert len(cache) == 1

    def test_result_carries_lake_path(self, tmp_path):
        lake = _make_lake(tmp_path, "MyLake", body='require mathlib from git')
        r = analyse_lake(lake, {})
        assert str(lake) == r["lake"]

    def test_junction_flagged_in_result(self, tmp_path):
        """Le cas fondateur (.10066 tranche 4) : une junction/symlink vers un
        cache sain doit populater ``result["junction"]`` ET laisser ``analyse_lake``
        compter les oleans du store reel (pas 0). Sur POSIX, ``os.symlink`` joue
        le role de la junction Windows ; le test du contrat (flag + traverse
        via realpath) suffit, le mecanisme de la junction etant absorbe par
        ``os.path.realpath()`` (commentaire canonique : ``islink()`` est False
        sur une junction Windows, c'est la divergence de chemin qui revele).
        """
        store = tmp_path / "store"
        store.mkdir(parents=True)
        for i in range(MATHLIB_OLEAN_FLOOR + 1):
            _write(store / f"f{i}.olean")

        lake = _make_lake(tmp_path, "L", body='require mathlib from git')
        mlib = lake / ".lake" / "packages" / "mathlib"
        mlib.parent.mkdir(parents=True, exist_ok=True)
        try:
            mlib.symlink_to(store, target_is_directory=True)
        except (OSError, NotImplementedError):
            pytest.skip("symlinks not supported on this platform")

        r = analyse_lake(lake, {})
        assert r["status"] == "ok", r
        assert r["oleans"] == MATHLIB_OLEAN_FLOOR + 1, r
        assert r["junction"] is True, r


# ---------------------------------------------------------------------------
# main() — exit codes, --strict, JSON output
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# main() — exit codes, --strict, JSON output
# ---------------------------------------------------------------------------

class TestMain:
    def test_advisory_exits_zero_with_cold_lake(self, tmp_path):
        """Sort 0 par defaut meme avec un lake froid (advisory)."""
        repo = tmp_path / "repo"
        repo.mkdir()
        _write(repo / ".git" / "HEAD", "ref: refs/heads/main")
        lake = _make_lake(repo, "alpha", body='require mathlib from git')
        (lake / ".lake" / "packages" / "mathlib").mkdir(parents=True)

        assert main(["--repo-path", str(repo)]) == 0

    def test_strict_exits_one_with_cold_lake(self, tmp_path):
        """Avec --strict, un lake froid force la sortie 1."""
        repo = tmp_path / "repo"
        repo.mkdir()
        _write(repo / ".git" / "HEAD", "ref: refs/heads/main")
        lake = _make_lake(repo, "alpha", body='require mathlib from git')
        (lake / ".lake" / "packages" / "mathlib").mkdir(parents=True)

        assert main(["--repo-path", str(repo), "--strict"]) == 1

    def test_json_out_writes_results(self, tmp_path):
        """Si --json-out, ecrit le rapport JSON (results[{status}] coherents)."""
        import json

        repo = tmp_path / "repo"
        repo.mkdir()
        _write(repo / ".git" / "HEAD", "ref: refs/heads/main")
        lake = _make_lake(repo, "alpha", body='require mathlib from git')
        (lake / ".lake" / "packages" / "mathlib").mkdir(parents=True)

        out = tmp_path / "out.json"
        argv = ["--repo-path", str(repo), "--json-out", str(out)]
        assert main(argv) == 0
        assert main(argv + ["--strict"]) == 1

        payload = json.loads(out.read_text(encoding="utf-8"))
        assert [r["status"] for r in payload["results"]] == ["cold"], payload

    def test_bad_repo_path_exits_2(self, tmp_path):
        """Un --repo-path qui n'est pas une racine git (.git absent) -> exit 2."""
        assert main(["--repo-path", str(tmp_path / "nope")]) == 2
