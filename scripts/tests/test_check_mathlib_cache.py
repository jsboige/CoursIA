#!/usr/bin/env python3
"""Tests de check_mathlib_cache.py — arborescences reelles, junctions reelles.

Les fixtures creent de vrais repertoires (et, sur Windows, de vraies junctions via
`mklink /J`) plutot que de simuler `os.walk` : le faux negatif que l'outil doit
eviter — un cache sain compte a 0 parce que l'outil ne traverse pas le lien —
n'apparait que sur une vraie junction.

    py scripts/tests/test_check_mathlib_cache.py
    npx pytest scripts/tests/test_check_mathlib_cache.py
"""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "lean"))

import check_mathlib_cache as mod  # noqa: E402


def make_repo(root: Path) -> Path:
    repo = root / "repo"
    (repo / ".git").mkdir(parents=True)
    return repo


def make_lake(repo: Path, name: str, *, mathlib_dep: bool = True) -> Path:
    lake = repo / name
    lake.mkdir(parents=True, exist_ok=True)
    body = 'require mathlib from git "https://github.com/leanprover-community/mathlib4"\n'
    (lake / "lakefile.lean").write_text(body if mathlib_dep else "package foo\n",
                                        encoding="utf-8")
    return lake


def fill_oleans(target: Path, count: int) -> None:
    build = target / ".lake" / "build" / "lib" / "lean"
    build.mkdir(parents=True, exist_ok=True)
    for i in range(count):
        (build / f"Mod{i}.olean").write_bytes(b"\x00")


def try_junction(link: Path, target: Path) -> bool:
    """Cree une junction Windows. Rend False si indisponible (non-Windows)."""
    if os.name != "nt":
        return False
    link.parent.mkdir(parents=True, exist_ok=True)
    proc = subprocess.run(["cmd", "/c", "mklink", "/J", str(link), str(target)],
                          capture_output=True, text=True)
    return proc.returncode == 0


# --------------------------------------------------------------------------- tests

def test_healthy_cache_is_ok(root: Path) -> None:
    repo = make_repo(root)
    lake = make_lake(repo, "alpha")
    fill_oleans(lake / ".lake" / "packages" / "mathlib", mod.MATHLIB_OLEAN_FLOOR + 5)

    res = mod.analyse_lake(lake, {})

    assert res["status"] == "ok", res
    assert res["oleans"] == mod.MATHLIB_OLEAN_FLOOR + 5, res


def test_empty_mathlib_dir_is_cold(root: Path) -> None:
    """Repertoire present mais vide = vrai cold, distinct d'une junction mal lue."""
    repo = make_repo(root)
    lake = make_lake(repo, "alpha")
    (lake / ".lake" / "packages" / "mathlib").mkdir(parents=True)

    res = mod.analyse_lake(lake, {})

    assert res["status"] == "cold", res
    assert res["oleans"] == 0, res


def test_partial_cache_is_not_ok(root: Path) -> None:
    repo = make_repo(root)
    lake = make_lake(repo, "alpha")
    fill_oleans(lake / ".lake" / "packages" / "mathlib", 3)

    assert mod.analyse_lake(lake, {})["status"] == "partial"


def test_absent_vs_no_dependency(root: Path) -> None:
    """Pas de mathlib installe : 'absent' si le lakefile le declare, sinon ignore."""
    repo = make_repo(root)
    declares = mod.analyse_lake(make_lake(repo, "alpha"), {})
    plain = mod.analyse_lake(make_lake(repo, "beta", mathlib_dep=False), {})

    assert declares["status"] == "absent", declares
    assert plain["status"] == "no_mathlib_dep", plain


def test_junction_is_traversed_and_flagged(root: Path) -> None:
    """Le cas fondateur : une junction vers un cache sain ne doit PAS compter 0."""
    repo = make_repo(root)
    store = repo / ".mathlib-cache" / "toolchain" / "mathlib"
    fill_oleans(store, mod.MATHLIB_OLEAN_FLOOR + 1)

    lake = make_lake(repo, "alpha")
    link = lake / ".lake" / "packages" / "mathlib"
    if not try_junction(link, store):
        print("SKIP  test_junction_is_traversed_and_flagged (junctions indisponibles)")
        return

    res = mod.analyse_lake(lake, {})

    assert res["status"] == "ok", res
    assert res["oleans"] == mod.MATHLIB_OLEAN_FLOOR + 1, res
    assert res["junction"] is True, res
    assert Path(res["realpath"]).name == "mathlib", res


def test_shared_store_counted_once(root: Path) -> None:
    """Deux lakes junctionnes vers le meme store = un seul comptage physique."""
    repo = make_repo(root)
    store = repo / ".mathlib-cache" / "toolchain" / "mathlib"
    fill_oleans(store, mod.MATHLIB_OLEAN_FLOOR + 2)

    cache: dict[str, int] = {}
    linked = 0
    for name in ("alpha", "beta"):
        lake = make_lake(repo, name)
        if try_junction(lake / ".lake" / "packages" / "mathlib", store):
            linked += 1
            mod.analyse_lake(lake, cache)

    if linked < 2:
        print("SKIP  test_shared_store_counted_once (junctions indisponibles)")
        return
    assert len(cache) == 1, cache


def test_find_lakes_excludes_worktrees_by_default(root: Path) -> None:
    repo = make_repo(root)
    make_lake(repo, "alpha")
    make_lake(repo, ".claude/worktrees/wt1/beta")

    assert [p.name for p in mod.find_lakes(repo)] == ["alpha"]
    assert len(mod.find_lakes(repo, include_worktrees=True)) == 2


def test_main_advisory_then_strict(root: Path) -> None:
    """Sort 0 par defaut meme avec un lake froid ; 1 avec --strict."""
    repo = make_repo(root)
    lake = make_lake(repo, "alpha")
    (lake / ".lake" / "packages" / "mathlib").mkdir(parents=True)

    out = root / "out.json"
    argv = ["--repo-path", str(repo), "--json-out", str(out)]

    assert mod.main(argv) == 0
    assert mod.main(argv + ["--strict"]) == 1

    import json
    payload = json.loads(out.read_text(encoding="utf-8"))
    assert [r["status"] for r in payload["results"]] == ["cold"], payload


def test_bad_repo_path_exits_2(root: Path) -> None:
    assert mod.main(["--repo-path", str(root / "nope")]) == 2


# --------------------------------------------------------------------- harnais

try:
    import pytest

    @pytest.fixture()
    def root(tmp_path: Path) -> Path:  # noqa: D103
        return tmp_path
except ImportError:  # pragma: no cover
    pass


def run_direct() -> int:
    tests = [(n, f) for n, f in sorted(globals().items())
             if n.startswith("test_") and callable(f)]
    failures = 0
    for name, fn in tests:
        with tempfile.TemporaryDirectory() as tmp:
            try:
                fn(Path(tmp))
                print(f"PASS  {name}")
            except Exception as exc:  # noqa: BLE001
                failures += 1
                print(f"FAIL  {name}: {exc}")
    print(f"\n{len(tests) - failures}/{len(tests)} tests passes")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(run_direct())
