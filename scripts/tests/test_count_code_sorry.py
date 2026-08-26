#!/usr/bin/env python3
"""Unit tests for count_code_sorry.py lake discovery (#13137).

The discovery anchored only on ``lakefile.lean`` (plus the legacy ``*_lean``
name fallback), so lakes configured with ``lakefile.toml`` and an arbitrary
name -- ``lean_game_defs`` and ``lean_game_defs_ext`` -- were silently absent
from the global denominator. These tests pin the false negatives that
motivated the fix:

- a ``*_lean`` dir with ``lakefile.lean`` (always worked, regression guard);
- an arbitrary-named dir with ``lakefile.toml`` (the fix);
- the two real GameTheory roots against the live repo (integration);
- a root carrying BOTH anchors deduplicated to one entry;
- excluded paths (``.lake/``, ``_peters/``, ``reference_docs/``) stay out;
- ``--lake`` explicit mode still scans a toml lake passed by hand.

Run: python -m pytest scripts/tests/test_count_code_sorry.py
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "lean"))

import count_code_sorry as ccs  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[2]


def make_lake(tmp_path: Path, name: str, anchor: str,
              with_lean: bool = True) -> Path:
    """Lay out a minimal fake lake named ``name`` anchored by ``anchor``."""
    root = tmp_path / name
    root.mkdir(parents=True)
    (root / anchor).write_text("/* fixture */\n", encoding="utf-8")
    if with_lean:
        (root / "Fake.lean").write_text(
            "theorem fake_ok : True := trivial\n", encoding="utf-8")
    return root


def names(paths: list[Path]) -> set[str]:
    return {p.name for p in paths}


# --- anchors -----------------------------------------------------------------

def test_lean_suffix_with_lakefile_lean_discovered(tmp_path):
    make_lake(tmp_path, "foo_lean", "lakefile.lean")
    assert names(ccs.discover_lakes(tmp_path)) == {"foo_lean"}


def test_arbitrary_name_with_lakefile_toml_discovered(tmp_path):
    """THE #13137 regression: toml anchor + arbitrary name was invisible."""
    make_lake(tmp_path, "lean_game_defs_like", "lakefile.toml")
    assert names(ccs.discover_lakes(tmp_path)) == {"lean_game_defs_like"}


def test_toml_anchor_and_lean_suffix_both_discovered(tmp_path):
    make_lake(tmp_path, "a_lean", "lakefile.lean")
    make_lake(tmp_path, "b_defs", "lakefile.toml")
    assert names(ccs.discover_lakes(tmp_path)) == {"a_lean", "b_defs"}


def test_root_with_both_anchors_counted_once(tmp_path):
    """A root carrying lakefile.lean AND lakefile.toml is one lake, not two."""
    root = tmp_path / "dual_lean"
    root.mkdir()
    (root / "lakefile.lean").write_text("", encoding="utf-8")
    (root / "lakefile.toml").write_text("", encoding="utf-8")
    (root / "Fake.lean").write_text("", encoding="utf-8")
    lakes = ccs.discover_lakes(tmp_path)
    assert len(lakes) == 1
    assert lakes[0].resolve() == root.resolve()


# --- exclusions --------------------------------------------------------------

def test_dot_lake_packages_excluded(tmp_path):
    """A vendored lake under .lake/ is a dependency, not an own lake."""
    make_lake(tmp_path / ".lake" / "packages" / "Mathlib",
              "Mathlib", "lakefile.lean")
    assert ccs.discover_lakes(tmp_path) == []


def test_peters_and_reference_docs_excluded(tmp_path):
    make_lake(tmp_path / "_peters" / "ext", "ext", "lakefile.lean")
    make_lake(tmp_path / "agent_tests" / "reference_docs" / "sm",
              "upstream", "lakefile.toml")
    assert ccs.discover_lakes(tmp_path) == []


# --- real regressions (integration against the live repo) --------------------

def test_real_game_defs_lakes_in_global_discovery():
    """lean_game_defs and lean_game_defs_ext are the two real #13137 misses."""
    nb_root = REPO_ROOT / "MyIA.AI.Notebooks"
    if not nb_root.is_dir():
        pytest.skip("repo layout not available (running outside checkout)")
    found = names(ccs.discover_lakes(nb_root))
    assert "lean_game_defs" in found
    assert "lean_game_defs_ext" in found


# --lake explicit mode ----------------------------------------------------------

def test_explicit_lake_scan_on_toml_lake(tmp_path, capsys):
    """--lake keeps working when handed a toml lake by hand (pre-fix path)."""
    lake = make_lake(tmp_path, "explicit_defs", "lakefile.toml")
    rc = ccs.main(["--repo", str(tmp_path), "--lake", str(lake), "--json",
                   "--no-vacuous"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "explicit_defs" in out
