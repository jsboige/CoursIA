#!/usr/bin/env python3
"""Tests for check_lean_inventory.py (issue #21765).

Dual-mode: runnable directly (``python scripts/lean/tests/test_check_lean_inventory.py``)
or under pytest (auto-collected by scripts-tests.yml).

The gate keeps ``MyIA.AI.Notebooks/GameTheory/LEAN_INVENTORY.md`` in sync with
the ``lean_lib`` declarations of the GameTheory lakes. The map was reconciled
on 2026-08-26 and never re-derived since: 9 libraries declared after that date
(``Abstraction``, ``ProgramGames``, ``StackelbergBilevel`` and the six
``Approval*`` libraries of ``social_choice_lean_peters``) never reached it --
20 proof files invisible to any reader of the map.

What these tests hold:

1. the real repository is coherent -- the map names every declared library
   (this is the test that turns the gate into a CI gate);
2. the parsers read both lakefile dialects, and do not count a library named
   in a comment;
3. the map must name a library by **code span** -- a library mentioned in prose
   only is not a documented library;
4. the gate can fail: a synthetic lake whose library the map does not name is
   reported as a drift (the control positive -- a detector that has never been
   seen red is not a detector).
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_lean_inventory as cli  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[3]


def _write_lake(root: Path, name: str, libs: str) -> Path:
    """Create a minimal lake with a lakefile.lean declaring ``libs``."""
    lake = root / name
    lake.mkdir(parents=True, exist_ok=True)
    (lake / "lakefile.lean").write_text(libs, encoding="utf-8")
    return lake


def test_repo_inventory_covers_every_declared_library():
    """Control positive on the real repository: the map is coherent."""
    report = cli.check(REPO_ROOT)
    assert report["verdict"] != "ERROR", report.get("error")
    assert report["declared_libs"] >= 21, report
    assert report["missing_from_inventory"] == [], report["missing_from_inventory"]
    assert report["verdict"] == "OK"


def test_parse_lean_libs_reads_bare_and_quoted_names():
    text = """
lean_lib StableMarriage where
  globs := #[`StableMarriage.*, `StableMarriage_en]

lean_lib «CGTTour» where
  globs := #[`CGTTour, `CGTTour_en]

lean_lib "Assignment" where
  globs := #[`Assignment.*]
"""
    assert cli.parse_lean_libs(text) == ["StableMarriage", "CGTTour", "Assignment"]


def test_parse_lean_libs_ignores_libraries_named_in_comments():
    text = """
-- c.306 (po-2026) : ajout d'un second `lean_lib CooperativeGames` qui suit
/- une mention historique de `lean_lib Ancien` dans un bloc -/
lean_lib SocialChoice where
  globs := #[`SocialChoice.*]
"""
    assert cli.parse_lean_libs(text) == ["SocialChoice"]


def test_parse_lean_libs_dedupes_a_name_declared_twice():
    text = """
lean_lib RepeatedGames where
  globs := #[`RepeatedGames.*]

lean_lib RepeatedGames where
  globs := #[`RepeatedGames_en]
"""
    assert cli.parse_lean_libs(text) == ["RepeatedGames"]


def test_parse_toml_libs_reads_the_table_dialect():
    text = """
name = "lean_game_defs"

[[lean_lib]]
name = "LeanGameDefs"
roots = ["Basic", "Nash"]
"""
    assert cli.parse_toml_libs(text) == ["LeanGameDefs"]


def test_inventory_mentions_requires_a_code_span():
    inventory = "Le module `Abstraction/` est documente.\n"
    assert cli.inventory_mentions(inventory, "Abstraction") is True
    assert cli.inventory_mentions(inventory, "ProgramGames") is False

    prose_only = "Le coeur du travail est le module Abstraction, bien documente.\n"
    assert cli.inventory_mentions(prose_only, "Abstraction") is False


def test_inventory_mentions_accepts_the_documented_spellings():
    for span in ("`ApprovalDefs`", "`ApprovalDefs_en.lean`", "`ApprovalDefs/`"):
        assert cli.inventory_mentions(span, "ApprovalDefs") is True
    # A different library that merely starts with the same letters does not count.
    assert cli.inventory_mentions("`ApprovalQuota`", "ApprovalDefs") is False


def test_check_reports_a_library_the_map_does_not_name(tmp_path):
    """The control positive: the gate CAN go red."""
    root = tmp_path / "MyIA.AI.Notebooks" / "GameTheory"
    _write_lake(root, "game_theory_lean", "lean_lib Abstraction where\n  globs := #[`Abstraction.*]\n")
    inventory = root / "LEAN_INVENTORY.md"
    inventory.write_text("# Carte\n\nAucun module abstrait ici.\n", encoding="utf-8")

    report = cli.check(tmp_path, "MyIA.AI.Notebooks/GameTheory/LEAN_INVENTORY.md",
                       "MyIA.AI.Notebooks/GameTheory")
    assert report["verdict"] == "DRIFT"
    assert report["findings"] == 1
    assert report["missing_from_inventory"][0]["lib"] == "Abstraction"
    assert report["missing_from_inventory"][0]["lake"].endswith("game_theory_lean")


def test_check_is_green_once_the_map_names_the_library(tmp_path):
    root = tmp_path / "MyIA.AI.Notebooks" / "GameTheory"
    _write_lake(root, "game_theory_lean", "lean_lib Abstraction where\n  globs := #[`Abstraction.*]\n")
    inventory = root / "LEAN_INVENTORY.md"
    inventory.write_text("# Carte\n\n| `Abstraction/` | 0 | ... |\n", encoding="utf-8")

    report = cli.check(tmp_path, "MyIA.AI.Notebooks/GameTheory/LEAN_INVENTORY.md",
                       "MyIA.AI.Notebooks/GameTheory")
    assert report["verdict"] == "OK"
    assert report["findings"] == 0


def test_check_reports_an_error_when_the_map_is_absent(tmp_path):
    report = cli.check(tmp_path, "MyIA.AI.Notebooks/GameTheory/LEAN_INVENTORY.md",
                       "MyIA.AI.Notebooks/GameTheory")
    assert report["verdict"] == "ERROR"


def test_main_exit_code_follows_the_verdict(tmp_path, capsys):
    root = tmp_path / "MyIA.AI.Notebooks" / "GameTheory"
    _write_lake(root, "game_theory_lean", "lean_lib Abstraction where\n  globs := #[`Abstraction.*]\n")
    inventory = root / "LEAN_INVENTORY.md"
    inventory.write_text("# Carte\n\nAucun module abstrait ici.\n", encoding="utf-8")

    rc = cli.main(["--repo-root", str(tmp_path),
                   "--inventory", "MyIA.AI.Notebooks/GameTheory/LEAN_INVENTORY.md",
                   "--root", "MyIA.AI.Notebooks/GameTheory"])
    assert rc == 1
    out = capsys.readouterr().out
    assert "MISSING_FROM_INVENTORY" in out
    assert "Abstraction" in out


if __name__ == "__main__":
    sys.exit(__import__("pytest").main([__file__, "-v"]))
