#!/usr/bin/env python3
"""Tests for check_target_coverage.py (#8782 advisory proof-integrity coverage).

Dual-mode: runnable directly (``python scripts/lean/tests/test_check_target_coverage.py``)
or under pytest (auto-collected by scripts-tests.yml on any ``scripts/**`` change).

Locks the advisory contract of the conway proof-integrity gate coverage check:
  - exit 0 unconditionally (advisory, never blocks CI);
  - blind-spot detection (compiled-but-ungated modules);
  - phantom detection (gated-but-no-source modules);
  - lib-root scoping (``<lib>/`` subdir + ``<lib>.lean`` umbrella + ``<lib>_en.lean`` sibling);
  - maximal walk excludes build cache / lakefile / toolchain.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_target_coverage import (  # noqa: E402
    _EXCLUDE_TOP_DIRS,
    discover_modules,
    main,
    parse_target_modules,
)


# ---------------------------------------------------------------------------
# Fixtures — a minimal fake lake mirroring the conway_lean layout
# ---------------------------------------------------------------------------

def _make_lake(tmp_path: Path, lib: str = "Conway") -> Path:
    """Build a fake lake: ``<lib>/`` subtree + umbrella ``<lib>.lean`` +
    ``<lib>_en.lean`` sibling, plus excluded build cache / lakefile / toolchain."""
    lake = tmp_path / "fake_lake"
    # subdir modules (the standard ``.submodules <lib>`` tree)
    (lake / lib / "Life").mkdir(parents=True)
    (lake / lib / "Life" / "GridCanonical.lean").write_text("-- a\n", encoding="utf-8")
    (lake / lib / "KochenSpecker.lean").write_text("-- b\n", encoding="utf-8")
    # umbrella root module (compiled by the glob, NOT under <lib>/)
    (lake / f"{lib}.lean").write_text("-- umbrella\n", encoding="utf-8")
    # _en i18n sibling (also compiled by the glob)
    (lake / f"{lib}_en.lean").write_text("-- en mirror\n", encoding="utf-8")
    # excluded: .lake build cache must never count as a module
    (lake / ".lake" / "build" / "lib").mkdir(parents=True)
    (lake / ".lake" / "build" / "lib" / "Junk.lean").write_text("-- cache\n", encoding="utf-8")
    # lakefile + toolchain are not modules
    (lake / "lakefile.lean").write_text("-- lakefile\n", encoding="utf-8")
    (lake / "lean-toolchain").write_text("leanprover/lean4:v4.31.0-rc1\n", encoding="utf-8")
    return lake


# ---------------------------------------------------------------------------
# discover_modules — lib-root scoped walk
# ---------------------------------------------------------------------------

class TestDiscoverScoped:
    def test_includes_subdir_umbrella_and_sibling(self, tmp_path):
        lake = _make_lake(tmp_path)
        mods = discover_modules(lake, "Conway")
        assert "Conway.Life.GridCanonical" in mods
        assert "Conway.KochenSpecker" in mods
        assert "Conway" in mods          # umbrella <lib>.lean
        assert "Conway_en" in mods       # <lib>_en.lean sibling

    def test_excludes_build_cache_and_lakefile(self, tmp_path):
        lake = _make_lake(tmp_path)
        mods = discover_modules(lake, "Conway")
        assert not any("Junk" in m or ".lake" in m for m in mods)
        assert "lakefile" not in mods
        assert "lean-toolchain" not in mods

    def test_missing_lib_root_returns_empty(self, tmp_path):
        lake = tmp_path / "empty_lake"
        lake.mkdir()
        (lake / "Foo.lean").write_text("-- x\n", encoding="utf-8")
        # lib_root "Bar" has no dir, no umbrella, no sibling -> nothing
        assert discover_modules(lake, "Bar") == set()


# ---------------------------------------------------------------------------
# discover_modules — maximal walk (no lib-root)
# ---------------------------------------------------------------------------

class TestDiscoverMaximal:
    def test_includes_every_lean_outside_excluded(self, tmp_path):
        lake = _make_lake(tmp_path)
        mods = discover_modules(lake, None)
        assert "Conway.Life.GridCanonical" in mods
        assert "Conway" in mods
        assert "Conway_en" in mods
        # build cache + lakefile + toolchain still excluded
        assert not any("Junk" in m for m in mods)
        assert not any("lakefile" in m or "lean-toolchain" in m for m in mods)

    def test_excluded_top_dirs_contract(self):
        """Documents the build-cache / VCS / tooling dirs that never hold modules."""
        for d in (".lake", ".git", "node_modules", ".venv"):
            assert d in _EXCLUDE_TOP_DIRS


# ---------------------------------------------------------------------------
# parse_target_modules
# ---------------------------------------------------------------------------

class TestParseTargets:
    def test_comma_split(self):
        assert parse_target_modules("A.B,A.C") == {"A.B", "A.C"}

    def test_whitespace_stripped(self):
        assert parse_target_modules(" A.B ,  A.C ") == {"A.B", "A.C"}

    def test_empties_filtered(self):
        assert parse_target_modules("A.B,, ,A.C") == {"A.B", "A.C"}
        assert parse_target_modules("") == set()


# ---------------------------------------------------------------------------
# CLI advisory contract — exit 0 always (never blocks CI)
# ---------------------------------------------------------------------------

class TestAdvisoryExitZero:
    def test_missing_project_path_exits_zero(self, capsys):
        rc = main(["--project-path", "does/not/exist", "--target-modules", "A"])
        assert rc == 0
        out = capsys.readouterr().out
        assert "not found" in out

    def test_phantom_target_exits_zero(self, tmp_path, capsys):
        lake = _make_lake(tmp_path)
        rc = main([
            "--project-path", str(lake),
            "--target-modules", "Conway.KochenSpecker,Conway.Ghost",
            "--lib-root", "Conway",
        ])
        assert rc == 0
        out = capsys.readouterr().out
        assert "PHANTOM" in out
        assert "Conway.Ghost" in out

    def test_blind_spot_exits_zero_with_note(self, tmp_path, capsys):
        lake = _make_lake(tmp_path)
        rc = main([
            "--project-path", str(lake),
            "--target-modules", "Conway.KochenSpecker",  # gate 1 of 4 compiled
            "--lib-root", "Conway",
            "--name", "fake",
        ])
        assert rc == 0
        out = capsys.readouterr().out
        assert "BLIND SPOT" in out
        # the advisory note that explains a green-but-hors-cible gate
        assert "hors-cible" in out or "#8782" in out

    def test_full_coverage_reports_ok(self, tmp_path, capsys):
        # every compiled module is targeted -> no blind spot, no phantom
        lake = _make_lake(tmp_path)
        all_mods = discover_modules(lake, "Conway")
        rc = main([
            "--project-path", str(lake),
            "--target-modules", ",".join(sorted(all_mods)),
            "--lib-root", "Conway",
        ])
        assert rc == 0
        out = capsys.readouterr().out
        assert "OK" in out
        assert "BLIND SPOT" not in out

    def test_coverage_pct_decreases_with_blind_spot(self, tmp_path, capsys):
        lake = _make_lake(tmp_path)
        # 4 compiled, 1 targeted -> 25.0 %
        main([
            "--project-path", str(lake),
            "--target-modules", "Conway.KochenSpecker",
            "--lib-root", "Conway",
            "--name", "pct",
        ])
        out = capsys.readouterr().out
        assert "25.0%" in out


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
