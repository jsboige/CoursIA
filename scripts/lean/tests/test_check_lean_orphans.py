#!/usr/bin/env python3
"""Tests for check_lean_orphans.py (#19015 strict gate for orphan .lean files).

Dual-mode: runnable directly (``python scripts/lean/tests/test_check_lean_orphans.py``)
or under pytest (auto-collected by scripts-tests.yml on any ``scripts/**`` change).

Locks the contract of the orphan gate:
  - parse lakefile with three glob flavours (``Name``, ``Name.*``, ``Name_en``);
  - recognise the ``.submodules `Name`` Lake DSL directive (synthetic marker);
  - exclude ``.lake/`` / ``_peters/`` / ``lakefile*`` / ``lean-toolchain`` from walk;
  - umbrella ``<Name>.lean`` at lake root is covered by ``Name.*`` glob;
  - import-reachability: a file ``import``-ed by a covered file is also covered;
  - default exit 0 (advisory); ``--strict`` flips to 1 on any orphan;
  - ``--exclude`` whitelists a known intentional orphan (e.g. skeleton aggregator);
  - instance #18786 (``ApprovalDefs.lean`` orphan on ``social_choice_lean_peters``)
    is caught by ``--strict`` (exit 1, ORPHAN list non-empty);
  - instance #18883 (knot_lean after fix) is clean (exit 0, no orphans).
"""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest

SCRIPT = Path(__file__).resolve().parent.parent / "check_lean_orphans.py"
sys.path.insert(0, str(SCRIPT.parent))
import check_lean_orphans  # noqa: E402


@pytest.fixture
def tmp_lake(tmp_path: Path) -> Path:
    """Build a tiny lake: 1 lib, 2 covered .lean, 1 orphan .lean."""
    lake = tmp_path / "mylake"
    lake.mkdir()
    (lake / "lakefile.lean").write_text(
        "import Lake\nopen Lake DSL\n\n"
        "package «mylake» where\n\n"
        "@[default_target]\nlean_lib «Foo» where\n"
        "  globs := #[`Foo, `Bar]\n"
    )
    (lake / "Foo.lean").write_text("namespace Foo\ndef x : Nat := 1\nend Foo\n")
    (lake / "Bar.lean").write_text("namespace Bar\ndef x : Nat := 1\nend Bar\n")
    (lake / "Baz.lean").write_text("namespace Baz\ndef x : Nat := 1\nend Baz\n")
    (lake / "lean-toolchain").write_text("leanprover/lean4:v4.10.0\n")
    return lake


def test_lakefile_parse_basic(tmp_lake: Path) -> None:
    libs = check_lean_orphans._read_libs_and_globs(
        (tmp_lake / "lakefile.lean").read_text()
    )
    assert libs == [("Foo", ["Foo", "Bar"])]


def test_covered_modules_umbrella(tmp_lake: Path) -> None:
    libs = check_lean_orphans._read_libs_and_globs(
        (tmp_lake / "lakefile.lean").read_text()
    )
    all_globs = [g for _, globs in libs for g in globs]
    covered = check_lean_orphans._covered_modules(tmp_lake, all_globs)
    assert (tmp_lake / "Foo.lean") in covered
    assert (tmp_lake / "Bar.lean") in covered
    assert (tmp_lake / "Baz.lean") not in covered  # orphan


def test_submodules_marker(tmp_path: Path) -> None:
    """The ``.submodules `Knots`` Lake DSL directive must be recognised.

    Faithful to Lake's native ``Glob.submodules n`` (strict prefix, the leaf
    ``Knots.lean`` is NOT covered; only ``n.isPrefixOf m && n != m``). The
    ``Knots_en`` plain token covers ``Knots_en.lean`` at the lake root.
    """
    lake = tmp_path / "knot"
    lake.mkdir()
    (lake / "lakefile.lean").write_text(
        "@[default_target]\nlean_lib «Knots» where\n"
        "  globs := #[.submodules `Knots, `Knots_en]\n"
    )
    (lake / "Knots.lean").write_text("namespace Knots\nend Knots\n")
    (lake / "Knots" / "Foo.lean").parent.mkdir()
    (lake / "Knots" / "Foo.lean").write_text("namespace Knots.Foo\nend\n")
    (lake / "Knots_en.lean").write_text("namespace Knots_en\nend Knots_en\n")
    libs = check_lean_orphans._read_libs_and_globs(
        (lake / "lakefile.lean").read_text()
    )
    all_globs = [g for _, globs in libs for g in globs]
    assert "__submodules__`Knots" in all_globs
    covered = check_lean_orphans._covered_modules(lake, all_globs)
    # ``.submodules `Knots`` is a STRICT-prefix glob: ``Knots.lean`` at the
    # lake root is NOT covered (would require ``Knots != Knots``).
    assert (lake / "Knots.lean") not in covered
    assert (lake / "Knots" / "Foo.lean") in covered
    # ``Knots_en`` is a plain token — covers ``Knots_en.lean`` at the root only.
    assert (lake / "Knots_en.lean") in covered


def test_default_no_globs_covers_root(tmp_path: Path) -> None:
    """Lake native default (no ``globs := #[...]``) builds ``<Name>.lean``.

    Regression for the adjoint reserve (c26): ``lean_lib Foo where`` (no globs
    clause) maps to ``roots = #[Foo], globs = roots.map Glob.one`` per
    ``LeanLibConfig.lean:30-46``. Treating it as ``globs = []`` would falsely
    report ``Foo.lean`` as orphan.
    """
    lake = tmp_path / "default_lib"
    lake.mkdir()
    (lake / "lakefile.lean").write_text(
        "lean_lib «Foo» where\n"
    )
    (lake / "Foo.lean").write_text("namespace Foo\nend Foo\n")
    (lake / "Bar.lean").write_text("namespace Bar\nend Bar\n")
    libs = check_lean_orphans._read_libs_and_globs(
        (lake / "lakefile.lean").read_text()
    )
    assert libs == [("Foo", ["Foo"])]  # Lake default applied
    all_globs = [g for _, globs in libs for g in globs]
    covered = check_lean_orphans._covered_modules(lake, all_globs)
    assert (lake / "Foo.lean") in covered
    assert (lake / "Bar.lean") not in covered  # Bar is genuinely orphan


def test_no_implicit_en_sibling(tmp_path: Path) -> None:
    r"""Plain token ``\`Foo`` does NOT implicitly cover ``Foo_en.lean``.

    Regression for the adjoint reserve (c26): Lake ``Glob.one Foo`` returns
    ``m == Foo`` only — no implicit i18n expansion. An earlier version of the
    helper added ``_en`` siblings, silently blanching ``Foo_en.lean`` whenever
    the FR token was declared without an explicit ``Foo_en`` token.
    """
    lake = tmp_path / "implicit_en"
    lake.mkdir()
    (lake / "lakefile.lean").write_text(
        "@[default_target]\nlean_lib «Foo» where\n"
        "  globs := #[`Foo]\n"
    )
    (lake / "Foo.lean").write_text("namespace Foo\nend Foo\n")
    (lake / "Foo_en.lean").write_text("namespace Foo_en\nend Foo_en\n")
    libs = check_lean_orphans._read_libs_and_globs(
        (lake / "lakefile.lean").read_text()
    )
    all_globs = [g for _, globs in libs for g in globs]
    covered = check_lean_orphans._covered_modules(lake, all_globs)
    assert (lake / "Foo.lean") in covered
    # CRITICAL — this is the regression we're guarding.
    assert (lake / "Foo_en.lean") not in covered


def test_and_submodules_covers_root_and_subdirs(tmp_path: Path) -> None:
    r"""``\`Foo.*`` desugars to ``Glob.andSubmodules \`Foo`` (non-strict prefix).

    Both ``Foo.lean`` at the lake root AND every ``Foo/X.lean`` for ``X != Foo``
    are covered. No implicit ``_en`` sibling.
    """


def test_globs_clause_skips_line_comments(tmp_path: Path) -> None:
    r"""``--`` line comments must not leak into the ``globs := #[...]`` parse.

    Regression c27: ``conway_cgt_lean/lakefile.lean:62`` carries an in-body
    example ``-- \`globs := #[`Foo, `Foo_en]`` -- the naive regex silently
    matched that example as the lib's globs instead of the real clause below.
    Stripping ``--[^\n]*`` before searching fixes it.
    """
    lake = tmp_path / "commented"
    lake.mkdir()
    (lake / "lakefile.lean").write_text(
        "@[default_target]\nlean_lib «Real» where\n"
        "  -- Verified in vitro: `globs := #[`Foo, `Foo_en]` compiles both .olean.\n"
        "  globs := #[`Real]\n"
    )
    (lake / "Real.lean").write_text("namespace Real\nend Real\n")
    (lake / "Foo.lean").write_text("namespace Foo\nend Foo\n")
    libs = check_lean_orphans._read_libs_and_globs(
        (lake / "lakefile.lean").read_text()
    )
    # The comment example must NOT pollute the parse -- ``Foo`` would otherwise
    # be silently added to ``Real``'s globs and ``Foo.lean`` would never appear
    # as an orphan.
    assert libs == [("Real", ["Real"])]
    lake = tmp_path / "and_sub"
    lake.mkdir()
    (lake / "lakefile.lean").write_text(
        "@[default_target]\nlean_lib «Foo» where\n"
        "  globs := #[`Foo.*]\n"
    )
    (lake / "Foo.lean").write_text("namespace Foo\nend Foo\n")
    (lake / "Foo" / "Bar.lean").parent.mkdir()
    (lake / "Foo" / "Bar.lean").write_text("namespace Foo.Bar\nend\n")
    (lake / "Foo_en" / "Bar.lean").parent.mkdir(parents=True)
    (lake / "Foo_en" / "Bar.lean").write_text("namespace Foo_en.Bar\nend\n")
    (lake / "Foo_en.lean").write_text("namespace Foo_en\nend Foo_en\n")
    libs = check_lean_orphans._read_libs_and_globs(
        (lake / "lakefile.lean").read_text()
    )
    all_globs = [g for _, globs in libs for g in globs]
    covered = check_lean_orphans._covered_modules(lake, all_globs)
    assert (lake / "Foo.lean") in covered  # non-strict prefix includes leaf
    assert (lake / "Foo" / "Bar.lean") in covered
    # The implicit ``_en`` sibling is NOT covered — must be declared explicitly.
    assert (lake / "Foo_en" / "Bar.lean") not in covered
    assert (lake / "Foo_en.lean") not in covered


def test_discover_excludes(tmp_lake: Path) -> None:
    (tmp_lake / ".lake" / "build").mkdir(parents=True)
    (tmp_lake / ".lake" / "build" / "X.lean").write_text("ignored\n")
    (tmp_lake / "_peters" / "Y.lean").parent.mkdir()
    (tmp_lake / "_peters" / "Y.lean").write_text("ignored\n")
    files = check_lean_orphans._discover_lean_files(tmp_lake)
    rels = {f.name for f in files}
    assert "X.lean" not in rels
    assert "Y.lean" not in rels
    assert "Foo.lean" in rels
    assert "lakefile.lean" not in rels
    assert "lean-toolchain" not in rels


def test_import_reachability(tmp_path: Path) -> None:
    """A file ``import``-ed by a covered file is also covered."""
    lake = tmp_path / "reach"
    lake.mkdir()
    (lake / "lakefile.lean").write_text(
        "@[default_target]\nlean_lib «A» where\n"
        "  globs := #[`A]\n"
    )
    (lake / "A.lean").write_text("import B\nnamespace A\nend A\n")
    (lake / "B.lean").write_text("namespace B\ndef x : Nat := 1\nend B\n")
    libs = check_lean_orphans._read_libs_and_globs(
        (lake / "lakefile.lean").read_text()
    )
    all_globs = [g for _, globs in libs for g in globs]
    covered = check_lean_orphans._covered_modules(lake, all_globs)
    all_lean = check_lean_orphans._discover_lean_files(lake)
    reachable = check_lean_orphans._imports_reachable_from(lake, covered, all_lean)
    assert (lake / "A.lean") in reachable
    assert (lake / "B.lean") in reachable  # via import


def test_default_advisory_exits_zero(tmp_lake: Path) -> None:
    """No --strict: orphans reported but exit 0."""
    rc = check_lean_orphans.main(
        [
            "--project-path", str(tmp_lake),
            "--lakefile", str(tmp_lake / "lakefile.lean"),
            "--name", "test",
        ]
    )
    assert rc == 0


def test_strict_exits_one_on_orphan(tmp_lake: Path) -> None:
    """--strict: orphan triggers exit 1 (acceptance gate #1 from #19015)."""
    rc = check_lean_orphans.main(
        [
            "--project-path", str(tmp_lake),
            "--lakefile", str(tmp_lake / "lakefile.lean"),
            "--name", "test",
            "--strict",
        ]
    )
    assert rc == 1


def test_strict_exits_zero_when_clean(tmp_path: Path) -> None:
    """--strict on a clean lake: exit 0."""
    lake = tmp_path / "clean"
    lake.mkdir()
    (lake / "lakefile.lean").write_text(
        "@[default_target]\nlean_lib «Foo» where\n  globs := #[`Foo]\n"
    )
    (lake / "Foo.lean").write_text("namespace Foo\nend Foo\n")
    rc = check_lean_orphans.main(
        [
            "--project-path", str(lake),
            "--lakefile", str(lake / "lakefile.lean"),
            "--name", "clean",
            "--strict",
        ]
    )
    assert rc == 0


def test_exclude_whitelists_intentional_orphan(tmp_lake: Path) -> None:
    """--exclude removes a known intentional orphan from the FAIL list."""
    rc = check_lean_orphans.main(
        [
            "--project-path", str(tmp_lake),
            "--lakefile", str(tmp_lake / "lakefile.lean"),
            "--name", "test",
            "--strict",
            "--exclude", "Baz.lean",
        ]
    )
    assert rc == 0


def test_instance_18786_approval_defs(tmp_path: Path) -> None:
    """Reproduce the #18786 defect: ``ApprovalDefs.lean`` orphan on
    ``social_choice_lean_peters`` (pre-fix lakefile: only ```PetersTour``)."""
    lake = tmp_path / "scp"
    lake.mkdir()
    (lake / "lakefile.lean").write_text(
        "@[default_target]\nlean_lib «PetersTour» where\n"
        "  globs := #[`PetersTour]\n"
    )
    (lake / "PetersTour.lean").write_text("namespace PetersTour\nend\n")
    (lake / "ApprovalDefs.lean").write_text("namespace ApprovalDefs\nend\n")
    (lake / "ApprovalDefs_en.lean").write_text("namespace ApprovalDefs_en\nend\n")
    rc = check_lean_orphans.main(
        [
            "--project-path", str(lake),
            "--lakefile", str(lake / "lakefile.lean"),
            "--name", "scp_pre_fix",
            "--strict",
        ]
    )
    assert rc == 1


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
