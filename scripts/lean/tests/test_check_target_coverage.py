#!/usr/bin/env python3
"""Tests for check_target_coverage.py (#8782 advisory proof-integrity coverage).

Dual-mode: runnable directly (``python scripts/lean/tests/test_check_target_coverage.py``)
or under pytest (auto-collected by scripts-tests.yml on any ``scripts/**`` change).

Locks the advisory contract of the conway proof-integrity gate coverage check:
  - exit 0 unconditionally (advisory, never blocks CI);
  - blind-spot detection (compiled-but-ungated modules);
  - phantom detection (gated-but-no-source modules);
  - lib-root scoping (``<lib>/`` subdir + ``<lib>.lean`` umbrella + ``<lib>_en.lean`` sibling);
  - maximal walk excludes build cache / lakefile / toolchain;
  - ``--from-workflow`` unions the target list over every gate job, so the report
    cannot hold a stale copy of it (#8782);
  - ``target-modules: "*"`` (issue #10889) is a runtime-derivation directive:
    the gate walks the lake itself (``discover_modules``) and drops ``_en`` i18n
    siblings by default (``filter_i18n_siblings``), so every compiled module is
    inspected by construction -- a hand-maintained list can never drift out of
    the gate's view again ("vert hors-cible", cf #8782).
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_target_coverage import (  # noqa: E402
    _EXCLUDE_TOP_DIRS,
    _uses_lean_axiom,
    discover_modules,
    filter_i18n_siblings,
    main,
    parse_target_modules,
    targets_from_workflow,
)

_REPO_ROOT = Path(__file__).resolve().parents[3]


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


# ---------------------------------------------------------------------------
# --from-workflow — the target list is read, never copied (#8782)
# ---------------------------------------------------------------------------

def _write_workflow(tmp_path: Path, body: str) -> Path:
    wf = tmp_path / "wf.yml"
    wf.write_text(body, encoding="utf-8")
    return wf


class TestUsesLeanAxiom:
    """Both call forms occur in the repo; matching only one silently halves coverage."""

    def test_pinned_remote_form(self):
        # lean-conway.yml
        assert _uses_lean_axiom("jsboige/CoursIA/.github/workflows/lean-axiom.yml@main")

    def test_local_relative_form(self):
        # lean-knot.yml (resolves per-PR)
        assert _uses_lean_axiom("./.github/workflows/lean-axiom.yml")

    def test_sha_pin_form(self):
        assert _uses_lean_axiom("jsboige/CoursIA/.github/workflows/lean-axiom.yml@abc1234")

    def test_other_reusable_workflow_rejected(self):
        assert not _uses_lean_axiom("./.github/workflows/lean-build.yml")
        assert not _uses_lean_axiom("actions/checkout@v4")

    def test_non_string_rejected(self):
        # a job with `steps:` and no `uses:` yields None, not a string
        assert not _uses_lean_axiom(None)  # type: ignore[arg-type]


class TestTargetsFromWorkflow:
    def test_unions_across_jobs(self, tmp_path):
        """The blocking gate and the audit gate are *both* the gate."""
        wf = _write_workflow(tmp_path, """
name: fake
jobs:
  proof-integrity:
    uses: jsboige/CoursIA/.github/workflows/lean-axiom.yml@main
    with:
      target-modules: "Conway.KochenSpecker,Conway.FreeWillTheorem"
      fail-on-sorry: true
  proof-integrity-audit:
    uses: ./.github/workflows/lean-axiom.yml
    with:
      target-modules: "Conway.Life.HashlifeCorrectness"
      fail-on-sorry: false
""")
        union, per_job = targets_from_workflow(wf)
        assert union == {
            "Conway.KochenSpecker",
            "Conway.FreeWillTheorem",
            "Conway.Life.HashlifeCorrectness",
        }
        assert set(per_job) == {"proof-integrity", "proof-integrity-audit"}
        assert per_job["proof-integrity-audit"] == {"Conway.Life.HashlifeCorrectness"}

    def test_ignores_non_gate_jobs(self, tmp_path):
        wf = _write_workflow(tmp_path, """
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - run: lake build
  proof-integrity:
    uses: ./.github/workflows/lean-axiom.yml
    with:
      target-modules: "Knots.Basic"
""")
        union, per_job = targets_from_workflow(wf)
        assert union == {"Knots.Basic"}
        assert set(per_job) == {"proof-integrity"}  # `build` contributes nothing

    def test_gate_job_with_empty_list_is_still_recorded(self, tmp_path):
        """A gate that targets nothing is a finding, not an absence -- keep it visible."""
        wf = _write_workflow(tmp_path, """
jobs:
  proof-integrity:
    uses: ./.github/workflows/lean-axiom.yml
    with:
      fail-on-sorry: true
""")
        union, per_job = targets_from_workflow(wf)
        assert union == set()
        assert per_job == {"proof-integrity": set()}  # recorded, not dropped

    def test_no_gate_job_yields_empty_per_job(self, tmp_path):
        wf = _write_workflow(tmp_path, """
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - run: echo hi
""")
        union, per_job = targets_from_workflow(wf)
        assert union == set()
        assert per_job == {}


class TestFromWorkflowCli:
    def test_reports_per_job_breakdown(self, tmp_path, capsys):
        lake = _make_lake(tmp_path)
        wf = _write_workflow(tmp_path, """
jobs:
  blocking:
    uses: ./.github/workflows/lean-axiom.yml
    with:
      target-modules: "Conway.KochenSpecker"
  audit:
    uses: ./.github/workflows/lean-axiom.yml
    with:
      target-modules: "Conway.Life.GridCanonical"
""")
        rc = main(["--project-path", str(lake), "--from-workflow", str(wf),
                   "--lib-root", "Conway", "--name", "fake"])
        assert rc == 0
        out = capsys.readouterr().out
        assert "job blocking: 1" in out
        assert "job audit: 1" in out
        # union of the two -> 2 of the 4 compiled modules, neither in the blind spot
        assert "Gate target-modules:                2" in out
        assert "Conway.Life.GridCanonical" not in out.split("BLIND SPOT")[-1]

    def test_no_gate_wired_is_not_a_zero_percent_figure(self, tmp_path, capsys):
        """`no gate job` and `0% covered` are opposite claims; never print the latter for the former."""
        lake = _make_lake(tmp_path)
        wf = _write_workflow(tmp_path, """
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - run: echo hi
""")
        rc = main(["--project-path", str(lake), "--from-workflow", str(wf),
                   "--lib-root", "Conway"])
        assert rc == 0
        out = capsys.readouterr().out
        assert "NO GATE WIRED" in out
        assert "nothing was measured" in out
        # the sentinel returns before any coverage arithmetic is printed
        assert "Covered" not in out
        assert "0.0%" not in out
        assert "BLIND SPOT" not in out

    def test_missing_workflow_exits_zero(self, tmp_path, capsys):
        lake = _make_lake(tmp_path)
        rc = main(["--project-path", str(lake),
                   "--from-workflow", str(tmp_path / "absent.yml"),
                   "--lib-root", "Conway"])
        assert rc == 0
        assert "workflow not found" in capsys.readouterr().out

    def test_source_flags_are_mutually_exclusive(self, tmp_path):
        lake = _make_lake(tmp_path)
        wf = _write_workflow(tmp_path, "jobs: {}\n")
        with pytest.raises(SystemExit):
            main(["--project-path", str(lake),
                  "--target-modules", "A", "--from-workflow", str(wf)])

    def test_a_source_is_required(self, tmp_path):
        lake = _make_lake(tmp_path)
        with pytest.raises(SystemExit):
            main(["--project-path", str(lake)])


# ---------------------------------------------------------------------------
# Runtime derivation (issue #10889) -- `target-modules: "*"`
# ---------------------------------------------------------------------------

class TestRuntimeDerivation:
    """The gate's ``"*"`` directive derives its module list at runtime.

    ``lean-axiom.yml`` walks the lake (``discover_modules``) and drops ``_en``
    i18n siblings by default (``filter_i18n_siblings``) unless a caller opts
    into the full bilingual surface via ``include-i18n-siblings: "true"``.
    These tests lock the two functions the workflow imports, so the exact
    filter the gate applies is unit-tested against the walk.
    """

    def test_walk_finds_en_in_root_stem_and_non_root_dir(self, tmp_path):
        lake = _make_lake(tmp_path)
        # a non-root `_en` DIRECTORY (Conway/Life_en/...) -- the segment filter
        # must catch it too, not only the root stem `<lib>_en.lean`.
        (lake / "Conway" / "Life_en").mkdir()
        (lake / "Conway" / "Life_en" / "GridCanonical_en.lean").write_text(
            "-- en\n", encoding="utf-8"
        )
        mods = discover_modules(lake, None)
        assert "Conway_en" in mods                       # root stem sibling
        assert "Conway.Life_en.GridCanonical_en" in mods  # non-root dir sibling
        assert "Conway.Life.GridCanonical" in mods         # FR kept by the walk

    def test_filter_drops_both_en_forms_keeps_fr(self, tmp_path):
        lake = _make_lake(tmp_path)
        (lake / "Conway" / "Life_en").mkdir()
        (lake / "Conway" / "Life_en" / "GridCanonical_en.lean").write_text(
            "-- en\n", encoding="utf-8"
        )
        mods = discover_modules(lake, None)
        fr = filter_i18n_siblings(mods)
        assert "Conway_en" not in fr
        assert "Conway.Life_en.GridCanonical_en" not in fr
        assert "Conway" in fr
        assert "Conway.Life.GridCanonical" in fr
        assert "Conway.KochenSpecker" in fr

    def test_filter_is_noop_without_en(self, tmp_path):
        # `include-i18n-siblings: "true"` skips the filter entirely; a lake
        # with no `_en` at all is the same set either way (idempotence of the
        # default path).
        lake = _make_lake(tmp_path)
        (lake / "Conway_en.lean").unlink()
        mods = discover_modules(lake, None)
        assert mods == filter_i18n_siblings(mods)

    def test_star_covers_everything_no_blind_spot(self, tmp_path, capsys):
        # "*" is a directive, not a module name: the advisory reports 100% by
        # construction and never a blind spot or a phantom.
        lake = _make_lake(tmp_path)
        rc = main(["--project-path", str(lake), "--target-modules", "*"])
        assert rc == 0
        out = capsys.readouterr().out
        assert "OK: target-modules=\"*\"" in out
        assert "100.0%" in out
        assert "BLIND SPOT" not in out
        assert "PHANTOM" not in out


class TestRealWorkflowRegression:
    """The report this mode exists to stop having emitted.

    Before ``--from-workflow``, the advisory step in ``lean-conway.yml`` was given
    the *blocking* job's list literally, so it printed
    ``Conway.Life.HashlifeCorrectness`` under "the gate never inspects their
    axioms" -- false about precisely the module option (b) of #8782 had been
    wired to cover. These assertions fail if any gate job's list is ever again
    dropped from the coverage report.
    """

    def test_conway_union_covers_the_audit_job_target(self):
        wf = _REPO_ROOT / ".github" / "workflows" / "lean-conway.yml"
        if not wf.is_file():
            pytest.skip(f"workflow not present: {wf}")
        union, per_job = targets_from_workflow(wf)
        assert len(per_job) >= 2, f"expected blocking + audit gate jobs, got {sorted(per_job)}"
        # Post-#10889 the audit job derives its list at runtime (`"*"`): the
        # union carries the sentinel instead of the literal module. Either
        # form means the gate inspects HashlifeCorrectness.
        assert "*" in union or "Conway.Life.HashlifeCorrectness" in union
        assert "Conway.KochenSpecker" in union
        assert "Conway.FreeWillTheorem" in union

    def test_knot_union_is_non_empty(self):
        wf = _REPO_ROOT / ".github" / "workflows" / "lean-knot.yml"
        if not wf.is_file():
            pytest.skip(f"workflow not present: {wf}")
        union, per_job = targets_from_workflow(wf)
        assert per_job, "lean-knot.yml has a proof-integrity job; it must be found"
        # Post-#10889 the knot gate derives its module list at runtime (`"*"`):
        # the union is the sentinel, not an enumerated module. Either form means
        # the gate inspects the whole lake, which is what this test guards.
        assert "*" in union or "Knots.Basic" in union


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
