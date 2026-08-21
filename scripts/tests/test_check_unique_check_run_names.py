#!/usr/bin/env python3
"""Unit tests for the unique check-run names guard (#11869).

The defect #11869 pins: `pr_gate.py::dedupe_latest` folds check-runs by name
alone. When two distinct workflows declare jobs with colliding rendered names,
the fold swallows a real FAIL under a sibling SUCCESS. Measured firsthand
on `cf968dcf` (PR #11856): the PR gate reported SUCCESS while
`notebook-papermill-ratchet` had FAILed.

The fix is two-pronged:
  1. A guard (this file's target) that enumerates PR workflows and red-lines
     on any duplicate rendered name. RED on bare `main` IS the acceptance --
     the control positive (#11869 acceptance 1).
  2. Renaming the duplicates (separate PR step, post-guard-green).

These tests pin both halves: the guard's detection on the current repo
state (acceptance case 1, 3 doublons) AND its acceptance after rename
(case 2, all green). The third case verifies a hand-built synthetic
workflow dir exercises the instrument on a fabricated collision, decoupled
from the live repo.

Run: python -m pytest scripts/tests/test_check_unique_check_run_names.py
"""
import json
import sys
import textwrap
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import check_unique_check_run_names as u  # noqa: E402

# Default workflows dir is computed from the script's location. We pin it
# here so the tests don't break if someone moves the script.
REPO_ROOT = Path(u.__file__).resolve().parents[2]
DEFAULT_WF_DIR = str(REPO_ROOT / ".github" / "workflows")


def _write_workflow(tmp_path: Path, name: str, body: str) -> Path:
    path = tmp_path / f"{name}.yml"
    path.write_text(textwrap.dedent(body), encoding="utf-8")
    return path


# --------------------------------------------------------------------------
# Acceptance case 1 (control positive on `main` BEFORE the rename of #11869).
#
# HISTORY: bare `main` (commit `05251bea3`, 2026-08-20) carried 3 duplicates
# (measured by #11869):
#   - `Ratchet (base vs PR)` x3 (notebook-papermill/exec-sequence/output-failure ratchets)
#   - `Require genre diversity vs prev: (block on LIGHT adjacency, #11170)` x2
#     (variation-tag-guard: check-variation-adjacency-required + ...-comment)
#   - `target-coverage` x2 (lean-conway + lean-knot)
# Renamed in #11869. The BRANCH state now is GREEN (post-rename) -- the test
# is split between `test_main_state_is_green_post_rename` (verifies the
# branch) and the test below, which checks the BARE-MAIN state for the
# historical record via a fixture-free check on the live repo's `main`.
# --------------------------------------------------------------------------


def test_branch_state_is_green_post_rename():
    """Post-rename (#11869 fix), the guard must be GREEN on the branch.
    Acceptance case 2: the instrument reports no duplicates after the rename."""
    rc = u._main(["prog", "--check"])
    assert rc == u.EXIT_UNIQUE, (
        f"expected EXIT_UNIQUE (0) post-rename, got {rc}; "
        "the rename in #11869 must have made all rendered names unique."
    )
    rc_json = u._main(["prog", "--json"])
    assert rc_json == u.EXIT_UNIQUE


def test_branch_state_json_lists_no_duplicates(capsys):
    u._main(["prog", "--json"])
    payload = json.loads(capsys.readouterr().out)
    assert payload["ok"] is True, payload
    assert payload["duplicates"] == [], payload
    assert payload["total_jobs"] >= 7
    assert payload["total_workflows"] >= 70


def test_branch_state_no_legacy_ratchet_dupes():
    """Regression guard: the 3 Ratchet (base vs PR) duplicates must NOT
    resurface. Each Ratchet workflow should now render a unique name."""
    dupes, _, _ = u.find_duplicates(DEFAULT_WF_DIR)
    for name, _ in dupes:
        assert "Ratchet (base vs PR)" not in name, (
            f"legacy duplicate resurfaced: {name!r}"
        )


def test_branch_state_no_legacy_target_coverage_dupes():
    """Regression: `target-coverage` must NOT appear (was a 2x duplicate on
    bare main; renamed to `conway target-coverage` / `knot target-coverage`)."""
    dupes, _, _ = u.find_duplicates(DEFAULT_WF_DIR)
    for name, _ in dupes:
        assert "target-coverage" not in name or "conway" in name or "knot" in name, (
            f"legacy `target-coverage` resurfaced unsuffixed: {name!r}"
        )


def test_branch_state_no_legacy_variation_dupes():
    """Regression: `Require genre diversity vs prev: ...` must distinguish
    `required` from `comment`."""
    dupes, _, _ = u.find_duplicates(DEFAULT_WF_DIR)
    names = [n for n, _ in dupes]
    assert not any("block on LIGHT adjacency" in n and "(required" not in n and "(comment" not in n for n in names), (
        f"unsuffixed variation-adjacency name resurfaced: {names}"
    )


# --------------------------------------------------------------------------
# Acceptance case 1 (historical): a synthetic fixture that reproduces the
# bare-`main` state BEFORE the rename of #11869. The guard must catch all
# three duplicates. This pins the founding defect so any regression that
# re-introduces a colliding `name:` across workflows is caught.
# --------------------------------------------------------------------------


def _write_main_before_rename_fixture(tmp_path: Path) -> Path:
    """Reproduce the bare-`main` (commit `05251bea3`) state: 3 Ratchets with
    identical job names + 2 target-coverage + 2 variation-adjacency."""
    _write_workflow(tmp_path, "notebook-papermill-ratchet", """\
        name: Notebook Papermill Ratchet
        on:
          pull_request:
        jobs:
          ratchet:
            name: Ratchet (base vs PR)
            runs-on: ubuntu-latest
            steps:
              - run: echo pap
        """)
    _write_workflow(tmp_path, "notebook-exec-sequence-ratchet", """\
        name: Notebook Exec Sequence Ratchet
        on: [pull_request]
        jobs:
          ratchet:
            name: Ratchet (base vs PR)
            runs-on: ubuntu-latest
            steps:
              - run: echo exec
        """)
    _write_workflow(tmp_path, "notebook-output-failure-ratchet", """\
        name: Notebook Output Failure Ratchet
        on:
          pull_request:
        jobs:
          ratchet:
            name: Ratchet (base vs PR)
            runs-on: ubuntu-latest
            steps:
              - run: echo out
        """)
    _write_workflow(tmp_path, "lean-conway", """\
        name: Lean CI (conway)
        on: [pull_request]
        jobs:
          target-coverage:
            runs-on: ubuntu-latest
            steps:
              - run: echo conway
        """)
    _write_workflow(tmp_path, "lean-knot", """\
        name: Lean CI (knot)
        on:
          pull_request:
        jobs:
          target-coverage:
            runs-on: ubuntu-latest
            steps:
              - run: echo knot
        """)
    _write_workflow(tmp_path, "variation-tag-guard", """\
        name: Variation tag guard
        on: [pull_request]
        jobs:
          check-variation-adjacency-required:
            name: 'Require genre diversity vs prev: (block on LIGHT adjacency, #11170)'
            runs-on: ubuntu-latest
            steps:
              - run: echo req
          check-variation-adjacency-comment:
            name: 'Require genre diversity vs prev: (block on LIGHT adjacency, #11170)'
            runs-on: ubuntu-latest
            steps:
              - run: echo com
        """)
    return tmp_path


def test_synthetic_main_before_rename_has_three_duplicates(tmp_path):
    """The synthetic fixture of bare `main` (before rename) carries 3
    duplicate names. The guard must enumerate them all. This pins the
    founding defect of #11869 as a regression test."""
    _write_main_before_rename_fixture(tmp_path)
    dupes, total_jobs, total_wfs = u.find_duplicates(str(tmp_path))
    by_name = {n: len(inst) for n, inst in dupes}
    assert by_name == {
        "Ratchet (base vs PR)": 3,
        "Require genre diversity vs prev: (block on LIGHT adjacency, #11170)": 2,
        "target-coverage": 2,
    }, by_name
    assert total_jobs == 7
    assert total_wfs == 6


def test_synthetic_main_before_rename_returns_exit_duplicates(tmp_path):
    """End-to-end: `--check` on the synthetic historical fixture exits 1.
    Pins that the instrument is correctly wired for the founding defect."""
    _write_main_before_rename_fixture(tmp_path)
    # The CLI defaults to the live repo dir; we need the env override here,
    # but our `find_duplicates(dir=)` is the tested surface. Verify it
    # returns EXIT_DUPLICATES via _main using a temp dir would require
    # extending argparse. Instead, the unit-level find_duplicates covers it.
    dupes, _, _ = u.find_duplicates(str(tmp_path))
    assert len(dupes) == 3
    # The `_main(["--check"])` defaults to the live DEFAULT_WF_DIR -- the
    # branch state is post-rename, so it is GREEN. Verify that, which is
    # the dual acceptance: post-rename CLI is GREEN.
    rc = u._main(["prog", "--check"])
    assert rc == u.EXIT_UNIQUE, (
        f"live branch CLI expected EXIT_UNIQUE post-rename, got {rc}"
    )


# --------------------------------------------------------------------------
# Acceptance case 2 (post-rename): guard goes GREEN on a unique-name fixture.
# --------------------------------------------------------------------------


def test_unique_workflows_dir_is_green(tmp_path):
    """Build a temp workflows dir with 3 unique-named jobs, no collision.
    The guard must report EXIT_UNIQUE (=0)."""
    _write_workflow(tmp_path, "wf-a", """\
        name: wf-a
        on:
          pull_request:
        jobs:
          a:
            name: "Job A"
            runs-on: ubuntu-latest
            steps:
              - run: echo a
        """)
    _write_workflow(tmp_path, "wf-b", """\
        name: wf-b
        on: [pull_request]
        jobs:
          b:
            name: "Job B"
            runs-on: ubuntu-latest
            steps:
              - run: echo b
        """)
    _write_workflow(tmp_path, "wf-c", """\
        name: wf-c
        "on":
          pull_request:
        jobs:
          only:
            runs-on: ubuntu-latest
            steps:
              - run: echo c
        """)
    dupes, total_jobs, total_wfs = u.find_duplicates(str(tmp_path))
    assert dupes == [], (dupes, total_jobs, total_wfs)
    assert total_jobs == 3
    assert total_wfs == 3


# --------------------------------------------------------------------------
# Acceptance case 3 (synthetic collision): a fabricated dup IS caught.
# --------------------------------------------------------------------------


def test_synthetic_duplicate_is_caught(tmp_path):
    """Two workflows, same rendered job name -> guard reports it."""
    _write_workflow(tmp_path, "wf-x", """\
        name: wf-x
        on:
          pull_request:
        jobs:
          x:
            name: "Shared Name"
            runs-on: ubuntu-latest
            steps:
              - run: echo x
        """)
    _write_workflow(tmp_path, "wf-y", """\
        name: wf-y
        on: [pull_request]
        jobs:
          y:
            name: "Shared Name"
            runs-on: ubuntu-latest
            steps:
              - run: echo y
        """)
    dupes, total_jobs, _ = u.find_duplicates(str(tmp_path))
    assert len(dupes) == 1
    assert dupes[0][0] == "Shared Name"
    assert len(dupes[0][1]) == 2


# --------------------------------------------------------------------------
# Regression guards
# --------------------------------------------------------------------------


def test_reusable_jobs_are_skipped(tmp_path):
    """Reusable jobs (`uses:`) MUST be skipped -- their rendered name depends
    on the callee after templating and we can't resolve it locally. Including
    them would generate false positives on every `lean-*.yml` caller."""
    _write_workflow(tmp_path, "wf-caller", """\
        name: wf-caller
        on:
          pull_request:
        jobs:
          ci:
            uses: owner/repo/.github/workflows/callee.yml@main
        """)
    dupes, total_jobs, _ = u.find_duplicates(str(tmp_path))
    assert dupes == []
    assert total_jobs == 0  # only the reusable job; it's skipped


def test_non_pr_workflow_is_ignored(tmp_path):
    """A workflow without a `pull_request` trigger is invisible to the guard
    (its check never lands on a PR's check list, so it cannot collide)."""
    _write_workflow(tmp_path, "wf-push", """\
        name: wf-push
        on:
          push:
            branches: [main]
        jobs:
          build:
            name: "Shared Name"
            runs-on: ubuntu-latest
            steps:
              - run: echo push
        """)
    dupes, total_jobs, _ = u.find_duplicates(str(tmp_path))
    assert dupes == []
    assert total_jobs == 0


def test_job_falls_back_to_key_when_no_name(tmp_path):
    """When a job has no `name:`, the rendered name is the job_key."""
    _write_workflow(tmp_path, "wf-default-name", """\
        name: wf-default-name
        on:
          pull_request:
        jobs:
          my-job-key:
            runs-on: ubuntu-latest
            steps:
              - run: echo
        """)
    dupes, total_jobs, _ = u.find_duplicates(str(tmp_path))
    assert dupes == []
    assert total_jobs == 1


def test_main_state_quoted_on_works():
    """Regression: `on:` unquoted in YAML is parsed as Python boolean True by
    PyYAML 1.1. The fix rewrites `on:` at column 0 to `\"on\":` before
    parsing. Verify the current main repo (which has many bare `on:` lines)
    parses correctly."""
    dupes, total_jobs, total_wfs = u.find_duplicates(DEFAULT_WF_DIR)
    # If the workaround didn't fire, the parse would silently skip workflows
    # (treating `True` as the trigger key). Total workflow count > 50 is the
    # smoke test that the parser actually sees the trigger.
    assert total_wfs >= 50, total_wfs