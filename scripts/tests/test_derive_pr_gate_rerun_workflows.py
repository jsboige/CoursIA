#!/usr/bin/env python3
"""Unit tests for derive_pr_gate_rerun_workflows.py (#11865).

What these pin, in order of how much damage getting them wrong would do:

1. **Positive control.** A derivation that has lost the gate's own workflow
   produces no verdict (exit 2), never a green and never a list -- an
   instrument that misparses the directory must not under-cover in silence,
   which is the exact defect class this script closes.
2. **Membership rule.** Path-filtered PR workflows ARE members (their checks
   block the PRs they run on); advisory-only and non-PR workflows are NOT.
3. **Drift verdicts.** In-sync commits exit 0; a missing or extra workflow
   name exits 1 with the offending name spelled out.

Run: python -m pytest scripts/tests/test_derive_pr_gate_rerun_workflows.py
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import derive_pr_gate_rerun_workflows as drv  # noqa: E402

import yaml  # noqa: E402


GATE_YML = """
name: PR gate
on:
  pull_request:
    branches: [main]
jobs:
  gate:
    name: PR gate
    runs-on: ubuntu-latest
"""

GUARD_YML = """
name: Some Guard
on:
  pull_request:
    branches: [main]
jobs:
  check-something-required:
    runs-on: ubuntu-latest
"""

PATH_FILTERED_YML = """
name: Path Filtered Guard
on:
  pull_request:
    branches: [main]
    paths: ['src/**']
jobs:
  check-paths-required:
    runs-on: ubuntu-latest
"""

ADVISORY_ONLY_YML = """
name: Pure Advisory
on:
  pull_request:
    branches: [main]
jobs:
  lint-advisory:
    name: some check (advisory)
    runs-on: ubuntu-latest
"""

PUSH_ONLY_YML = """
name: Push Only
on:
  push:
    branches: [main]
jobs:
  check-push-required:
    runs-on: ubuntu-latest
"""

RERUN_YML_TEMPLATE = """
name: PR gate (re-aggregate)
on:
  workflow_run:
    workflows: [{names}]
    types: [completed]
jobs:
  reaggregate:
    runs-on: ubuntu-latest
"""

# `pull_request: {}` (not bare `pull_request:`): PyYAML parses the bare key
# as None, and the shared _pull_request_trigger treats None as absent -- the
# inherited pr_gate.py semantics, kept here on purpose (no real workflow in
# .github/workflows uses the bare-key shape; verified at #11865 delivery).
NO_NAME_YML = """
on:
  pull_request: {}
jobs:
  check-anon-required:
    runs-on: ubuntu-latest
"""


def make_dir(tmp_path, files):
    wf = tmp_path / "workflows"
    wf.mkdir()
    for name, text in files.items():
        (wf / name).write_text(text, encoding="utf-8")
    return str(wf)


def make_rerun(tmp_path, names):
    rendered = RERUN_YML_TEMPLATE.format(names=", ".join(f'"{n}"' for n in names))
    p = tmp_path / "pr-gate-rerun.yml"
    p.write_text(rendered, encoding="utf-8")
    return str(p)


FULL_FIXTURE = {
    "gate.yml": GATE_YML,
    "guard.yml": GUARD_YML,
    "paths.yml": PATH_FILTERED_YML,
    "advisory.yml": ADVISORY_ONLY_YML,
    "push.yml": PUSH_ONLY_YML,
    "no-name.yml": NO_NAME_YML,
}


# --- membership rule ----------------------------------------------------------


def test_membership_rule(tmp_path):
    derived, gate = drv.derive_rerun_workflows(make_dir(tmp_path, FULL_FIXTURE))
    assert gate == ["PR gate"]
    assert derived == ["Path Filtered Guard", "Some Guard", "no-name"]


def test_path_filtered_workflows_are_members(tmp_path):
    derived, _ = drv.derive_rerun_workflows(
        make_dir(tmp_path, {"gate.yml": GATE_YML, "paths.yml": PATH_FILTERED_YML})
    )
    assert derived == ["Path Filtered Guard"]


def test_advisory_only_and_non_pr_workflows_are_not_members(tmp_path):
    derived, _ = drv.derive_rerun_workflows(
        make_dir(
            tmp_path,
            {
                "gate.yml": GATE_YML,
                "advisory.yml": ADVISORY_ONLY_YML,
                "push.yml": PUSH_ONLY_YML,
            },
        )
    )
    assert derived == []


# --- positive control ----------------------------------------------------------


def test_positive_control_failure_is_a_null_verdict(tmp_path, capsys):
    # No gate.yml: the mapping cannot find the workflow owning the PR gate
    # job. check() must return 2 (nul) -- never 0 (silent pass) and never a
    # printed list.
    wf = make_dir(tmp_path, {"guard.yml": GUARD_YML})
    rerun = make_rerun(tmp_path, ["Some Guard"])
    assert drv.check(wf, rerun) == drv.EXIT_BROKEN
    assert drv.main(["--print-yaml", "--workflows-dir", wf]) == drv.EXIT_BROKEN


def test_gate_workflow_never_in_derived_list(tmp_path):
    # Even if committed by mistake, the gate stays out of the derived list:
    # its completion would re-trigger the rerun workflow and self-sustain.
    derived, gate = drv.derive_rerun_workflows(
        make_dir(tmp_path, {"gate.yml": GATE_YML, "guard.yml": GUARD_YML})
    )
    assert gate == ["PR gate"]
    assert "PR gate" not in derived


def test_unreadable_rerun_yml_is_null_not_empty(tmp_path):
    wf = make_dir(tmp_path, FULL_FIXTURE)
    missing = str(tmp_path / "does-not-exist.yml")
    assert drv.check(wf, missing) == drv.EXIT_BROKEN


# --- drift verdicts -------------------------------------------------------------


def test_in_sync_commits_exit_zero(tmp_path):
    wf = make_dir(tmp_path, FULL_FIXTURE)
    rerun = make_rerun(tmp_path, ["Some Guard", "Path Filtered Guard", "no-name"])
    assert drv.check(wf, rerun) == drv.EXIT_SYNC


def test_missing_workflow_name_exits_one_with_name_spelled(tmp_path, capsys):
    wf = make_dir(tmp_path, FULL_FIXTURE)
    rerun = make_rerun(tmp_path, ["Some Guard"])  # forgot the other two
    assert drv.check(wf, rerun) == drv.EXIT_DRIFT
    out = capsys.readouterr().out
    assert "MISSING" in out and "Path Filtered Guard" in out and "no-name" in out


def test_extra_workflow_name_exits_one(tmp_path, capsys):
    wf = make_dir(tmp_path, FULL_FIXTURE)
    rerun = make_rerun(tmp_path, ["Some Guard", "Ghost Workflow"])
    assert drv.check(wf, rerun) == drv.EXIT_DRIFT
    out = capsys.readouterr().out
    assert "EXTRA" in out and "Ghost Workflow" in out


def test_print_yaml_round_trips_through_check(tmp_path):
    wf = make_dir(tmp_path, FULL_FIXTURE)
    import contextlib
    import io

    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        assert drv.main(["--print-yaml", "--workflows-dir", wf]) == drv.EXIT_SYNC
    printed = buf.getvalue()
    assert printed.startswith("workflows: [")
    # The emitted line, re-committed, must satisfy --check (the regeneration
    # path the drift message advertises actually converges).
    body = printed[len("workflows: "):]
    names = [str(n) for n in yaml.safe_load(body)]
    rerun = make_rerun(tmp_path, names)
    assert drv.check(wf, rerun) == drv.EXIT_SYNC


# --- regression against the real repository --------------------------------------


def test_real_repo_list_is_in_sync():
    """The committed pr-gate-rerun.yml must match the derivation from the
    repository's own .github/workflows. A workflow added without
    regenerating the list trips this test AND the CI drift guard -- that is
    the forcing function, not an inconvenience to work around.
    """
    repo = Path(__file__).resolve().parents[2]
    assert (
        drv.check(
            str(repo / ".github" / "workflows"),
            str(repo / ".github" / "workflows" / "pr-gate-rerun.yml"),
        )
        == drv.EXIT_SYNC
    )
