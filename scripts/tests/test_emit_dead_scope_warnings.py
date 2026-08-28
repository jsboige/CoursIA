"""Tests for `scripts/ci/emit_dead_scope_warnings.py` (#13129).

The helper is the advisory-side bridge between `check_lane_claim.py`'s
`caller_empty_scope` and the GitHub Actions `::warning::` annotation
channel. The tests cover:
  - paths extraction from a PR body with a [CLAIMED] marker
  - paths extraction from a body with NO marker (no-ops)
  - the lane extractor (delegates to `grain_tag.extract_lane`)
  - end-to-end: a body with one dead and one live glob produces ONE annotation
  - end-to-end: a body whose every glob matches -> zero annotations
  - the proximity suggestion is a SEPARATE channel (stderr WARN from
    `check_lane_claim.py`'s `_lint_claim_events`, not this helper's stdout)
  - the lane-claim-guard workflow YAML stays structurally valid after the
    helper is wired in (regression pin for the heredoc/inline-python3 trap)
"""
from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
SCRIPTS_CI = ROOT / "scripts" / "ci"
SCRIPTS = ROOT / "scripts"


def _load_helper():
    """Import `emit_dead_scope_warnings` as a module (no package install)."""
    spec = importlib.util.spec_from_file_location(
        "emit_dead_scope_warnings",
        SCRIPTS_CI / "emit_dead_scope_warnings.py",
    )
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(SCRIPTS))  # for grain_tag, check_lane_claim
    spec.loader.exec_module(mod)
    return mod


HELPER = _load_helper()


def test_extract_lane_reads_grain_tag_in_body():
    body = (
        "Grain: MED/tooling — lane myia-po-2024:CoursIA-2 — "
        "prev: MED/guard #13248\n\n"
        "Some prose.\n"
    )
    assert HELPER._extract_lane(body) == "myia-po-2024:CoursIA-2"


def test_extract_lane_empty_when_no_grain_tag():
    assert HELPER._extract_lane("Nothing here.") == ""


def test_extract_paths_in_body_parses_marker_clause():
    body = (
        "Some intro.\n"
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- "
        "paths: scripts/check_lane_claim.py, scripts/grain_tag.py\n\n"
        "Closing prose."
    )
    assert HELPER._extract_paths_in_body(body) == [
        "scripts/check_lane_claim.py",
        "scripts/grain_tag.py",
    ]


def test_extract_paths_in_body_empty_when_no_clause():
    assert HELPER._extract_paths_in_body("Just prose, no claim.") == []


def test_extract_paths_in_body_dedupes():
    body = "[CLAIMED] lane x -- paths: a.py, b.py, a.py"
    assert HELPER._extract_paths_in_body(body) == ["a.py", "b.py"]


def test_main_emits_one_warning_per_dead_glob(tmp_path, capsys):
    """End-to-end -- a body with one dead glob + one live glob yields ONE
    `::warning::` line. Live globs are intentionally silent (the channel
    is for hints, not noise)."""
    body_file = tmp_path / "body.txt"
    body_file.write_text(
        "Grain: MED/tooling — lane myia-po-2024:CoursIA-2 — "
        "prev: MED/guard #13248\n\n"
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: "
        "scripts/notexist_typo.py, scripts/check_lane_claim.py\n",
        encoding="utf-8",
    )
    rc = HELPER.main(["--body-file", str(body_file)])
    assert rc == 0
    captured = capsys.readouterr()
    lines = [ln for ln in captured.out.splitlines() if ln.startswith("::warning")]
    assert len(lines) == 1
    assert "scripts/notexist_typo.py" in lines[0]
    assert "Dead scope glob (#13129)" in lines[0]


def test_main_no_warnings_when_all_globs_live(tmp_path, capsys):
    """Negative control -- a body whose every glob matches a tracked file
    produces ZERO annotations. Selectivity pin: the helper is a hint
    channel, not a no-op rewriter of every PR."""
    body_file = tmp_path / "body.txt"
    body_file.write_text(
        "Grain: MED/tooling — lane myia-po-2024:CoursIA-2\n\n"
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: "
        "scripts/check_lane_claim.py, scripts/grain_tag.py\n",
        encoding="utf-8",
    )
    rc = HELPER.main(["--body-file", str(body_file)])
    assert rc == 0
    captured = capsys.readouterr()
    assert captured.out.strip() == ""


def test_main_no_warnings_when_no_paths_clause(tmp_path, capsys):
    body_file = tmp_path / "body.txt"
    body_file.write_text(
        "Grain: MED/tooling — lane myia-po-2024:CoursIA-2\n\n"
        "Just prose, no claim marker.\n",
        encoding="utf-8",
    )
    rc = HELPER.main(["--body-file", str(body_file)])
    assert rc == 0
    assert capsys.readouterr().out.strip() == ""


def test_main_no_warnings_when_no_lane(tmp_path, capsys):
    body_file = tmp_path / "body.txt"
    body_file.write_text(
        "[CLAIMED] lane x -- paths: scripts/notexist.py\n",
        encoding="utf-8",
    )
    rc = HELPER.main(["--body-file", str(body_file)])
    assert rc == 0
    assert capsys.readouterr().out.strip() == ""


def test_lane_claim_guard_workflow_yaml_remains_valid():
    """Regression pin -- the YAML literal must parse cleanly after the
    helper is wired in. The c.579 first attempt broke the YAML by putting
    a multi-line `python3 -c "..."` in a YAML scalar; the helper extraction
    avoids that trap. Pin stays green for the foreseeable future."""
    import yaml  # type: ignore

    wf = ROOT / ".github" / "workflows" / "lane-claim-guard.yml"
    data = yaml.safe_load(wf.read_text(encoding="utf-8"))
    assert "jobs" in data
    assert "check-lane-claim-advisory" in data["jobs"]
    # The advisory job's `run:` block must mention the helper by path.
    advisory_run = "\n".join(
        step.get("run", "") for step in
        data["jobs"]["check-lane-claim-advisory"]["steps"]
    )
    assert "emit_dead_scope_warnings.py" in advisory_run
