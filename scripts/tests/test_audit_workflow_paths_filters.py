#!/usr/bin/env python3
"""Tests for audit_workflow_paths_filters.py — issue #10600.

The audit is a READ-ONLY inventory. Tests assert:
  1. Inventory enumerates at least 80 workflows (the repo has 80+ workflows).
  2. The PR-type fan-out estimate is monotonically lower than the no-filter
     count (a strict subset, never wider).
  3. Strict mode flags REQUIS-SANS-paths violations.
  4. JSON output is parseable and contains the expected keys.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPT = REPO_ROOT / "scripts" / "audit_workflow_paths_filters.py"


def run(args: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=30,
    )


def test_inventory_size():
    result = run(["--json"])
    assert result.returncode == 0, f"audit failed: {result.stderr}"
    data = json.loads(result.stdout)
    assert data["workflows_total"] >= 80, (
        f"expected >=80 workflows, got {data['workflows_total']}"
    )
    assert data["workflows_pull_request"] >= 70, (
        f"expected >=70 pull_request workflows, got {data['workflows_pull_request']}"
    )


def test_fanout_subset():
    result = run(["--json"])
    data = json.loads(result.stdout)
    pulls = data["workflows_pull_request"]
    for pr_type, n in data["fanout_estimated_per_pr_type"].items():
        assert n <= pulls, (
            f"fanout for {pr_type} ({n}) exceeds total pulls ({pulls})"
        )


def test_strict_required_without_paths():
    """Strict mode must EXIT 0 on main (PR gate IS paths-filtered in fact via
    repo convention; if it ever loses its paths filter, this test will catch it).

    Note: PR gate IS paths-filtered (issue #11809 cascade). If main goes red
    here, it's a real signal that a required check has lost its filter.
    """
    result = run(["--strict"])
    assert result.returncode == 0, (
        f"strict mode flagged violations: {result.stderr}"
    )


def test_json_keys():
    result = run(["--json"])
    data = json.loads(result.stdout)
    expected_keys = {
        "issue",
        "workflows_total",
        "workflows_pull_request",
        "workflows_with_paths",
        "workflows_label_posing",
        "required_checks",
        "required_checks_source",
        "fanout_estimated_per_pr_type",
        "rows",
    }
    assert expected_keys.issubset(data.keys()), (
        f"missing keys: {expected_keys - set(data.keys())}"
    )


def test_markdown_output():
    result = run([])
    assert result.returncode == 0
    assert "# Audit workflow paths-filters" in result.stdout
    assert "pull_request" in result.stdout


if __name__ == "__main__":
    test_inventory_size()
    print("test_inventory_size OK")
    test_fanout_subset()
    print("test_fanout_subset OK")
    test_strict_required_without_paths()
    print("test_strict_required_without_paths OK")
    test_json_keys()
    print("test_json_keys OK")
    test_markdown_output()
    print("test_markdown_output OK")
    print("All tests passed.")