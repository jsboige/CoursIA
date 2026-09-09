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
        encoding="utf-8", errors="replace",
    )


def test_inventory_size():
    result = run(["--json"])
    assert result.returncode == 0, f"audit failed: {result.stderr}"
    data = json.loads(result.stdout)
    assert data["workflows_total"] >= 80, (
        f"expected >=80 workflows, got {data['workflows_total']}"
    )
    # #13384 : la fusion des 5 gardes always-on en l'umbrella always-on-guards.yml
    # a rendu leurs workflows sources dormants (workflow_dispatch seul) —
    # 74 -> 69 workflows a trigger pull_request. Plancher recalibre de 70 a 65
    # (marge 4, identique a la marge d'origine), cf precedent absorption fast-lane.
    assert data["workflows_pull_request"] >= 65, (
        f"expected >=65 pull_request workflows, got {data['workflows_pull_request']}"
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


def test_pr_target_filter_excludes_main_detected():
    """#12773 : ``branches-ignore: [main]`` is an effective filter for the
    #10600 objective (do not fire on PRs targeting main). The audit must
    detect it as such and report it in the ``pr_target_filter_excludes_main``
    column.

    Unit-level test : import the helper and feed synthetic workflow dicts.
    """
    # Imported here to avoid polluting the top-level namespace with the
    # production module when the test is collected by pytest.
    sys.path.insert(0, str(REPO_ROOT / "scripts"))
    from audit_workflow_paths_filters import (  # noqa: E402
        has_pr_target_filter_excluding_main,
    )

    # branches-ignore: [main]  -> filter effectif
    wf_ignore = {"on": {"pull_request": {"branches-ignore": ["main"]}}}
    assert has_pr_target_filter_excluding_main(wf_ignore) is True

    # branches: [...] excluant main -> filter effectif
    wf_allowlist = {"on": {"pull_request": {"branches": ["feature/**"]}}}
    assert has_pr_target_filter_excluding_main(wf_allowlist) is True

    # branches: [...] incluant main -> PAS de filtre excluant
    wf_main_ok = {"on": {"pull_request": {"branches": ["main", "feature/**"]}}}
    assert has_pr_target_filter_excluding_main(wf_main_ok) is False

    # Aucun filtre -> False
    wf_no_filter = {"on": {"pull_request": {}}}
    assert has_pr_target_filter_excluding_main(wf_no_filter) is False

    # paths seul (sans target filter) -> False (mais on garde ``paths:`` comme
    # filtre distinct dans le rapport)
    wf_paths_only = {"on": {"pull_request": {"paths": ["scripts/**"]}}}
    assert has_pr_target_filter_excluding_main(wf_paths_only) is False


def test_orphan_delivery_scan_now_reported_as_filtered():
    """#12773 : ``orphaned-delivery-scan.yml`` carries
    ``branches-ignore: [main]`` on its pull_request trigger. The audit
    should now report its ``pr_target_filter_excludes_main`` field as True,
    closing the optional-residue gap that #12773 acceptance leaves open.
    """
    result = run(["--json"])
    assert result.returncode == 0, f"audit failed: {result.stderr}"
    data = json.loads(result.stdout)
    rows = data["rows"]
    target = next(
        (r for r in rows if r["name"] == "Orphaned delivery scan"),
        None,
    )
    assert target is not None, "Orphaned delivery scan workflow not found in audit"
    assert target.get("pr_target_filter_excludes_main") is True, (
        "branches-ignore: [main] should be detected as effective filter "
        "for the #10600 objective"
    )


def test_fanout_pr_target_main_subset_of_pulls():
    """#12773 : the ``pr-target-main`` fan-out estimate must be <= total
    pull_request count (subset semantics). With branches-ignore exclusions
    taken into account, it should be strictly less than the total.
    """
    result = run(["--json"])
    data = json.loads(result.stdout)
    pulls = data["workflows_pull_request"]
    n_main = data["fanout_estimated_per_pr_type"].get("pr-target-main")
    assert n_main is not None, "pr-target-main key missing from fanout"
    assert n_main <= pulls, (
        f"fanout for pr-target-main ({n_main}) exceeds total pulls ({pulls})"
    )


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