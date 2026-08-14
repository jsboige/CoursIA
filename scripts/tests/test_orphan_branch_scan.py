#!/usr/bin/env python3
"""Unit tests for the pure classification core of orphan_branch_scan.py (#10918).

The ``classify_branch`` function is network-free; ``main`` (the gh/git wiring)
is exercised end-to-end in CI dry-runs, not here. The fixtures encode the three
test cases measured firsthand on 2026-08-14 (issue #10918, last 200 merged
PRs): #10770 and #10684 orphaned deliverables (must surface), #10791 did NOT
(byte-identical content despite being a non-ancestor -- the ancestrality trap).
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from orphan_branch_scan import classify_branch, STATUS_SAME, STATUS_DIFF, STATUS_ABSENT  # noqa: E402


def _content(*statuses):
    """Build a content diff from status->path pairs like (STATUS_ABSENT, 'x.ipynb')."""
    return [{"path": p, "status": s} for s, p in statuses]


def test_orphan_absent_file():
    # Mirrors #10770: Lean-20 absent on main, not ancestor, no open PR.
    verdict, _ = classify_branch(
        "feature/c8266-sendov-theoremes",
        exists=True, is_ancestor_of_main=False, open_prs_to_main=0,
        content=_content((STATUS_ABSENT, "Lean-20-Analysis-I-Tao-Workflow.ipynb"),
                         (STATUS_SAME, "Lean-19-Sendov-Complex-Analysis.ipynb")),
    )
    assert verdict == "orphan"


def test_orphan_diff_file():
    # Mirrors #10684: Z3-Python-13 enrichment differs from main.
    verdict, _ = classify_branch(
        "fix/gitleaks-pin-8243",
        exists=True, is_ancestor_of_main=False, open_prs_to_main=0,
        content=_content((STATUS_DIFF, "Z3-Python-13-UnsatCores.ipynb")),
    )
    assert verdict == "orphan"


def test_same_content_not_flagged():
    # Mirrors #10791: non-ancestor but byte-identical content -- NOT orphan.
    verdict, why = classify_branch(
        "feature/c245-lean17-knots-headers-phase2",
        exists=True, is_ancestor_of_main=False, open_prs_to_main=0,
        content=_content((STATUS_SAME, "Lean-17-Knots-a-Conway-and-Proofs.ipynb")),
    )
    assert verdict == "same"
    assert "byte-identique" in why


def test_integrated_ancestor_not_flagged():
    verdict, _ = classify_branch(
        "feature/merged-long-ago",
        exists=True, is_ancestor_of_main=True, open_prs_to_main=0, content=[],
    )
    assert verdict == "integrated"


def test_legitimate_stack_not_flagged():
    # An open PR towards main exists -- the deliverable is in flight.
    verdict, _ = classify_branch(
        "feature/in-flight",
        exists=True, is_ancestor_of_main=False, open_prs_to_main=1,
        content=_content((STATUS_DIFF, "x.ipynb")),
    )
    assert verdict == "stacked"


def test_branch_gone():
    verdict, _ = classify_branch(
        "feature/deleted", exists=False, is_ancestor_of_main=False,
        open_prs_to_main=0, content=[],
    )
    assert verdict == "gone"


def test_empty_content_is_same_not_orphan():
    # Branch that changed nothing vs main: no lost deliverable.
    verdict, _ = classify_branch(
        "feature/empty", exists=True, is_ancestor_of_main=False,
        open_prs_to_main=0, content=[],
    )
    assert verdict == "same"
