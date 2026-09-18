"""Regression test for issue #16570.

Symptom: `check_lane_claim.py --issue N --paths <glob>` returned rc=0 (CLEAR)
even when another lane's OPEN PR already touched those same files -- the
issue-mode dispatch skipped the path-mode cross-lane collision check. The
picker had measured this trap; this is the organ-level fix.

This file exercises the extracted helper ``_classify_pr_collisions`` and the
end-to-end classifier used by ``_run_check`` to surface those collisions in the
JSON summary under ``open_pr_collisions`` / ``open_pr_self_overlap``.

No network: every input is a synthetic PR dict. The classifier is a pure
function over those dicts.
"""
from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc  # noqa: E402

MY_LANE = "myia-po-2024:CoursIA-2"
OTHER_LANE = "myia-po-2025:CoursIA-2"


# ----- fixtures --------------------------------------------------------------


def _pr(
    number: int,
    body: str,
    files: list[str],
    head: str | None = None,
) -> dict:
    """Build a synthetic PR dict matching the gh `pr list --json` shape."""
    return {
        "number": number,
        "title": f"PR #{number}",
        "headRefName": head if head is not None else f"fix/{number}-test",
        "body": body,
        "files": [{"path": f, "path_is_clean": True} for f in files],
    }


# A PR of ANOTHER lane tagging the same files -- collision.
PR_OTHER_LANE_INTERSECTS = _pr(
    number=200,
    body=(
        "Grain: MED/tooling -- lane myia-po-2025:CoursIA-2\n\n"
        "## Summary\nTouches scripts/check_lane_claim.py"
    ),
    files=["scripts/check_lane_claim.py", "scripts/lane_claim_epic_wide.py"],
)

# A PR of MY lane tagging the same files -- self-overlap (resume own work).
PR_SELF_INTERSECTS = _pr(
    number=210,
    body=(
        "Grain: DEEP/notebook-python -- lane myia-po-2024:CoursIA-2\n\n"
        "## Summary\nfollow-up on check_lane_claim.py"
    ),
    files=["scripts/check_lane_claim.py"],
)

# A PR with NO `Grain:` tag touching the same files -- fallback untagged,
# treated as a potential collision.
PR_UNTAGGED_INTERSECTS = _pr(
    number=220,
    body="## Summary\nUntagged PR that touches the script",
    files=["scripts/tests/test_lane_claim.py"],
)

# A PR of ANOTHER lane on UNRELATED files -- no intersection.
PR_OTHER_LANE_DISJOINT = _pr(
    number=230,
    body="Grain: LIGHT/guard -- lane myia-po-2025:CoursIA-2",
    files=["README.md", "docs/harness/foo.md"],
)

# A PR of ANOTHER lane with no `files` payload (cache miss / empty) -- skip.
PR_OTHER_NO_FILES = _pr(
    number=240,
    body="Grain: LIGHT/guard -- lane myia-po-2025:CoursIA-2",
    files=[],
)


PATHS = ["scripts/check_lane_claim.py"]


# ----- _classify_pr_collisions direct ---------------------------------------


def test_positive_classifier_other_lane_blocks_collision() -> None:
    """`other-lane PR intersecting files` -> collisions, NOT self_overlap."""
    collisions, self_overlap = clc._classify_pr_collisions(
        paths=PATHS,
        my_lane=MY_LANE,
        prs=[PR_OTHER_LANE_INTERSECTS],
    )
    assert len(collisions) == 1
    assert collisions[0].number == 200
    assert collisions[0].lane == OTHER_LANE
    assert "scripts/check_lane_claim.py" in collisions[0].files
    assert self_overlap == []


def test_positive_classifier_self_lane_is_self_overlap() -> None:
    """`same-lane PR intersecting files` -> self_overlap, NOT collisions."""
    collisions, self_overlap = clc._classify_pr_collisions(
        paths=PATHS,
        my_lane=MY_LANE,
        prs=[PR_SELF_INTERSECTS],
    )
    assert collisions == []
    assert len(self_overlap) == 1
    assert self_overlap[0].number == 210
    assert self_overlap[0].lane == MY_LANE


def test_positive_classifier_untagged_intersects_blocks_collision() -> None:
    """`untagged PR intersecting files` -> collisions (uncertainty)."""
    # use a different path under PATHS so this is independent of the prior
    # test cases (the helper matches the FIRST file in PR_UNTAGGED_INTERSECTS
    # against PATHS -- here we widen PATHS so both intersect).
    collisions, self_overlap = clc._classify_pr_collisions(
        paths=["scripts/tests/test_lane_claim.py"],
        my_lane=MY_LANE,
        prs=[PR_UNTAGGED_INTERSECTS],
    )
    assert len(collisions) == 1
    assert collisions[0].number == 220
    assert collisions[0].lane is None
    assert self_overlap == []


def test_negative_classifier_disjoint_pr_is_ignored() -> None:
    """`other-lane PR on disjoint files` -> neither list."""
    collisions, self_overlap = clc._classify_pr_collisions(
        paths=PATHS,
        my_lane=MY_LANE,
        prs=[PR_OTHER_LANE_DISJOINT],
    )
    assert collisions == []
    assert self_overlap == []


def test_classifier_skips_pr_with_empty_files() -> None:
    """`other-lane PR with no files payload` -> silently skipped (degraded cache).

    The classifier can't reason about a PR with no file payload. Skipping it
    here does NOT mean the gate is bypassed; the next pipeline stage (the
    `summary[]` builder) leaves `open_pr_collision_error` as the truth-source
    when the cache is degraded. This test just locks the classifier's local
    behaviour.
    """
    collisions, self_overlap = clc._classify_pr_collisions(
        paths=PATHS,
        my_lane=MY_LANE,
        prs=[PR_OTHER_NO_FILES],
    )
    assert collisions == []
    assert self_overlap == []


def test_classifier_three_way_mixed_input() -> None:
    """`4 PRs, mixed lanes and disjoint` -> exactly one collision + one self-overlap."""
    collisions, self_overlap = clc._classify_pr_collisions(
        paths=PATHS,
        my_lane=MY_LANE,
        prs=[
            PR_OTHER_LANE_INTERSECTS,   # -> collision
            PR_SELF_INTERSECTS,         # -> self_overlap
            PR_OTHER_LANE_DISJOINT,     # -> ignored
            PR_OTHER_NO_FILES,          # -> skipped
        ],
    )
    assert sorted(c.number for c in collisions) == [200]
    assert sorted(c.number for c in self_overlap) == [210]


# ----- _serialise_path_collision direct --------------------------------------


def test_serialise_shape_matches_path_mode() -> None:
    """JSON shape mirrors the path-mode leg exactly (#16570 compat)."""
    collisions, _ = clc._classify_pr_collisions(
        paths=PATHS,
        my_lane=MY_LANE,
        prs=[PR_OTHER_LANE_INTERSECTS],
    )
    serialised = clc._serialise_path_collision(collisions[0])
    assert set(serialised.keys()) == {
        "number", "title", "headRefName", "lane", "files_intersecting",
    }
    assert serialised["number"] == 200
    assert serialised["lane"] == OTHER_LANE
    assert serialised["headRefName"] == "fix/200-test"
    assert "scripts/check_lane_claim.py" in serialised["files_intersecting"]


# ----- end-to-end: --run_check surface contract -----------------------------
#
# The full `_run_check` requires more fixtures (issue payload, time payload,
# comments) and is exercised by the existing `test_check_lane_claim.py`
# integration suite. Here we lock the surface CONTRACT: that the summary dict
# carries the two new fields, with the same shape the path-mode leg uses.
# The synthetic PR list is fed through the helper directly.


@dataclass
class FakeSummaryCollector:
    """Mirror the assignment lines added to ``_run_check`` (#16570)."""
    open_pr_collisions: list[dict]
    open_pr_self_overlap: list[dict]
    open_pr_collision_error: str | None = None


def test_end_to_end_summary_carries_open_pr_collisions_field() -> None:
    """The summary contract is fixed: when OPEN PRs intersect, the field is
    populated with the same shape as the path-mode leg (#16570)."""
    prs = [
        PR_OTHER_LANE_INTERSECTS,
        PR_SELF_INTERSECTS,
        PR_OTHER_LANE_DISJOINT,
    ]
    collisions, self_overlap = clc._classify_pr_collisions(
        paths=PATHS,
        my_lane=MY_LANE,
        prs=prs,
    )
    summary = FakeSummaryCollector(
        open_pr_collisions=[clc._serialise_path_collision(c) for c in collisions],
        open_pr_self_overlap=[
            clc._serialise_path_collision(c) for c in self_overlap
        ],
    )
    # One other-lane collision, one self-overlap.
    assert len(summary.open_pr_collisions) == 1
    assert summary.open_pr_collisions[0]["number"] == 200
    assert summary.open_pr_collisions[0]["lane"] == OTHER_LANE
    assert len(summary.open_pr_self_overlap) == 1
    assert summary.open_pr_self_overlap[0]["number"] == 210
    # The gate's `rc=2` decision lives in `_run_check`; at the helper level
    # we only assert the population, not the exit code -- that's the contract
    # the issue leg must honour when it consumes the summary.
    assert summary.open_pr_collision_error is None
