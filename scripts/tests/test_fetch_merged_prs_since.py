#!/usr/bin/env python3
"""Unit tests for fetch_merged_prs_since.py -- the merge-window fetcher (#12636).

The G-VAR-3 adjacency guard resolves a lane's REAL predecessor from the merged
sequence. The old fetch (`gh pr list --state merged --limit 100`) is ordered by
CREATION date, so with ~100 merges/day it covers roughly one day of creations
and a low-activity lane's grain merged a few days ago falls out of the batch
(the pre-#12095 regression, #12636). This helper pages the `merged:>=` window
(merge-time, not creation); these tests pin its pagination/dedup contract.

Run:
    python -m pytest scripts/tests/test_fetch_merged_prs_since.py
"""
import sys
from datetime import date, timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import fetch_merged_prs_since as fmps  # noqa: E402


def _pr(n: int, merged_at: str) -> dict:
    return {"number": n, "body": "some body", "mergedAt": merged_at}


def test_since_date_default_and_days():
    today = date.today()
    assert fmps.since_date(0) == today.isoformat()
    assert fmps.since_date(21) == (today - timedelta(days=21)).isoformat()


def test_fetch_paginates_and_dedupes():
    # Page 1 full, page 2 short -> both collected; a duplicate across pages dedupes.
    calls = []

    def fake_run(page, since):
        calls.append(page)
        if page == 1:
            return [_pr(i, f"2026-08-{i:02d}T00:00:00Z") for i in range(1, fmps.PAGE_SIZE + 1)]
        # short page carrying one duplicate of page-1's number 1
        return [_pr(1, "dup"), _pr(fmps.PAGE_SIZE + 1, "2026-08-31T00:00:00Z")]

    prs = fmps.fetch("2026-08-01", run=fake_run, max_pages=3)

    assert calls == [1, 2]                 # stopped on the short page
    nums = [p["number"] for p in prs]
    assert len(nums) == fmps.PAGE_SIZE + 1  # no duplicate kept
    assert 1 in nums and fmps.PAGE_SIZE + 1 in nums


def test_fetch_stops_at_max_pages():
    def fake_run(page, since):
        return [_pr(i + page * fmps.PAGE_SIZE, f"2026-08-{(i % 28) + 1:02d}T00:00:00Z")
                for i in range(1, fmps.PAGE_SIZE + 1)]

    prs = fmps.fetch("2026-08-01", run=fake_run, max_pages=3)

    assert len(prs) == fmps.PAGE_SIZE * 3
