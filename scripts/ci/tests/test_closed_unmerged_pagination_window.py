"""Regression tests for complete closed-PR pagination (#25109)."""
from __future__ import annotations

import importlib.util
from datetime import datetime, timezone
from pathlib import Path


_MODULE_PATH = Path(__file__).resolve().parents[1] / "list_closed_unmerged_prs.py"
_SPEC = importlib.util.spec_from_file_location("list_closed_unmerged_prs_pagination", _MODULE_PATH)
lcu = importlib.util.module_from_spec(_SPEC)
assert _SPEC and _SPEC.loader
_SPEC.loader.exec_module(lcu)


def _pr(number: int, updated: str, *, closed: str | None = None, merged: bool = True):
    return {
        "number": number,
        "updated_at": updated,
        "closed_at": closed or updated,
        "merged_at": updated if merged else None,
    }


def test_closed_unmerged_reads_window_past_page_50():
    since = datetime(2026, 10, 9, tzinfo=timezone.utc)
    recent = "2026-10-20T12:00:00Z"
    pages = {
        page: [_pr(page * 100 + i, recent) for i in range(100)]
        for page in range(1, 51)
    }
    pages[51] = [_pr(5101, recent, merged=False)]
    seen: list[int] = []

    def fetch(page: int):
        seen.append(page)
        return pages.get(page, [])

    result = lcu.closed_unmerged("owner/repo", since, fetch_page=fetch)

    assert seen == list(range(1, 52))
    assert [pr["number"] for pr in result] == [5101]


def test_closed_unmerged_stops_after_updated_at_exits_window():
    since = datetime(2026, 10, 9, tzinfo=timezone.utc)
    recent_page = [_pr(i, "2026-10-20T12:00:00Z") for i in range(100)]
    old_page = [_pr(200 + i, "2026-10-08T12:00:00Z") for i in range(100)]
    seen: list[int] = []

    def fetch(page: int):
        seen.append(page)
        return {1: recent_page, 2: old_page}.get(page, [])

    result = lcu.closed_unmerged("owner/repo", since, fetch_page=fetch)

    assert seen == [1, 2]
    assert result == []
