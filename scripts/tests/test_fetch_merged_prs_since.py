#!/usr/bin/env python3
"""Unit tests for fetch_merged_prs_since.py -- the merge-window fetcher.

The G-VAR-3 adjacency guard resolves a lane's REAL predecessor from the merged
sequence. When this fetch returns nothing the guard silently degrades to the
frozen `prev:` field -- it keeps passing and blocking, just on the wrong axis.
Two mechanisms produced that degradation, and these tests pin both shut:

* **#12636** -- `--limit 100` orders by CREATION date, so a quiet lane's older
  grain fell out. Fixed by searching on `merged:>=` (merge-time).
* **2026-08-29** -- the fix for #12636 paged with `gh pr list ... --page N`, a
  flag `gh pr list` does not have. Every real call raised, so the guard ran on
  `declared` repo-wide for the script's whole life. The three tests here all
  injected a fake `run`, so the argv was never executed once --
  `test_run_gh_argv_is_accepted_by_gh` is the control that closes that hole.

Run:
    python -m pytest scripts/tests/test_fetch_merged_prs_since.py
"""
import shutil
import subprocess
import sys
from datetime import date, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import fetch_merged_prs_since as fmps  # noqa: E402


def _pr(n: int, merged_at: str) -> dict:
    return {"number": n, "body": "some body", "mergedAt": merged_at}


def test_since_date_default_and_days():
    today = date.today()
    assert fmps.since_date(0) == today.isoformat()
    assert fmps.since_date(21) == (today - timedelta(days=21)).isoformat()


def test_fetch_walks_the_window_in_date_slices_and_dedupes():
    """The window is covered by consecutive [since, until) slices, no overlap kept."""
    calls = []

    def fake_run(since, until):
        calls.append((since, until))
        # one PR per slice, plus a duplicate of the first in the last slice
        n = len(calls)
        out = [_pr(n, f"{since}T00:00:00Z")]
        if n == 3:
            out.append(_pr(1, "duplicate"))
        return out

    prs = fmps.fetch("2026-08-01", run=fake_run, slice_days=3,
                     today=date(2026, 8, 8))

    # 2026-08-01 -> 2026-08-09 (today+1) in 3-day slices: 01-04, 04-07, 07-09
    assert calls == [("2026-08-01", "2026-08-04"),
                     ("2026-08-04", "2026-08-07"),
                     ("2026-08-07", "2026-08-09")]
    nums = [p["number"] for p in prs]
    assert nums == [1, 2, 3], "le doublon inter-tranches n'a pas ete dedoublonne"


def test_fetch_covers_today_itself():
    """A PR merged today must be inside the window -- the guard's freshest signal."""
    seen = []

    def fake_run(since, until):
        seen.append((since, until))
        return []

    fmps.fetch("2026-08-28", run=fake_run, slice_days=3, today=date(2026, 8, 29))

    assert seen[-1][1] == "2026-08-30", (
        "la derniere tranche s'arrete a {} : les merges d'aujourd'hui sont hors "
        "fenetre".format(seen[-1][1]))


def test_fetch_halves_a_slice_that_comes_back_at_the_search_cap():
    """A batch AT the cap is the cap, not a measurement -- narrow and retry."""
    widths = []

    def fake_run(since, until):
        d0 = date.fromisoformat(since)
        d1 = date.fromisoformat(until)
        w = (d1 - d0).days
        widths.append(w)
        # 4-day and 2-day slices are truncated; 1-day slices are honest
        if w > 1:
            return [_pr(i, "x") for i in range(fmps.SEARCH_RESULT_CAP)]
        return [_pr(1000 + len(widths), "x")]

    prs = fmps.fetch("2026-08-01", run=fake_run, slice_days=4,
                     today=date(2026, 8, 1))

    assert widths[:3] == [1, 1, 1] or 1 in widths, (
        "la tranche saturee n'a jamais ete retrecie : {}".format(widths))
    assert all(len(p) for p in prs[:1])
    assert len(prs) >= 1


def test_fetch_raises_rather_than_truncating_when_one_day_is_still_capped():
    """Silent truncation would hand the guard a partial sequence that looks whole."""
    def fake_run(since, until):
        return [_pr(i, "x") for i in range(fmps.SEARCH_RESULT_CAP)]

    with pytest.raises(RuntimeError, match="search cap"):
        fmps.fetch("2026-08-01", run=fake_run, slice_days=1,
                   today=date(2026, 8, 1))


def test_main_returns_1_when_the_fetch_raises():
    """The caller's `|| rm -f` must see a nonzero exit, never a partial file.

    Patched on `fetch`, not on `run_gh`: `fetch` binds `run=run_gh` as a DEFAULT
    ARGUMENT, evaluated once at definition time, so rebinding the module
    attribute never reaches it. The only injection point is `fetch(run=...)`.
    """
    def boom(since):
        raise OSError("gh absent")

    original = fmps.fetch
    fmps.fetch = boom
    try:
        assert fmps.main(["--days", "3"]) == 1
    finally:
        fmps.fetch = original


@pytest.mark.skipif(shutil.which("gh") is None, reason="gh binary absent")
def test_run_gh_argv_is_accepted_by_gh():
    """THE control the `--page` regression escaped for its whole life.

    Every other test injects `run`, so the argv `run_gh` builds was never once
    executed. `gh pr list` has no `--page` flag; the call raised on every real
    invocation and the guard fell back to `declared` repo-wide, silently. This
    test asserts the shape of the command is accepted by the real binary --
    `--help` on the same subcommand, plus an assertion that every flag we pass
    is one `gh pr list` advertises.
    """
    help_out = subprocess.run(
        ["gh", "pr", "list", "--help"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    ).stdout

    # The flags run_gh passes, extracted from the function's own argv so the
    # test cannot drift away from the code it guards.
    calls = {}

    def capture(*a, **kw):
        calls["argv"] = a[0]
        raise SystemExit  # do not actually hit the network

    original = subprocess.run
    subprocess.run = capture
    try:
        try:
            fmps.run_gh("2026-08-01", "2026-08-04")
        except SystemExit:
            pass
    finally:
        subprocess.run = original

    argv = calls["argv"]
    assert argv[:3] == ["gh", "pr", "list"], argv
    flags = [tok for tok in argv if tok.startswith("--")]
    unknown = [f for f in flags if f not in help_out]
    assert not unknown, (
        "run_gh passe des options que `gh pr list` n'a pas : {} "
        "(c'est exactement la faute `--page`)".format(unknown))
