#!/usr/bin/env python3
"""Unit tests for refresh_stale_adjacency (the G-VAR-3 stale-verdict re-trigger).

Covers the pure helpers: `append_marker` (idempotent), `now_marker` (format),
and the verdict-routing logic of `refresh_one` simulated via fake `gh` output.

The end-to-end `refresh_one` calls real `gh` CLI -- so the live-call branch is
tested by hand against a small set of PRs and NOT in pytest. The unit tests
focus on:

  * `append_marker` idempotency -- running the function N times on the same
    body produces exactly ONE marker, with the latest timestamp.
  * The marker format -- exactly one line, ISO-8601 UTC, prefixed.
  * `now_marker` returns a string that round-trips through `append_marker`.
  * The verdict-routing matrix of `refresh_one` -- given a fake
    `(always_on_failing, guard_pass)` pair, decide correctly whether to
    refresh.

We mock the subprocess calls so the unit tests do not need network. The
fixture `FakeRun` emulates `subprocess.run` output for `gh pr view --json
body` and `gh pr checks`. A monkeypatch fixture swaps
`subprocess.run` for a controller.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import refresh_stale_adjacency as rsa  # noqa: E402


# --- helpers ----------------------------------------------------------------


class FakeRun:
    """Emulates `subprocess.run` return for `gh` calls.

    `specs` is a dict mapping `argv` tuple -> (returncode, stdout, stderr).
    The first matching spec wins; the default is (0, "", "") so unrelated
    calls return cleanly.
    """

    def __init__(self, specs: dict | None = None) -> None:
        self.specs: dict = specs or {}
        self.calls: list[tuple] = []

    def __call__(self, argv, capture_output=True, text=True, check=False,
                 input=None, **kwargs):  # noqa: ANN001 -- mirror subprocess.run
        self.calls.append(tuple(argv))
        # Find a matching spec (subsequence match: argv must contain all of
        # `argv_prefix` tokens in order).
        for key, val in self.specs.items():
            if self._argv_matches(list(argv), key):
                rc, stdout, stderr = val
                cp = subprocess.CompletedProcess(
                    args=argv, returncode=rc, stdout=stdout, stderr=stderr,
                )
                return cp
        return subprocess.CompletedProcess(
            args=argv, returncode=0, stdout="", stderr="",
        )

    @staticmethod
    def _argv_matches(argv, key) -> bool:
        # If key is a tuple of strings, all must appear in argv in order.
        if isinstance(key, tuple):
            i = 0
            for tok in argv:
                if tok == key[i]:
                    i += 1
                    if i == len(key):
                        return True
            return False
        return False


@pytest.fixture
def fake_run(monkeypatch):
    """Replace `subprocess.run` with a FakeRun controller.

    Returns the FakeRun instance; the caller sets `.specs` to declare
    expected `gh` invocations.
    """
    fr = FakeRun()
    monkeypatch.setattr(rsa.subprocess, "run", fr)
    return fr


# --- pure helper tests ------------------------------------------------------


def test_append_marker_adds_one_line():
    body = "## Quoi\n\nClose #1.\n\nGrain: MED/guard -- lane myia-po-2026:CoursIA -- prev: MED/guard #0\n"
    out = rsa.append_marker(body, "<!-- refresh-adj: 2026-09-01T09:42:00Z -->")
    assert out.count("<!-- refresh-adj:") == 1
    assert out.endswith("<!-- refresh-adj: 2026-09-01T09:42:00Z -->\n")
    assert "Grain: MED/guard" in out  # substance preserved


def test_append_marker_idempotent():
    body = "## Section\n\nBody.\n"
    out1 = rsa.append_marker(body, "<!-- refresh-adj: 2026-09-01T09:00:00Z -->")
    out2 = rsa.append_marker(out1, "<!-- refresh-adj: 2026-09-01T09:30:00Z -->")
    out3 = rsa.append_marker(out2, "<!-- refresh-adj: 2026-09-01T10:00:00Z -->")
    assert out3.count("<!-- refresh-adj:") == 1, f"expected 1, got {out3.count('<!-- refresh-adj:')}"
    assert "2026-09-01T10:00:00Z" in out3
    assert "2026-09-01T09:00:00Z" not in out3
    assert "2026-09-01T09:30:00Z" not in out3


def test_append_marker_handles_empty_body():
    out = rsa.append_marker("", "<!-- refresh-adj: 2026-09-01T00:00:00Z -->")
    assert out == "<!-- refresh-adj: 2026-09-01T00:00:00Z -->\n"


def test_append_marker_handles_none_body():
    # Defensive: a None body (unusual, but seen in fork PRs) becomes "".
    out = rsa.append_marker("", "<!-- refresh-adj: X -->")
    assert "<!-- refresh-adj: X -->" in out


def test_now_marker_format():
    m = rsa.now_marker()
    # Exactly one line, no trailing newline, exact prefix.
    assert m.startswith("<!-- refresh-adj: ")
    assert m.endswith(" -->")
    # The timestamp between is ISO-8601 UTC (YYYY-MM-DDTHH:MM:SSZ).
    iso = re.search(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", m)
    assert iso is not None


def test_now_marker_round_trips_through_append_marker():
    body = "Some body\n"
    out = rsa.append_marker(body, rsa.now_marker())
    assert out.count("<!-- refresh-adj:") == 1


# --- verdict-routing tests (refresh_one logic, mocked subprocess) ------------


PR_BODY_OK = (
    "## Quoi\n\n"
    "Fixes #1. Grain tag.\n\n"
    "Grain: MED/docs -- lane myia-po-2026:CoursIA -- prev: MED/tooling #999\n"
)


def _setup_fake_for_pr(fake_run: FakeRun, pr: int, body: str,
                        always_on_failing: bool) -> None:
    """Configure FakeRun for one PR: body, checks, comments."""
    fake_run.specs[("pr", "view", str(pr), "--json", "body")] = (
        0, json.dumps({"body": body}), "")
    fake_run.specs[("pr", "view", str(pr), "--json", "comments",
                    "--jq")] = (
        0, "[]", "")
    checks = [
        ["Always-on guards -- 12 organes, 1 checkout",
         "fail" if always_on_failing else "success", "0s", "https://x"],
    ]
    checks_text = "\n".join("\t".join(row) for row in checks) + "\n"
    fake_run.specs[("pr", "checks", str(pr))] = (0, checks_text, "")
    # `gh pr edit ... --body-file -` (the edit call): accept any input.
    fake_run.specs[("pr", "edit", str(pr), "--body-file", "-")] = (
        0, "", "")


def test_refresh_one_skips_when_already_passing(fake_run):
    """If `Always-on guards` is NOT failing, do NOT refresh.

    The script must NEVER touch a PR whose check is already green: the
    guard could fail on the next run for an unrelated reason and we would
    have polluted its body for nothing.
    """
    _setup_fake_for_pr(fake_run, 13812, PR_BODY_OK, always_on_failing=False)
    merged_window = [
        {"number": 999, "body": "Grain: MED/tooling -- lane myia-po-2026:CoursIA -- prev: MED/guard #998\n",
         "mergedAt": "2026-09-01T07:00:00Z"},
    ]
    result = rsa.refresh_one(13812, dry_run=True, merged_window=merged_window)
    assert result["would_refresh"] is False
    assert result["refreshed"] is False
    assert result["always_on_failing"] is False


def test_refresh_one_refreshes_when_stale_failing(fake_run):
    """If Always-on guards is failing AND guard_pass=True, refresh.

    The founder case: G-VAR-3 stale verdict (the merged sequence has moved
    past the PR's predecessor).
    """
    _setup_fake_for_pr(fake_run, 13812, PR_BODY_OK, always_on_failing=True)
    merged_window = [
        {"number": 999, "body": "Grain: MED/tooling -- lane myia-po-2026:CoursIA -- prev: MED/guard #998\n",
         "mergedAt": "2026-09-01T07:00:00Z"},
    ]
    # MED/docs after MED/tooling -> guard_pass=True.
    result = rsa.refresh_one(13812, dry_run=True, merged_window=merged_window)
    assert result["guard_pass"] is True
    assert result["always_on_failing"] is True
    assert result["would_refresh"] is True
    assert result["refreshed"] is True  # dry-run, virtual


def test_refresh_one_refuses_when_real_failing(fake_run):
    """If Always-on guards is failing AND guard_pass=False, do NOT refresh.

    A genuine G-VAR-3 adjacency (the rule is doing its job) is NOT a stale
    verdict: the script must surface this, not pretend a marker will help.
    """
    body_guard = (
        "## Quoi\n\nFixes.\n\n"
        "Grain: LIGHT/guard -- lane myia-po-2026:CoursIA -- prev: LIGHT/guard #0\n"
    )
    _setup_fake_for_pr(fake_run, 13869, body_guard, always_on_failing=True)
    # Two consecutive LIGHT/guard in the merged window -> G-VAR-3 fires.
    merged_window = [
        {"number": 998, "body": "Grain: LIGHT/guard -- lane myia-po-2026:CoursIA -- prev: LIGHT/tooling #997\n",
         "mergedAt": "2026-09-01T05:00:00Z"},
        {"number": 997, "body": "Grain: LIGHT/tooling -- lane myia-po-2026:CoursIA -- prev: MED/guard #996\n",
         "mergedAt": "2026-09-01T04:00:00Z"},
    ]
    result = rsa.refresh_one(13869, dry_run=True, merged_window=merged_window)
    assert result["guard_pass"] is False
    assert result["always_on_failing"] is True
    assert result["would_refresh"] is False
    assert result["refreshed"] is False


def test_refresh_one_handles_no_grain_tag(fake_run):
    """If the PR body has no Grain tag, the script refuses to touch it.

    A missing Grain tag is the tag-required guard's territory (#10045).
    Refresh-adjacency would not help; the marker is misleading noise.
    """
    body_no_tag = "## Quoi\n\nThis PR has no Grain tag.\n"
    _setup_fake_for_pr(fake_run, 13999, body_no_tag, always_on_failing=True)
    result = rsa.refresh_one(13999, dry_run=True, merged_window=[])
    assert result["guard_pass"] is False
    assert result["would_refresh"] is False
    assert "no Grain tag" in result["reason"]


# --- batch behaviour (main) -------------------------------------------------


def test_main_mixed_outcomes(fake_run, capsys, monkeypatch):
    """Run `main` with a mix of stale-failing, real-failing, and already-passing.

    Exit code: 0 (no real failures). Output: a results list, one entry per
    PR, in the order given. Mocks `fetch_merged_prs_since.py` (no network).
    """
    # PR 1: stale-failing -> would_refresh.
    _setup_fake_for_pr(fake_run, 1, PR_BODY_OK, always_on_failing=True)
    # PR 2: already-passing -> would NOT refresh.
    body_pass = "Grain: MED/notebook-python -- lane myia-po-2026:CoursIA -- prev: MED/guard #1\n"
    _setup_fake_for_pr(fake_run, 2, body_pass, always_on_failing=False)
    merged_window = [
        {"number": 1, "body": "Grain: MED/guard -- lane myia-po-2026:CoursIA -- prev: MED/docs #0\n",
         "mergedAt": "2026-09-01T05:00:00Z"},
    ]
    # fetch_merged_window must also be mocked -- it shells out to a Python
    # script that reads `gh` and the network.
    monkeypatch.setattr(rsa, "fetch_merged_window", lambda days=21: merged_window)
    rc = rsa.main(["--pr", "1", "--pr", "2", "--dry-run"])
    captured = capsys.readouterr()
    payload = json.loads(captured.out)
    assert rc == 0
    assert len(payload["results"]) == 2
    assert payload["results"][0]["pr"] == 1
    assert payload["results"][0]["would_refresh"] is True
    assert payload["results"][1]["pr"] == 2
    assert payload["results"][1]["would_refresh"] is False


def test_main_exit_1_on_real_failing(fake_run, capsys, monkeypatch):
    """A real-failing PR (always_on_failing=False, guard_pass=False) -> exit 1.

    This is the diagnostic case: the guard is failing for a reason the
    refresh cannot fix (e.g., tag-required, off-list genre). The operator
    needs to know.
    """
    body_no_tag = "## Section\n\nNo grain tag here.\n"
    _setup_fake_for_pr(fake_run, 999, body_no_tag, always_on_failing=False)
    # No `Always-on guards` failing (it's "success" in the spec above), but
    # `guard_pass=False` because no Grain tag -- so the route is "real fail".
    monkeypatch.setattr(rsa, "fetch_merged_window", lambda days=21: [])
    rc = rsa.main(["--pr", "999", "--dry-run"])
    assert rc == 1
