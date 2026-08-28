#!/usr/bin/env python3
"""Tests for `scripts.issue_create_idempotent`.

Two scopes:
- Unit tests on `find_recent_duplicate` with injectable `_gh_issue_list_by_title`.
- A network-gated live test that runs the CLI against the real repo and
  verifies `--check-only` reports no recent dup under a unique title.
"""
from __future__ import annotations

import importlib.util
import os
import subprocess
import sys
import unittest
from datetime import datetime, timedelta, timezone
from pathlib import Path
from unittest import mock

_SCRIPT = Path(__file__).resolve().parent.parent / "issue_create_idempotent.py"
_spec = importlib.util.spec_from_file_location(
    "issue_create_idempotent", _SCRIPT,
)
assert _spec and _spec.loader, f"could not load {_SCRIPT}"
_mod = importlib.util.module_from_spec(_spec)
sys.modules["issue_create_idempotent"] = _mod
_spec.loader.exec_module(_mod)

find_recent_duplicate = _mod.find_recent_duplicate
create_issue_idempotent = _mod.create_issue_idempotent
_gh_issue_list_by_title = _mod._gh_issue_list_by_title


_FIXED_NOW = datetime(2026, 8, 26, 12, 0, 0, tzinfo=timezone.utc)


class TestFindRecentDuplicate(unittest.TestCase):
    def _mock_gh_returning(self, rows):
        """Patch _gh_issue_list_by_title to return the given rows."""
        return mock.patch.object(
            _mod, "_gh_issue_list_by_title", return_value=rows,
        )

    def test_no_match_returns_none(self):
        # Issue is 1 hour before _FIXED_NOW -- outside the 10-min window.
        rows = [
            {"number": 1, "title": "foo", "createdAt": "2026-08-26T11:00:00Z",
             "state": "OPEN"},
        ]
        with self._mock_gh_returning(rows):
            result = find_recent_duplicate(
                "foo", window_minutes=10, now=_FIXED_NOW,
            )
        self.assertIsNone(result)

    def test_match_within_window(self):
        rows = [
            {"number": 42, "title": "foo", "createdAt": "2026-08-26T11:55:00Z",
             "state": "OPEN"},
        ]
        with self._mock_gh_returning(rows):
            result = find_recent_duplicate(
                "foo", window_minutes=10, now=_FIXED_NOW,
            )
        self.assertIsNotNone(result)
        self.assertEqual(result["number"], 42)

    def test_match_outside_window(self):
        rows = [
            {"number": 42, "title": "foo", "createdAt": "2026-08-26T11:00:00Z",
             "state": "OPEN"},  # 1 h avant
        ]
        with self._mock_gh_returning(rows):
            result = find_recent_duplicate(
                "foo", window_minutes=10, now=_FIXED_NOW,
            )
        self.assertIsNone(result)

    def test_returns_most_recent_of_many(self):
        rows = [
            {"number": 1, "title": "foo", "createdAt": "2026-08-26T11:50:00Z",
             "state": "CLOSED"},
            {"number": 2, "title": "foo", "createdAt": "2026-08-26T11:55:00Z",
             "state": "OPEN"},
            {"number": 3, "title": "foo", "createdAt": "2026-08-26T11:58:00Z",
             "state": "OPEN"},
        ]
        with self._mock_gh_returning(rows):
            result = find_recent_duplicate(
                "foo", window_minutes=15, now=_FIXED_NOW,
            )
        self.assertEqual(result["number"], 3)

    def test_title_strict_equality(self):
        """gh returns rows with similar titles -- the helper must match exactly.

        GitHub search is fuzzy; we filter by exact title equality ourselves.
        We sort by createdAt and pick the most recent -- so the most recent
        EXACT match wins, not the first one in the list.
        """
        rows = [
            {"number": 1, "title": "foo bar", "createdAt": "2026-08-26T11:55:00Z",
             "state": "OPEN"},
            {"number": 2, "title": "foo", "createdAt": "2026-08-26T11:58:00Z",
             "state": "OPEN"},
        ]
        with self._mock_gh_returning(rows):
            result = find_recent_duplicate(
                "foo", window_minutes=10, now=_FIXED_NOW,
            )
        self.assertEqual(result["number"], 2)

    def test_title_with_whitespace_normalized(self):
        """gh may echo leading/trailing whitespace; we strip before comparing."""
        rows = [
            {"number": 1, "title": "  foo  ", "createdAt": "2026-08-26T11:55:00Z",
             "state": "OPEN"},
        ]
        with self._mock_gh_returning(rows):
            result = find_recent_duplicate(
                "foo", window_minutes=10, now=_FIXED_NOW,
            )
        self.assertEqual(result["number"], 1)


class TestCreateIssueIdempotent(unittest.TestCase):
    def test_skips_when_recent_duplicate_exists(self):
        rows = [
            {"number": 100, "title": "foo", "createdAt": "2026-08-26T11:55:00Z",
             "state": "OPEN"},
        ]
        with mock.patch.object(_mod, "_gh_issue_list_by_title",
                               return_value=rows), \
             mock.patch.object(_mod.subprocess, "run") as mock_run:
            new_number, existing = create_issue_idempotent(
                "foo", "body", label="x",
                window_minutes=10, dry_run=False, now=_FIXED_NOW,
            )
        self.assertIsNone(new_number)
        self.assertIsNotNone(existing)
        self.assertEqual(existing["number"], 100)
        mock_run.assert_not_called()  # never invoked gh issue create

    def test_proceeds_when_no_recent_duplicate(self):
        with mock.patch.object(_mod, "_gh_issue_list_by_title",
                               return_value=[]), \
             mock.patch.object(_mod.subprocess, "run") as mock_run:
            mock_run.return_value.returncode = 0
            mock_run.return_value.stdout = (
                "https://github.com/jsboige/CoursIA/issues/999\n"
            )
            mock_run.return_value.stderr = ""
            new_number, existing = create_issue_idempotent(
                "foo", "body", label="x",
                window_minutes=10, dry_run=False, now=_FIXED_NOW,
            )
        self.assertEqual(new_number, 999)
        self.assertIsNone(existing)
        mock_run.assert_called_once()
        args = mock_run.call_args[0][0]
        self.assertEqual(args[:3], ["gh", "issue", "create"])
        self.assertIn("--title", args)
        self.assertIn("foo", args)

    def test_dry_run_skips_even_when_no_dup(self):
        """In dry-run, no `gh issue create` is invoked."""
        with mock.patch.object(_mod, "_gh_issue_list_by_title",
                               return_value=[]), \
             mock.patch.object(_mod.subprocess, "run") as mock_run:
            new_number, existing = create_issue_idempotent(
                "foo", "body", label=None,
                window_minutes=10, dry_run=True, now=_FIXED_NOW,
            )
        self.assertIsNone(new_number)
        self.assertIsNone(existing)
        mock_run.assert_not_called()

    def test_gh_create_failure_raises(self):
        with mock.patch.object(_mod, "_gh_issue_list_by_title",
                               return_value=[]), \
             mock.patch.object(_mod.subprocess, "run") as mock_run:
            mock_run.return_value.returncode = 1
            mock_run.return_value.stderr = "auth required"
            with self.assertRaises(RuntimeError) as ctx:
                create_issue_idempotent(
                    "foo", "body", label=None,
                    window_minutes=10, dry_run=False, now=_FIXED_NOW,
                )
        self.assertIn("auth required", str(ctx.exception))


class TestCLILive(unittest.TestCase):
    """Network-gated: requires `gh auth` against jsboige/CoursIA."""

    def test_check_only_unique_title(self):
        if not os.environ.get("ISSUE_DEDUP_NETWORK"):
            self.skipTest("set ISSUE_DEDUP_NETWORK=1 to run live CLI test")
        # A title that's almost certainly unique: includes the test timestamp.
        unique_title = (
            f"TEST-detect-dup-cli-{datetime.now(timezone.utc).isoformat()}"
        )
        proc = subprocess.run(
            [
                sys.executable, str(_SCRIPT),
                "--check-only", "--title", unique_title,
                "--window-minutes", "10",
            ],
            capture_output=True, text=True, timeout=30,
        )
        self.assertEqual(proc.returncode, 0, msg=proc.stdout + proc.stderr)
        self.assertIn("no-recent-duplicate", proc.stdout)


if __name__ == "__main__":
    unittest.main()
