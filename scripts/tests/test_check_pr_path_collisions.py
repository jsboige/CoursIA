#!/usr/bin/env python3
"""Tests for `scripts.check_pr_path_collisions` (issue #13359).

The detector core is PURE (no network, no `gh`); idempotency and comment
rendering are also pure. Only the CLI driver (`list_open_prs`,
`existing_comment`, `post_comment`) touches GitHub -- those are exercised by the
live `--dry-run`, not by these offline unit tests.

The positive control is a SYNTHETIC pair seeded directly into the pure
detector, so it is reproducible offline and fails loudly if the detector
breaks (the acceptance criterion for #13359 is that the control is present and
verifiable, not that it points at a volatile live pair).
"""
from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

_SCRIPT = Path(__file__).resolve().parent.parent / "check_pr_path_collisions.py"
_spec = importlib.util.spec_from_file_location("check_pr_path_collisions", _SCRIPT)
assert _spec and _spec.loader, f"could not load {_SCRIPT}"
_mod = importlib.util.module_from_spec(_spec)
sys.modules["check_pr_path_collisions"] = _mod
_spec.loader.exec_module(_mod)

PrRow = _mod.PrRow
PathCollision = _mod.PathCollision
detect_path_collisions = _mod.detect_path_collisions
collisions_for_pr = _mod.collisions_for_pr
render_comment = _mod.render_comment
find_marker_comment = _mod.find_marker_comment
COMMENT_MARKER_START = _mod.COMMENT_MARKER_START
SELF_TEST_PAIR = _mod.SELF_TEST_PAIR
SELF_TEST_SHARED_PATH = _mod.SELF_TEST_SHARED_PATH


def _pr(number: int, paths: list[str], title: str = "") -> PrRow:
    return PrRow(number=number, title=title, paths=tuple(paths))


class TestDetectPathCollisions(unittest.TestCase):
    def test_empty_input(self):
        result = detect_path_collisions([])
        self.assertEqual(result.total_prs_scanned, 0)
        self.assertEqual(result.n_collisions, 0)
        self.assertEqual(result.colliding_prs, [])

    def test_single_pr_unique_path(self):
        """Acceptance #1: a PR touching a path no other PR touches -> no collision."""
        result = detect_path_collisions([_pr(1, ["only/unique.ipynb"])])
        self.assertEqual(result.n_collisions, 0)
        self.assertEqual(result.colliding_prs, [])

    def test_positive_control_fabricated_pair(self):
        """Acceptance #2: two PRs sharing a path -> the pair is detected."""
        a, b = SELF_TEST_PAIR
        result = detect_path_collisions([
            _pr(a, [SELF_TEST_SHARED_PATH]),
            _pr(b, [SELF_TEST_SHARED_PATH]),
        ])
        self.assertEqual(result.n_collisions, 1)
        c = result.collisions[0]
        self.assertEqual((c.a_number, c.b_number), (a, b))
        self.assertIn(SELF_TEST_SHARED_PATH, c.shared_paths)
        self.assertEqual(result.colliding_prs, [a, b])

    def test_both_sides_warned_naming_other(self):
        """Acceptance #2 (cont): each side's comment names the other by number."""
        a, b = SELF_TEST_PAIR
        result = detect_path_collisions([
            _pr(a, [SELF_TEST_SHARED_PATH], title="A"),
            _pr(b, [SELF_TEST_SHARED_PATH], title="B"),
        ])
        ca = render_comment(a, "A", collisions_for_pr(a, result.collisions))
        cb = render_comment(b, "B", collisions_for_pr(b, result.collisions))
        self.assertIn(f"#{b}", ca)
        self.assertIn(f"#{a}", cb)

    def test_multi_path_aggregation(self):
        result = detect_path_collisions([
            _pr(10, ["x/a.ipynb", "x/b.ipynb"]),
            _pr(11, ["x/a.ipynb"]),
        ])
        self.assertEqual(result.n_collisions, 1)
        c = result.collisions[0]
        self.assertEqual(c.shared_paths, ("x/a.ipynb",))

    def test_pr_with_no_files_skipped(self):
        result = detect_path_collisions(
            [_pr(1, []), _pr(2, ["z.ipynb"])]
        )
        self.assertEqual(result.n_collisions, 0)

    def test_large_pool_over_thirty(self):
        """Acceptance #4: detection stays correct on a pool larger than 30."""
        prs = [_pr(n, [f"f{n}.ipynb"]) for n in range(1, 41)]
        prs.append(_pr(41, ["f1.ipynb"]))  # collides with PR 1
        result = detect_path_collisions(prs)
        self.assertEqual(result.total_prs_scanned, 41)
        self.assertEqual(result.n_collisions, 1)
        c = result.collisions[0]
        self.assertIn(1, (c.a_number, c.b_number))
        self.assertIn(41, (c.a_number, c.b_number))


class TestSameIssueFilter(unittest.TestCase):
    def test_same_issue_kept(self):
        """Two PRs sharing a path AND citing the same issue -> kept."""
        result = detect_path_collisions([
            _pr(1, ["x.ipynb"], title="fix(#11703): deliver X"),
            _pr(2, ["x.ipynb"], title="fix(#11703): deliver X (take 2)"),
        ])
        tbn = {1: "fix(#11703): deliver X", 2: "fix(#11703): deliver X (take 2)"}
        kept = _mod.filter_same_issue_collisions(result.collisions, tbn)
        self.assertEqual(len(kept), 1)
        self.assertEqual((kept[0].a_number, kept[0].b_number), (1, 2))

    def test_different_issue_dropped(self):
        """Shared path but different issues -> dropped (README-manifest noise)."""
        result = detect_path_collisions([
            _pr(1, ["README.md"], title="docs: fix intro (#100)"),
            _pr(2, ["README.md"], title="docs: fix links (#200)"),
        ])
        tbn = {1: "docs: fix intro (#100)", 2: "docs: fix links (#200)"}
        kept = _mod.filter_same_issue_collisions(result.collisions, tbn)
        self.assertEqual(kept, [])

    def test_issue_numbers_parser(self):
        self.assertEqual(_mod._issue_numbers("feat(a,b,#12/#13): x"), {12, 13})
        self.assertEqual(_mod._issue_numbers("no issue here"), set())


class TestCommentProtocol(unittest.TestCase):
    def test_render_comment_is_marker_framed(self):
        result = detect_path_collisions(
            [_pr(1, ["x.ipynb"]), _pr(2, ["x.ipynb"])]
        )
        body = render_comment(1, "t", collisions_for_pr(1, result.collisions))
        self.assertIn(COMMENT_MARKER_START, body)
        self.assertIn(_mod.COMMENT_MARKER_END, body)
        self.assertIn("#2", body)

    def test_find_marker_comment_idempotent(self):
        """Acceptance #3: a re-run finds the existing marker comment (no dup)."""
        comments = [
            {"id": 111, "body": "unrelated"},
            {"id": 222, "body": "noise <!-- PR-PATH-COLLISION:START --> tail"},
            {"id": 333, "body": "different"},
        ]
        self.assertEqual(find_marker_comment(comments), "222")

    def test_find_marker_comment_absent(self):
        self.assertIsNone(find_marker_comment([]))
        self.assertIsNone(find_marker_comment([{"id": 1, "body": "plain"}]))

    def test_deterministic_order(self):
        prs = [
            _pr(7, ["x.ipynb"]),
            _pr(3, ["x.ipynb", "y.ipynb"]),
            _pr(5, ["y.ipynb"]),
        ]
        result = detect_path_collisions(prs)
        numbers = [(c.a_number, c.b_number) for c in result.collisions]
        self.assertEqual(numbers, [(3, 5), (3, 7)])
        result2 = detect_path_collisions(prs)
        self.assertEqual(result.as_dict(), result2.as_dict())


if __name__ == "__main__":
    unittest.main()
