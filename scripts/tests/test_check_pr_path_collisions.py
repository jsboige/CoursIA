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


class TestThreeVerbs(unittest.TestCase):
    """#13489: post/update/retract planned over the UNION colliding ∪ markers."""

    def _collision(self, a, b, path="shared/x.ipynb"):
        return PathCollision(a_number=a, b_number=b, shared_paths=(path,))

    def test_union_covers_marker_carrier_no_longer_colliding(self):
        """THE structural fix: a resolved PR stays in the iteration set.

        Before #13489 the loop iterated colliding PRs only, so a PR whose
        neighbour merged was never visited again and its stale advisory could
        never be retracted.
        """
        plan = _mod.plan_actions(
            colliding_prs=[10],
            collisions=[self._collision(10, 11)],
            title_by_number={10: "A", 11: "B"},
            marker_by_number={
                20: ("999", _mod.render_comment(20, "old", [self._collision(20, 21)]))
            },
            resolved_on="2026-08-29T00:00Z",
        )
        retracts = [a for a in plan if a.verb == "retract"]
        self.assertEqual([a.number for a in retracts], [20])
        self.assertEqual(retracts[0].comment_id, "999")
        self.assertIn(_mod.RESOLVED_SIGNATURE, retracts[0].body)

    def test_post_when_no_marker(self):
        plan = _mod.plan_actions(
            colliding_prs=[10, 11],
            collisions=[self._collision(10, 11)],
            title_by_number={10: "A", 11: "B"},
            marker_by_number={10: None, 11: None},
            resolved_on="2026-08-29T00:00Z",
        )
        self.assertEqual(
            [(a.number, a.verb) for a in plan], [(10, "post"), (11, "post")]
        )

    def test_update_when_body_drifted(self):
        """Neighbour changed: the old comment names the WRONG PR -> refresh."""
        old_body = _mod.render_comment(10, "A", [self._collision(10, 99)])
        plan = _mod.plan_actions(
            colliding_prs=[10],
            collisions=[self._collision(10, 11)],
            title_by_number={10: "A"},
            marker_by_number={10: ("77", old_body)},
            resolved_on="2026-08-29T00:00Z",
        )
        updates = [a for a in plan if a.verb == "update"]
        self.assertEqual(len(updates), 1)
        self.assertEqual(updates[0].comment_id, "77")
        self.assertIn("#11", updates[0].body)

    def test_none_when_body_current(self):
        body = _mod.render_comment(10, "A", [self._collision(10, 11)])
        plan = _mod.plan_actions(
            colliding_prs=[10],
            collisions=[self._collision(10, 11)],
            title_by_number={10: "A"},
            marker_by_number={10: ("77", body)},
            resolved_on="2026-08-29T00:00Z",
        )
        self.assertEqual([(a.number, a.verb) for a in plan], [(10, "none")])

    def test_recollision_swaps_resolution_note_back_to_advisory(self):
        note = _mod.render_resolution_comment(10, "2026-08-28T00:00Z")
        plan = _mod.plan_actions(
            colliding_prs=[10],
            collisions=[self._collision(10, 11)],
            title_by_number={10: "A"},
            marker_by_number={10: ("77", note)},
            resolved_on="2026-08-29T00:00Z",
        )
        self.assertEqual([(a.number, a.verb) for a in plan], [(10, "update")])
        self.assertNotIn(_mod.RESOLVED_SIGNATURE, plan[0].body)

    def test_already_resolved_stays_none(self):
        note = _mod.render_resolution_comment(20, "2026-08-28T00:00Z")
        plan = _mod.plan_actions(
            colliding_prs=[],
            collisions=[],
            title_by_number={},
            marker_by_number={20: ("77", note)},
            resolved_on="2026-08-29T00:00Z",
        )
        self.assertEqual([(a.number, a.verb) for a in plan], [(20, "none")])

    def test_resolution_note_shape(self):
        note = _mod.render_resolution_comment(20, "2026-08-29T00:00Z")
        self.assertIn(_mod.COMMENT_MARKER_START, note)
        self.assertTrue(_mod.is_resolution_note(note))
        self.assertIn("2026-08-29T00:00Z", note)
        self.assertFalse(_mod.is_resolution_note(_mod.render_comment(20, "t", [])))
        self.assertFalse(_mod.is_resolution_note(None))

    def test_find_marker_entry_returns_id_and_body(self):
        body = "x <!-- PR-PATH-COLLISION:START --> y"
        self.assertEqual(_mod.find_marker_entry([{"id": 55, "body": body}]), ("55", body))
        self.assertIsNone(_mod.find_marker_entry([{"id": 1, "body": "plain"}]))


if __name__ == "__main__":
    unittest.main()
