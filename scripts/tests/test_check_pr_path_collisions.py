#!/usr/bin/env python3
"""Tests for `scripts.check_pr_path_collisions` (issues #13359, #13615).

The detector core is PURE (no network, no `gh`); idempotency and comment
rendering are also pure. Only the CLI driver (`list_open_prs`,
`find_marker`, `post_comment`) touches GitHub -- those are exercised by the
live `--dry-run`, not by these offline unit tests.

The positive controls are SYNTHETIC pairs seeded directly into the pure
detector, plus the two HISTORICAL pairs of #13615 replayed at their state of
then, so the suite is reproducible offline and fails loudly if the detector
breaks. The negative controls (stacked pair, artifact-only overlap) are as
load-bearing as the positives: a guard that reports everything reports
nothing (#13615).
"""
from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import subprocess as _subprocess
import sys
import unittest
from pathlib import Path
from unittest import mock

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
HISTORICAL_STRONG_PAIRS = _mod.HISTORICAL_STRONG_PAIRS


def _pr(number: int, paths: list[str], title: str = "", body: str = "",
        base_ref: str = "", head_ref: str = "") -> PrRow:
    return PrRow(number=number, title=title, paths=tuple(paths), body=body,
                 base_ref=base_ref, head_ref=head_ref)


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


class TestTiering(unittest.TestCase):
    """#13615: strong = shared file + common cited issue, weak otherwise."""

    def test_strong_when_common_issue_in_title(self):
        result = detect_path_collisions([
            _pr(1, ["x.ipynb"], title="fix(#11703): deliver X"),
            _pr(2, ["x.ipynb"], title="fix(#11703): deliver X (take 2)"),
        ])
        self.assertEqual(result.n_collisions, 1)
        c = result.collisions[0]
        self.assertEqual(c.tier, "strong")
        self.assertEqual(c.common_issues, (11703,))

    def test_weak_when_issues_disjoint(self):
        """Shared README, different issues -> weak, NOT dropped (#13615 posts it)."""
        result = detect_path_collisions([
            _pr(1, ["README.md"], title="docs: fix intro (#100)"),
            _pr(2, ["README.md"], title="docs: fix links (#200)"),
        ])
        self.assertEqual(result.n_collisions, 1)
        c = result.collisions[0]
        self.assertEqual(c.tier, "weak")
        self.assertEqual(c.common_issues, ())

    def test_strong_when_common_issue_only_in_body(self):
        """Body keywords (Closes/Fixes/See/refs/Part of) also cite issues.

        The pre-#13615 filter read titles only, so a pair whose common issue
        lived in both bodies was tiered weak. #13615 measures the emission
        channel by title AND body.
        """
        result = detect_path_collisions([
            _pr(1, ["n/x.ipynb"], title="feat: X", body="Closes #12373"),
            _pr(2, ["n/x.ipynb"], title="fix: Y", body="See #12373 for context."),
        ])
        self.assertEqual(result.n_collisions, 1)
        c = result.collisions[0]
        self.assertEqual(c.tier, "strong")
        self.assertIn(12373, c.common_issues)

    def test_body_keyword_scoped_not_incidental(self):
        """An incidental ``#N`` in the body (no cite keyword) does NOT count."""
        row = PrRow(number=1, title="", paths=(), body="discussed in #999 elsewhere")
        self.assertNotIn(999, row.cited_issues())
        row2 = PrRow(number=2, title="", paths=(), body="Refs #999")
        self.assertIn(999, row2.cited_issues())

    def test_cited_issues_merges_title_and_body(self):
        row = PrRow(number=1, title="fix(a,#12/#13): x", paths=(),
                    body="Closes #12. Part of #77.")
        self.assertEqual(row.cited_issues(), {12, 13, 77})

    def test_strong_collisions_selector(self):
        result = detect_path_collisions([
            _pr(1, ["x.ipynb"], title="fix(#10): a"),
            _pr(2, ["x.ipynb"], title="fix(#10): b"),
            _pr(3, ["y.ipynb"], title="docs(#20): c"),
            _pr(4, ["y.ipynb"], title="docs(#30): d"),
        ])
        strong = _mod.strong_collisions(result.collisions)
        self.assertEqual([(c.a_number, c.b_number) for c in strong], [(1, 2)])
        self.assertEqual(
            [(c.a_number, c.b_number) for c in result.collisions],
            [(1, 2), (3, 4)],
        )


class TestExclusions(unittest.TestCase):
    """#13615 negative controls: expected overlaps report NOTHING."""

    def test_stacked_pair_excluded(self):
        """Base of one = head of the other -> the overlap IS the stack."""
        result = detect_path_collisions([
            _pr(900010, ["stacked/x.md"], title="base tranche",
                base_ref="main", head_ref="feature/stack-1"),
            _pr(900011, ["stacked/x.md"], title="upper tranche",
                base_ref="feature/stack-1", head_ref="feature/stack-2"),
        ])
        self.assertEqual(result.n_collisions, 0)
        self.assertIn((900010, 900011), result.stacked_pairs_excluded)

    def test_same_base_different_heads_not_stacked(self):
        """Two tranches on a COMMON base are siblings, not a stack -> signal."""
        result = detect_path_collisions([
            _pr(10, ["x.md"], title="a", base_ref="main", head_ref="feature/one"),
            _pr(11, ["x.md"], title="b", base_ref="main", head_ref="feature/two"),
        ])
        self.assertEqual(result.n_collisions, 1)

    def test_stacked_needs_both_refs_known(self):
        """Missing base/head data never stacks anything (fail-open to signal)."""
        result = detect_path_collisions([
            _pr(10, ["x.md"], title="a", head_ref="feature/one"),
            _pr(11, ["x.md"], title="b", base_ref="feature/one"),
        ])
        self.assertEqual(result.n_collisions, 1)

    def test_catalog_artifacts_excluded(self):
        """COURSE_CATALOG.generated.* overlap carries no signal."""
        result = detect_path_collisions([
            _pr(1, ["COURSE_CATALOG.generated.json", "x/a.md"], title="a"),
            _pr(2, ["COURSE_CATALOG.generated.json", "COURSE_CATALOG.generated.md"],
                 title="b"),
        ])
        self.assertEqual(result.n_collisions, 0)

    def test_twin_registry_excluded(self):
        """twin_pairs.d/ rebaselines overlap structurally, permanently."""
        result = detect_path_collisions([
            _pr(1, ["scripts/notebook_tools/twin_pairs.d/app-1-nqueens.yaml"],
                title="a"),
            _pr(2, ["scripts/notebook_tools/twin_pairs.d/app-2-pct.yaml"],
                title="b"),
        ])
        self.assertEqual(result.n_collisions, 0)

    def test_mixed_pair_survives_on_signal_path(self):
        """Artifact overlap + one real shared path -> still reported."""
        result = detect_path_collisions([
            _pr(1, ["COURSE_CATALOG.generated.md", "real/n.ipynb"], title="a"),
            _pr(2, ["real/n.ipynb"], title="b"),
        ])
        self.assertEqual(result.n_collisions, 1)
        self.assertEqual(result.collisions[0].shared_paths, ("real/n.ipynb",))


class TestHistoricalPairs(unittest.TestCase):
    """#13615 acceptance: the two real pairs replayed at their state of then."""

    def test_both_historical_pairs_flagged_strong(self):
        for a, b, path, issue in HISTORICAL_STRONG_PAIRS:
            with self.subTest(pair=f"#{a}/#{b}"):
                result = detect_path_collisions([
                    _pr(a, [path, f"other/{a}.md"], title=f"feat(#{issue}): x",
                        body=f"Closes #{issue}"),
                    _pr(b, [path], title=f"fix(#{issue}): y",
                        body=f"See #{issue}"),
                ])
                self.assertEqual(result.n_collisions, 1)
                c = result.collisions[0]
                self.assertEqual(c.tier, "strong")
                self.assertIn(issue, c.common_issues)
                self.assertIn(path, c.shared_paths)

    def test_historical_paths_exist_in_repo(self):
        """The fixtures encode REAL repo paths (verified on main), not inventions."""
        import subprocess
        for _, _, path, _ in HISTORICAL_STRONG_PAIRS:
            with self.subTest(path=path):
                proc = subprocess.run(
                    ["git", "cat-file", "-e", f"HEAD:{path}"],
                    capture_output=True,
                )
                self.assertEqual(
                    proc.returncode, 0,
                    f"fixture path {path} does not exist in the checkout",
                )


class TestCommentProtocol(unittest.TestCase):
    def test_render_comment_is_marker_framed(self):
        result = detect_path_collisions(
            [_pr(1, ["x.ipynb"]), _pr(2, ["x.ipynb"])]
        )
        body = render_comment(1, "t", collisions_for_pr(1, result.collisions))
        self.assertIn(COMMENT_MARKER_START, body)
        self.assertIn(_mod.COMMENT_MARKER_END, body)
        self.assertIn("#2", body)

    def test_render_comment_names_tier_and_issues(self):
        """#13615: the comment names the tier, the paths AND the common issues."""
        result = detect_path_collisions([
            _pr(1, ["x.ipynb"], title="fix(#42): a"),
            _pr(2, ["x.ipynb"], title="fix(#42): b"),
        ])
        body = render_comment(1, "t", collisions_for_pr(1, result.collisions))
        self.assertIn("fort", body)
        self.assertIn("#42", body)
        self.assertIn("x.ipynb", body)

    def test_render_comment_weak_tier_no_issue_line(self):
        result = detect_path_collisions([
            _pr(1, ["README.md"], title="docs(#100): a"),
            _pr(2, ["README.md"], title="docs(#200): b"),
        ])
        body = render_comment(1, "t", collisions_for_pr(1, result.collisions))
        self.assertIn("faible", body)
        self.assertNotIn("issues communes", body)

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

    def test_find_marker_reads_the_rest_route_not_graphql(self):
        """The id must be spendable by the PATCH writer (#14421).

        ``find_marker_entry`` is pure and cannot tell a database id from a
        GraphQL node id -- both are truthy strings, so every unit test above
        passes under either source. The defect therefore lives entirely in
        the *fetch*, which is why this test asserts on the argv rather than
        on the returned tuple.

        Measured 2026-09-04 on #14495: ``gh pr view --json comments`` renders
        ``IC_kwDOH2Odns8AAAABSfMUxw`` where the REST collection renders
        ``5535634631``; ``GET /repos/.../issues/comments/IC_kwDO...`` answers
        ``404 Not Found``. ``edit_comment`` spends this id on that very route,
        so a GraphQL id makes every update and retract 404 while POST keeps
        working -- ``post=13 update=0 retract=0`` in run 364.
        """
        seen = {}

        def _capture(argv, **kwargs):
            argv = list(argv)
            seen["argv"] = argv
            page = [{"id": 5535634631,
                     "body": "x " + _mod.COMMENT_MARKER_START + " y"}]
            return _subprocess.CompletedProcess(
                argv, 0, stdout=json.dumps([page]), stderr="")

        with mock.patch.object(_mod.subprocess, "run", side_effect=_capture):
            entry = _mod.find_marker("owner/repo", 4242)

        self.assertIsNotNone(entry)
        self.assertEqual(entry[0], "5535634631")
        # The REST collection, addressable by the PATCH sibling ...
        self.assertIn("api", seen["argv"][:2])
        self.assertIn("repos/owner/repo/issues/4242/comments", seen["argv"])
        # ... paginated, so a marker past page 1 is not misread as absent ...
        self.assertIn("--paginate", seen["argv"])
        # ... and never the GraphQL projection, whose ids are not spendable.
        self.assertNotIn("view", seen["argv"])
        self.assertFalse(
            [a for a in seen["argv"] if a == "comments"],
            "'--json comments' returns GraphQL node ids the writer cannot use",
        )


class TestGhRowExtraction(unittest.TestCase):
    def test_from_gh_dict_reads_body_and_refs(self):
        row = PrRow.from_gh_dict({
            "number": 7,
            "title": "fix(#9): t",
            "body": "Closes #9",
            "baseRefName": "main",
            "headRefName": "feature/x",
            "files": [{"path": "a\\b.ipynb"}, {"path": ""}],
        })
        self.assertEqual(row.paths, ("a/b.ipynb",))
        self.assertEqual(row.body, "Closes #9")
        self.assertEqual(row.base_ref, "main")
        self.assertEqual(row.head_ref, "feature/x")
        self.assertEqual(row.cited_issues(), {9})


class TestWriteFailureReporting(unittest.TestCase):
    """#13623 acceptance 4: a forced write failure is WARNed and not confirmed.

    Positive control: the defect itself is that a non-zero rc is swallowed. A
    test must force a non-zero rc and prove BOTH that the WARN appears AND that
    the write reports failure (so the caller's ``confirmed`` count excludes it)
    -- otherwise "no write fails" is indistinguishable from "failures are not
    looked at".
    """

    @staticmethod
    def _proc(rc: int, stderr: str, stdout: str = "") -> _subprocess.CompletedProcess:
        return _subprocess.CompletedProcess(
            args=[], returncode=rc, stdout=stdout, stderr=stderr
        )

    def _run(self, fn, *args, rc: int, stderr: str) -> tuple[bool, str]:
        stderr_buf = io.StringIO()
        with mock.patch.object(
            _mod.subprocess, "run", return_value=self._proc(rc, stderr)
        ):
            with contextlib.redirect_stderr(stderr_buf):
                ok = fn(*args, dry_run=False)
        return ok, stderr_buf.getvalue()

    def test_post_comment_warns_and_reports_failure(self):
        ok, err = self._run(
            _mod.post_comment, "repo", 123, "body", rc=1, stderr="gh: permission denied"
        )
        self.assertFalse(ok)
        self.assertIn("WARN: write failed for #123", err)
        self.assertIn("permission denied", err)

    def test_edit_comment_warns_and_reports_failure(self):
        stderr_buf = io.StringIO()
        with mock.patch.object(
            _mod.subprocess, "run", return_value=self._proc(1, "gh: rate limit")
        ):
            with contextlib.redirect_stderr(stderr_buf):
                ok = _mod.edit_comment("repo", 123, "id456", "body", dry_run=False)
        self.assertFalse(ok)
        self.assertIn("WARN: write failed for #123", stderr_buf.getvalue())
        self.assertIn("rate limit", stderr_buf.getvalue())

    def test_post_comment_success_silent(self):
        ok, err = self._run(
            _mod.post_comment, "repo", 123, "body", rc=0, stderr=""
        )
        self.assertTrue(ok)
        self.assertNotIn("WARN", err)

    def test_edit_comment_success_silent(self):
        stderr_buf = io.StringIO()
        with mock.patch.object(
            _mod.subprocess, "run", return_value=self._proc(0, "")
        ):
            with contextlib.redirect_stderr(stderr_buf):
                ok = _mod.edit_comment("repo", 123, "id456", "body", dry_run=False)
        self.assertTrue(ok)
        self.assertNotIn("WARN", stderr_buf.getvalue())

    def test_dry_run_never_calls_gh(self):
        with mock.patch.object(
            _mod.subprocess, "run", side_effect=AssertionError("gh must not run in dry-run")
        ) as mocked:
            ok = _mod.post_comment("repo", 123, "body", dry_run=True)
            self.assertTrue(ok)
            mocked.assert_not_called()


class TestWriteChannelAndMuteVisibility(unittest.TestCase):
    """#14236. Two defects were measured on run 33597345910 (2026-09-02):
    30 of 33 planned writes returned ``Not Found (HTTP 404)``, and the run
    concluded ``success`` anyway. The first is addressed by changing channel,
    the second by making the loss able to turn a run red."""

    @staticmethod
    def _proc(rc: int, stderr: str = "", stdout: str = ""):
        return _subprocess.CompletedProcess(
            args=[], returncode=rc, stdout=stdout, stderr=stderr
        )

    def test_post_comment_uses_the_rest_endpoint_not_gh_pr_comment(self):
        """``gh pr comment`` reaches the comment through GraphQL, which
        reports a missing permission as NOT_FOUND -- indistinguishable from a
        PR that does not exist. REST answers with the real status code."""
        seen = {}

        def _capture(argv, **kwargs):
            seen["argv"] = list(argv)
            return self._proc(0)

        with mock.patch.object(_mod.subprocess, "run", side_effect=_capture):
            ok = _mod.post_comment("owner/repo", 4242, "hello", dry_run=False)

        self.assertTrue(ok)
        argv = seen["argv"]
        self.assertEqual(argv[:4], ["gh", "api", "--method", "POST"])
        self.assertIn("repos/owner/repo/issues/4242/comments", argv)
        # The channel that masked the failure must be gone, not merely
        # supplemented: a fallback would restore the masking on the retry.
        self.assertNotIn("comment", argv[:3])

    def test_post_comment_transmits_the_body_not_the_temp_path(self):
        """The endpoint assertion above is blind to what is actually SENT.

        ``gh api -f key=@path`` sends the literal string ``@path``; only
        ``-F`` dereferences it, and ``--input <json>`` -- what the PATCH
        sibling ``edit_comment`` already used -- sidesteps the ``@``
        semantics entirely. Under ``-f body=@<tmp>`` every marker posted the
        name of a temporary file instead of the report, and, since the marker
        string was then absent from the body, ``find_marker_entry`` could no
        longer find its own comment and posted a fresh one on each run.

        Measured on 2026-09-03: #14447 carried 4 such comments, and 7 of the
        40 most recent PRs were affected. The test therefore reads the
        payload back rather than trusting the argv shape."""
        seen = {}

        def _capture(argv, **kwargs):
            argv = list(argv)
            seen["argv"] = argv
            # The temp file still exists here: post_comment unlinks it in its
            # `finally`, after subprocess.run returns.
            idx = argv.index("--input")
            seen["payload"] = json.loads(
                Path(argv[idx + 1]).read_text(encoding="utf-8")
            )
            return self._proc(0)

        with mock.patch.object(_mod.subprocess, "run", side_effect=_capture):
            ok = _mod.post_comment("owner/repo", 4242, "hello #900", dry_run=False)

        self.assertTrue(ok)
        self.assertEqual(seen["payload"]["body"], "hello #900")
        # No argument may carry the "@<path>" form that caused the defect.
        self.assertFalse(
            [a for a in seen["argv"] if a.startswith("body=@")],
            "the body must not be passed as a literal @path",
        )

    def test_failed_write_is_warned_and_returns_false(self):
        buf = io.StringIO()
        with mock.patch.object(
            _mod.subprocess, "run",
            return_value=self._proc(1, "gh: Not Found (HTTP 404)"),
        ):
            with contextlib.redirect_stderr(buf):
                ok = _mod.post_comment("owner/repo", 13817, "body", dry_run=False)
        self.assertFalse(ok)
        self.assertIn("WARN", buf.getvalue())
        self.assertIn("13817", buf.getvalue())

    def _cli_with_one_planned_write(self, extra_argv, write_rc):
        """Drive _cli end-to-end over a synthetic two-PR collision.

        The pair is built so exactly one comment is planned; ``write_rc``
        decides whether that write is confirmed."""
        rows = [
            _pr(101, ["a/shared.py"], title="one", body="See #900"),
            _pr(102, ["a/shared.py"], title="two", body="See #900"),
        ]
        calls = {"n": 0}

        def _fake_run(argv, **kwargs):
            calls["n"] += 1
            if argv[:2] == ["gh", "api"]:
                return self._proc(write_rc, "gh: Not Found (HTTP 404)"
                                  if write_rc else "")
            return self._proc(0, stdout="[]")

        with mock.patch.object(_mod, "list_open_prs", return_value=rows),              mock.patch.object(_mod, "_repo_default", return_value="owner/repo"),              mock.patch.object(_mod, "scan_markers", return_value=({}, set())),              mock.patch.object(_mod, "label_strong_pairs", return_value=None),              mock.patch.object(_mod.subprocess, "run", side_effect=_fake_run):
            out, err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                rc = _mod._cli(extra_argv)
        return rc, out.getvalue(), err.getvalue()

    def test_write_loss_turns_the_run_red_when_asked(self):
        """Positive control: the flag must actually be able to fail."""
        rc, stdout, stderr = self._cli_with_one_planned_write(
            ["--fail-on-write-loss"], write_rc=1
        )
        self.assertEqual(rc, 1)
        self.assertIn("write(s) failed", stderr)
        self.assertIn("::error", stdout)

    def test_no_write_loss_stays_green_under_the_same_flag(self):
        """Negative control: the flag must not fail a healthy run -- without
        this, a check that always fails carries no information either."""
        rc, stdout, _ = self._cli_with_one_planned_write(
            ["--fail-on-write-loss"], write_rc=0
        )
        self.assertEqual(rc, 0)
        self.assertNotIn("::error", stdout)

    def test_write_loss_alone_does_not_fail_without_the_flag(self):
        """The organ stays advisory by default: callers that do not opt in
        keep the exit-0 contract the header promises."""
        rc, stdout, _ = self._cli_with_one_planned_write([], write_rc=1)
        self.assertEqual(rc, 0)
        self.assertIn("::error", stdout)



if __name__ == "__main__":
    unittest.main()
