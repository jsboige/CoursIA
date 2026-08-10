#!/usr/bin/env python3
r"""Unit tests for lane_claim_required.py -- the blocking CI gate of #10223.

Pins the 7-case acceptance grid from #10223 (a-g) plus the decisive criterion
6 (replay #10176 body vs #10169 comments -> block with blocking_lane =
myia-po-2025:CoursIA-2; pass after [OVERRIDE]) and the single-reader invariant
(no competing regex). The issue fetcher is injected -- these tests NEVER touch
the network.

Run: python -m pytest scripts/tests/test_lane_claim_required.py
"""
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

# scripts/ci/ must be importable (lane_claim_required lives there) AND scripts/
# (its deps grain_tag, check_lane_claim).
_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent))            # scripts/
sys.path.insert(0, str(_HERE.parent / "ci"))     # scripts/ci/

import lane_claim_required as lcr  # noqa: E402
import check_lane_claim as clc  # noqa: E402

# A fixed NOW so the staleness math is deterministic (criterion g: 49h claim).
NOW = datetime(2026, 8, 9, 22, 0, 0, tzinfo=timezone.utc)


# --- helpers ------------------------------------------------------------------

def comment(body, created_at, author="jsboige", url=None):
    return {
        "body": body,
        "createdAt": created_at,
        "author": {"login": author},
        "url": url,
    }


def issue_payload(*comments, number=10169, title="t"):
    return {"number": number, "title": title, "comments": list(comments)}


def fetcher_from(table):
    """Build an injectable issue fetcher from {issue_num: payload}."""
    return lambda n: table.get(n)


def pr_body(lane, ref_line):
    """Build a synthetic PR body with a Grain lane tag + a reference line."""
    return (
        f"Grain: DEEP/guard -- lane {lane} -- prev: MED/refactor #10151\n\n"
        f"## Summary\n\n{ref_line}\n"
    )


# --- 7-case acceptance grid (a-g) --------------------------------------------

def test_a_no_claim_on_closing_issue_is_pass():
    # (a) Issue carries no claim -> pass (the way is clear).
    body = pr_body("myia-po-2025:CoursIA", "Closes #10169")
    fetch = fetcher_from({10169: issue_payload(
        comment("just a discussion comment", "2026-08-09T11:00:00Z"),
        number=10169,
    )})
    v = lcr.check(body, fetch, now=NOW)
    assert v["guard_pass"] is True
    assert v["pr_lane"] == "myia-po-2025:CoursIA"
    assert v["closing_issues"] == [10169]


def test_b_my_own_claim_is_pass():
    # (b) I hold the active claim -> pass (resuming my own work).
    body = pr_body("myia-po-2025:CoursIA", "Closes #10169")
    fetch = fetcher_from({10169: issue_payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA -- working here",
                "2026-08-09T11:00:00Z"),
    )})
    v = lcr.check(body, fetch, now=NOW)
    assert v["guard_pass"] is True


def test_c_other_lane_claim_on_closing_ref_is_block():
    # (c) Another lane holds an active claim on a CLOSING reference -> BLOCK.
    # This is the #10169 incident shape.
    body = pr_body("myia-po-2026:CoursIA", "Closes #10169")
    fetch = fetcher_from({10169: issue_payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA-2 -- working here",
                "2026-08-09T11:41:43Z"),
    )})
    v = lcr.check(body, fetch, now=NOW)
    assert v["guard_pass"] is False
    assert v["blocking_lane"] == "myia-po-2025:CoursIA-2"
    assert v["blocking_issue"] == 10169
    assert v["pr_lane"] == "myia-po-2026:CoursIA"


def test_d_same_conflict_on_non_closing_ref_is_pass():
    # (d) Same conflict but on a NON-closing reference (See #N) -> pass.
    # find_close_keyword_pr_refs only matches closing keywords, so See/Part of
    # never reach the blocking path.
    body = pr_body("myia-po-2026:CoursIA", "See #10169 -- contributes to the epic")
    fetch = fetcher_from({10169: issue_payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA-2 -- working here",
                "2026-08-09T11:41:43Z"),
    )})
    v = lcr.check(body, fetch, now=NOW)
    assert v["guard_pass"] is True
    assert v["closing_issues"] == []  # See #N is not closing -> not scanned
    # Criterion (d): non-closing conflict -> pass + ADVISORY label (Task 4).
    assert "lane-claim-conflict" in v["advisory_labels"]


def test_e_released_claim_is_pass():
    # (e) The other lane RELEASED its claim -> pass.
    body = pr_body("myia-po-2026:CoursIA", "Closes #10169")
    fetch = fetcher_from({10169: issue_payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA-2 -- working here",
                "2026-08-09T11:41:43Z"),
        comment("[RELEASED] lane myia-po-2025:CoursIA-2 -- landed",
                "2026-08-09T15:00:00Z"),
    )})
    v = lcr.check(body, fetch, now=NOW)
    assert v["guard_pass"] is True


def test_f_override_naming_my_lane_is_pass():
    # (f) Coordinator [OVERRIDE] naming MY lane -> pass (adjudication grants it
    # to me). This is the #10169 resolution once the override is written.
    body = pr_body("myia-po-2026:CoursIA", "Closes #10169")
    fetch = fetcher_from({10169: issue_payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA-2 -- working here",
                "2026-08-09T11:41:43Z"),
        comment("[OVERRIDE] lane myia-po-2026:CoursIA -- substance favors",
                "2026-08-09T22:00:00Z"),
    )})
    v = lcr.check(body, fetch, now=NOW)
    assert v["guard_pass"] is True


def test_g_stale_claim_49h_is_pass_with_warning():
    # (g) Other lane's claim is 49h old (>= 48h threshold) -> pass + staleness
    # warning. NOW is 22:00 on 08-09; 49h earlier is 21:00 on 08-07.
    stale_at = "2026-08-07T21:00:00Z"  # exactly 49h before NOW
    body = pr_body("myia-po-2026:CoursIA", "Closes #10169")
    fetch = fetcher_from({10169: issue_payload(
        comment(f"[CLAIMED] lane myia-po-2025:CoursIA-2 -- working here",
                stale_at),
    )})
    v = lcr.check(body, fetch, stale_threshold=48.0, now=NOW)
    assert v["guard_pass"] is True
    assert any("stale" in w for w in v["warnings"])


# --- decisive criterion 6: replay #10176 body vs #10169 comments -------------

def test_criterion6_replay_10176_vs_10169_blocks_then_passes_after_override():
    # The motivating incident. PR #10176 (po-2026) body Closes #10169, which
    # carries po-2025:CoursIA-2's sole issue-level claim -> BLOCK with
    # blocking_lane = myia-po-2025:CoursIA-2. Then the coordinator's
    # adjudication as [OVERRIDE] lane myia-po-2026:CoursIA -> PASS.
    body_pre = pr_body("myia-po-2026:CoursIA", "Closes #10169")
    fetch_pre = fetcher_from({10169: issue_payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA-2 -- the guard organ",
                "2026-08-09T11:41:43Z"),
    )})
    v_pre = lcr.check(body_pre, fetch_pre, now=NOW)
    assert v_pre["guard_pass"] is False, "must block before the override"
    assert v_pre["blocking_lane"] == "myia-po-2025:CoursIA-2"

    # Same body, but the issue now carries the coordinator's [OVERRIDE].
    fetch_post = fetcher_from({10169: issue_payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA-2 -- the guard organ",
                "2026-08-09T11:41:43Z"),
        comment("[OVERRIDE] lane myia-po-2026:CoursIA -- substance favors #10176",
                "2026-08-09T22:00:00Z"),
    )})
    v_post = lcr.check(body_pre, fetch_post, now=NOW)
    assert v_post["guard_pass"] is True, "must pass after the override"


# --- lane-unreadable defers (does not duplicate the tag gate) ----------------

def test_lane_unreadable_is_pass_defers_to_tag_gate():
    # No Grain lane tag -> defer to check-variation-tag-required, never block.
    body = "## Summary\n\nCloses #10169 but no Grain lane tag.\n"
    fetch = fetcher_from({10169: issue_payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA-2 -- x",
                "2026-08-09T11:41:43Z"),
    )})
    v = lcr.check(body, fetch, now=NOW)
    assert v["guard_pass"] is True
    assert v["pr_lane"] is None


# --- fetch failure is fail-open ----------------------------------------------

def test_fetch_failure_is_fail_open_with_warning():
    body = pr_body("myia-po-2026:CoursIA", "Closes #999999")
    fetch = lambda n: None  # always fails (missing issue / network)
    v = lcr.check(body, fetch, now=NOW)
    assert v["guard_pass"] is True
    assert any("fail-open" in w for w in v["warnings"])


# --- multiple closing issues: one clean, one blocked ------------------------

def test_multiple_closing_issues_one_blocked():
    body = pr_body("myia-po-2026:CoursIA", "Closes #100, Fixes #200")
    fetch = fetcher_from({
        100: issue_payload(
            comment("[CLAIMED] lane myia-po-2025:CoursIA-2 -- x",
                    "2026-08-09T11:41:43Z"),
            number=100,
        ),
        200: issue_payload(number=200),  # no claim -> clean
    })
    v = lcr.check(body, fetch, now=NOW)
    assert v["guard_pass"] is False
    assert v["blocking_issue"] == 100


# --- advisory labels (#10223 Task 4) -- never block --------------------------

def test_advisory_lane_claim_absent_when_closing_issue_has_no_claim():
    # Closes an issue that carries NO claim at all -> advisory label (measure
    # adoption), never a block. The historical backlog was mostly taken without
    # a claim; reddening here would teach nothing.
    body = pr_body("myia-po-2026:CoursIA", "Closes #10169")
    fetch = fetcher_from({10169: issue_payload(number=10169)})  # no comments
    v = lcr.check(body, fetch, now=NOW)
    assert v["guard_pass"] is True
    assert "lane-claim-absent" in v["advisory_labels"]


def test_advisory_lane_claim_conflict_on_see_ref():
    # See #N (non-closing) where another lane claims #N -> advisory label; the
    # closing variant of the same conflict would block. A multi-lane EPIC is
    # advisory by construction.
    body = pr_body("myia-po-2026:CoursIA", "See #10169 -- part of the epic")
    fetch = fetcher_from({10169: issue_payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA-2 -- working here",
                "2026-08-09T11:41:43Z"),
    )})
    v = lcr.check(body, fetch, now=NOW)
    assert v["guard_pass"] is True
    assert v["closing_issues"] == []  # non-closing -> not scanned for blocking
    assert "lane-claim-conflict" in v["advisory_labels"]


def test_advisory_labels_empty_when_no_refs():
    # Lane readable but no issue reference at all -> no advisory labels.
    body = pr_body("myia-po-2026:CoursIA", "Just a refactoring, no issue ref.")
    fetch = fetcher_from({})
    v = lcr.check(body, fetch, now=NOW)
    assert v["guard_pass"] is True
    assert v["advisory_labels"] == []


def test_advisory_labels_carried_on_block_verdict():
    # A block verdict must still carry the advisory_labels field (well-typed)
    # so the advisory job can read it even when the blocking job is red.
    body = pr_body("myia-po-2026:CoursIA", "Closes #10169")
    fetch = fetcher_from({10169: issue_payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA-2 -- working here",
                "2026-08-09T11:41:43Z"),
    )})
    v = lcr.check(body, fetch, now=NOW)
    assert v["guard_pass"] is False
    # #10169 has a claim (not absent) and is closing (not a See) -> no advisory
    # label fires here, but the field is present and a list on the block path.
    assert isinstance(v["advisory_labels"], list)


# --- is_advisory: the job name must NOT be advisory --------------------------

def test_is_advisory_false_for_required_job_name():
    # The YAML job name carries `-required`; is_advisory must NOT classify it
    # as advisory (criterion: blocking job neutralized by name = complicity).
    sys.path.insert(0, str(_HERE.parent))
    import pr_gate  # noqa: E402
    assert pr_gate.is_advisory("check-lane-claim-required") is False
    # Sanity: a name with "advisory" IS advisory (the discriminator).
    assert pr_gate.is_advisory("some advisory label") is True


# --- CLI end-to-end (subprocess, no network) ---------------------------------

def test_cli_body_file_pass_exit_zero(tmp_path):
    body_file = tmp_path / "body_pass.md"
    body_file.write_text(
        pr_body("myia-po-2025:CoursIA", "See #10169 -- epic contribution"),
        encoding="utf-8",
    )
    proc = subprocess.run(
        [sys.executable, "scripts/ci/lane_claim_required.py",
         "--body-file", str(body_file)],
        capture_output=True, text=True, check=False,
    )
    assert proc.returncode == 0, f"expected 0, got {proc.returncode}: {proc.stderr!r}"
    v = json.loads(proc.stdout)
    assert v["guard_pass"] is True


def test_cli_lane_unreadable_exit_zero(tmp_path):
    body_file = tmp_path / "body_nolane.md"
    body_file.write_text("## Summary\n\nNo Grain tag.\n", encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "scripts/ci/lane_claim_required.py",
         "--body-file", str(body_file)],
        capture_output=True, text=True, check=False,
    )
    assert proc.returncode == 0
    v = json.loads(proc.stdout)
    assert v["pr_lane"] is None


def test_cli_missing_body_file_exit_two(tmp_path):
    proc = subprocess.run(
        [sys.executable, "scripts/ci/lane_claim_required.py",
         "--body-file", str(tmp_path / "nonexistent.md")],
        capture_output=True, text=True, check=False,
    )
    assert proc.returncode == 2


# --- #10323: closingIssuesReferences is authoritative for a PR body -----------
#
# The regex finder matches a closing keyword even inside a code span, a fenced
# block, or a negation ("NOT closing #N") -- contexts GitHub's parser ignores.
# closingIssuesReferences (passed as pr_closing_refs) is what GitHub will
# ACTUALLY close on merge. A regex hit absent from that set must NOT block.
# A real closing ref still does (the ratchet does not disarm).


def _body_with(line, lane="myia-po-2026:CoursIA"):
    return (
        f"Grain: DEEP/guard -- lane {lane} -- prev: MED/guard #10151\n\n"
        f"## Summary\n\n{line}\n"
    )


def _claimed_by_other_issue(num=6724):
    return fetcher_from({num: issue_payload(
        comment("[CLAIMED] lane myia-po-2025:CoursIA-2 -- working here",
                "2026-08-09T11:41:43Z"),
        number=num,
    )})


def test_10323_closing_keyword_in_negation_does_not_block():
    # The #10307 incident shape: the body carries a closing keyword in a context
    # GitHub's parser ignores (here a negated prose clause). The regex finder
    # matches `Closes #6724` regardless of the surrounding "NOT" -- but GitHub
    # resolves nothing (pr_closing_refs=set()), so the gate must NOT block even
    # though another lane claims #6724. The word "closing" itself is NOT a
    # GitHub keyword and does not match `close[ds]?`; the FP trigger is the
    # canonical `Closes`/`Fixes`/`Resolves` token in a GitHub-ignored context.
    body = _body_with("- OUT of scope: NOT actually Closes #6724 (epic sub-delivery).")
    fetch = _claimed_by_other_issue(6724)
    v = lcr.check(body, fetch, now=NOW, pr_closing_refs=set())
    assert v["guard_pass"] is True
    assert v["closing_issues"] == []
    assert any("IGNORED_BY_GITHUB" in w for w in v["warnings"])


def test_10323_closing_keyword_in_inline_code_span_does_not_block():
    # `` `Closes #6724` `` inside backticks -- GitHub ignores closing keywords
    # in inline code. Regex matches, GitHub doesn't -> no block.
    body = _body_with("Avoid the form `Closes #6724`; use `See #6724` instead.")
    fetch = _claimed_by_other_issue(6724)
    v = lcr.check(body, fetch, now=NOW, pr_closing_refs=set())
    assert v["guard_pass"] is True
    assert any("IGNORED_BY_GITHUB" in w for w in v["warnings"])


def test_10323_closing_keyword_in_fenced_block_does_not_block():
    # A closing keyword inside a ``` fenced code block is ignored by GitHub.
    body = _body_with("Example of what NOT to write:\n```\nCloses #6724\n```\n")
    fetch = _claimed_by_other_issue(6724)
    v = lcr.check(body, fetch, now=NOW, pr_closing_refs=set())
    assert v["guard_pass"] is True
    assert any("IGNORED_BY_GITHUB" in w for w in v["warnings"])


def test_10323_real_closing_ref_still_blocks_when_other_lane_claims():
    # Ratchet (acceptance #4): a REAL `Closes #N` that GitHub resolves (it is
    # in pr_closing_refs) still blocks when another lane holds a fresh claim.
    # The fix must make the gate MORE correct, not more permissive.
    body = _body_with("Closes #6724")
    fetch = _claimed_by_other_issue(6724)
    v = lcr.check(body, fetch, now=NOW, pr_closing_refs={6724})
    assert v["guard_pass"] is False
    assert v["blocking_issue"] == 6724
    assert v["blocking_lane"] == "myia-po-2025:CoursIA-2"
    assert v["closing_issues"] == [6724]


def test_10323_none_pr_closing_refs_falls_back_to_regex_with_warning():
    # Backward compat / fail-open: when closingIssuesReferences is unavailable
    # (older caller or fetch failure), pr_closing_refs=None -> the gate keeps
    # the regex-only behaviour (does not disarm) and warns about the gap.
    body = _body_with("Closes #6724")
    fetch = _claimed_by_other_issue(6724)
    v = lcr.check(body, fetch, now=NOW, pr_closing_refs=None)
    assert v["guard_pass"] is False  # regex still blocks the real ref
    assert any("unavailable" in w for w in v["warnings"])


def test_10323_advisory_absent_not_fired_on_ignored_closing_ref():
    # lane-claim-absent must not fire on a closing keyword GitHub ignores (code
    # span) -- consistent with the blocking path.
    body = _body_with("Avoid `Closes #6724`; use `See #6724`.")
    fetch = fetcher_from({6724: issue_payload(number=6724)})  # no claim
    v = lcr.check(body, fetch, now=NOW, pr_closing_refs=set())
    assert v["guard_pass"] is True
    assert "lane-claim-absent" not in v["advisory_labels"]


def test_10323_cli_pr_closing_refs_arg_parsed(tmp_path):
    # The CLI accepts --pr-closing-refs and the verdict reflects the cross-check.
    body_file = tmp_path / "body.md"
    body_file.write_text(_body_with("Closes #6724"), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "scripts/ci/lane_claim_required.py",
         "--body-file", str(body_file), "--pr-closing-refs", ""],
        capture_output=True, text=True, check=False,
    )
    v = json.loads(proc.stdout)
    assert v["guard_pass"] is True  # GitHub closes nothing -> no block
    assert v["closing_issues"] == []
    assert any("IGNORED_BY_GITHUB" in w for w in v["warnings"])
