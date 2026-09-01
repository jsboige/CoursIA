#!/usr/bin/env python3
"""Unit tests for the pure verdict logic of check_already_delivered.py (#13876).

The 4 sources (git_log, gh_search_prs, gh_issue_body, diff_filter_R) hit the
network via gh CLI, so they're exercised end-to-end in live runs, not here.
These fixtures encode the verdict logic against pre-canned source dicts,
mirroring the 5 firsthand-measured cases from cycle 24:

  - #13610 : commit + 3 PRs merged on subject -> LIVRÉ
  - #13760 : 1 PR merged on subject -> LIVRÉ (no commit needed)
  - #13850 : no commit, no PR on subject, but issue body cites a MERGED PR
            sharing a title keyword -> LIVRÉ via body ref
  - #13870 : 2 PRs OPEN, none merged -> AMBIGU
  - #13876 : 0 signals, but body cites old PRs whose titles share no keyword
            with the issue -> AMBIGU (the issue is in flight, not delivered)

The 5 verdicts are the lesson L1502 (cycle 24) — preflight must detect the
rider-delivery pattern (PR `Refs #N` from a parent issue → the issue stays
OPEN by administrative oversight).
"""

import sys
import os
import json

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from check_already_delivered import check  # noqa: E402


def _patched_check(issue, title, *, git_log=None, search_prs=None, body=None, indirect=None):
    """Bypass the gh-backed sources and feed canned data to the verdict core.

    We monkeypatch the 4 source_* functions on the module so the verdict sees
    our fixtures instead of calling gh. The verdict logic itself is the unit
    under test.
    """
    import check_already_delivered as mod

    orig_git = mod.source_git_log
    orig_search = mod.source_gh_search
    orig_body = mod.source_gh_issue_body
    orig_rename = mod.source_diff_filter_rename

    mod.source_git_log = lambda i: git_log or {"commits": [], "count": 0, "note": "subject-only"}
    mod.source_gh_search = lambda i: search_prs or {"prs": [], "count": 0, "errors": []}
    mod.source_gh_issue_body = lambda i: body or {"body_excerpt": "", "title": title or "", "state": "OPEN", "pr_refs": [], "commit_refs": [], "error": ""}
    mod.source_diff_filter_rename = lambda i, t=None: {"candidates": []}

    try:
        # Pre-populate the indirect lookup by patching _run via the gh pr view path
        # Simpler: stub _run so any `gh pr view` call returns our canned indirect PR
        canned_indirect = indirect or []
        orig_run = mod._run
        def fake_run(cmd, cwd=None):
            if cmd and cmd[0] == "gh" and cmd[1] == "pr" and cmd[2] == "view":
                # Find PR number
                for tok in cmd:
                    if isinstance(tok, str) and tok.isdigit():
                        n = int(tok)
                        for pr in canned_indirect:
                            if pr.get("number") == n:
                                import json as _json
                                return 0, _json.dumps({
                                    "number": pr["number"],
                                    "state": pr.get("state", "MERGED"),
                                    "mergedAt": pr.get("mergedAt", ""),
                                    "title": pr.get("title", ""),
                                    "url": pr.get("url", ""),
                                    "body": pr.get("body", ""),
                                }), ""
                        return 1, "", "not found"
            return orig_run(cmd, cwd=cwd)
        mod._run = fake_run
        try:
            return check(issue, title=title)
        finally:
            mod._run = orig_run
    finally:
        mod.source_git_log = orig_git
        mod.source_gh_search = orig_search
        mod.source_gh_issue_body = orig_body
        mod.source_diff_filter_rename = orig_rename


def test_livre_commit_et_pr_merged_sur_subject():
    """Mirrors #13610: commit referencing #N AND 3 PRs merged on the subject."""
    r = _patched_check(
        issue=13610,
        title="check_pr_perimeter article indefini edit-verb",
        git_log={"commits": ["e821d5290 fix(...) check_pr_perimeter (#13610)"], "count": 1, "note": "subject-only"},
        search_prs={"prs": [
            {"number": 13612, "state": "MERGED", "mergedAt": "2026-08-30T19:00:00Z", "title": "fix(...check_pr_perimeter...) (#13610)"},
            {"number": 13700, "state": "MERGED", "mergedAt": "2026-08-30T19:30:00Z", "title": "fix(...check_pr_perimeter...) (#13610)"},
        ], "count": 2, "errors": []},
        body={"body_excerpt": "PR #13612", "title": "check_pr_perimeter", "state": "OPEN", "pr_refs": [13612], "commit_refs": []},
    )
    assert r["verdict"] == "LIVRÉ", r
    assert r["exit_code"] == 1
    assert 13612 in r["merged_prs"]


def test_livre_pr_merged_seul_sans_commit():
    """Mirrors #13760: PR #13788 MERGED but commit subject uses a different number.

    This is the cycle-20 false-premise case: commit `0d3b026f9 chore(probas):
    zero-pad PyMC` doesn't mention #13760 in its subject, but PR #13788 (titled
    with #13760) MERGED on origin/main. The script must classify LIVRÉ based
    on the PR alone — the commit is a *weak* signal, not required.
    """
    r = _patched_check(
        issue=13760,
        title="zero-pad PyMC 1-9 en 01-09",
        git_log={"commits": [], "count": 0, "note": "subject-only"},
        search_prs={"prs": [
            {"number": 13788, "state": "MERGED", "mergedAt": "2026-08-31T08:56:00Z", "title": "chore(probas): zero-pad PyMC 1-9 -> 01-09, reference sweep + twin registry re-au (#13760)"},
        ], "count": 1, "errors": []},
        body={"body_excerpt": "PR #13788", "title": "zero-pad PyMC 1-9", "state": "OPEN", "pr_refs": [13788], "commit_refs": []},
    )
    assert r["verdict"] == "LIVRÉ", r
    assert 13788 in r["merged_prs"]


def test_livre_via_body_ref_pr_indirecte_mergee():
    """Mirrors #13850: PR #13824 MERGED with no commit/subject match, BUT the issue
    body cites PR #13824 AND its title shares the keyword 'Infer-2b-Debugging'
    with the issue title. This is the rider-delivery pattern L1502.
    """
    r = _patched_check(
        issue=13850,
        title="fix(generator,#13824 follow-up): Infer-2b-Debugging-Bonnes-Pratiques absent de docs/curriculum/{recherche,trading}.md (catalog-pr-hygiene HARD 1)",
        git_log={"commits": [], "count": 0, "note": "subject-only"},
        search_prs={"prs": [], "count": 0, "errors": []},
        body={"body_excerpt": "PR #13824 ...", "title": "fix(generator,#13824 follow-up): Infer-2b-Debugging-Bonnes-Pratiques", "state": "OPEN", "pr_refs": [13824], "commit_refs": []},
        indirect=[{
            "number": 13824,
            "state": "MERGED",
            "mergedAt": "2026-08-30T19:51:00Z",
            "title": "fix(reclass,#13824): Infer-6-Debugging -> Infer-2b-Debugging-Bonnes-Pratiques (accretion transversale)",
            "url": "https://github.com/jsboige/CoursIA/pull/13824",
            "body": "Refs #13850",  # Would normally be here; we don't check it
        }],
    )
    assert r["verdict"] == "LIVRÉ", r
    assert 13824 in r["indirect_merged_prs"]
    assert 13824 in r["indirect_credited_prs"]


def test_ambigu_prs_open_sans_merge():
    """Mirrors #13870: 2 PRs OPEN with subject match, no merge.

    For a worker lane, OPEN PR + commit on the branch = LIVRÉ, but the script
    is repo-wide so it can't see local branches. The verdict stays AMBIGU
    so the worker is warned but not blocked from claiming if they can show
    the branch.
    """
    r = _patched_check(
        issue=13870,
        title="L721 stale-tracker guard filter lane par tag body",
        git_log={"commits": [], "count": 0, "note": "subject-only"},
        search_prs={"prs": [
            {"number": 13872, "state": "OPEN", "mergedAt": "", "title": "fix(rules,#13870): L721 stale-tracker guard"},
        ], "count": 1, "errors": []},
        body={"body_excerpt": "PR #13872", "title": "L721 stale-tracker guard", "state": "OPEN", "pr_refs": [13872], "commit_refs": []},
    )
    assert r["verdict"] == "AMBIGU", r
    assert r["exit_code"] == 2
    assert 13872 in r["open_prs"]
    assert r["merged_prs"] == []


def test_ambigu_body_ref_sans_keyword_partage():
    """Mirrors #13876: issue body cites 8 historical PRs whose titles do NOT
    share a keyword with the issue title. Verdict must be AMBIGU (not LIVRÉ).

    Without the keyword filter, all 8 PRs would be credited and the script
    would falsely report LIVRÉ. This is the test that pins the filter.
    """
    r = _patched_check(
        issue=13876,
        title="scripts/check_already_delivered.py preflight cross-check",
        git_log={"commits": [], "count": 0, "note": "subject-only"},
        search_prs={"prs": [], "count": 0, "errors": []},
        body={"body_excerpt": "old refs: #9780, #10000, #10500", "title": "scripts/check_already_delivered.py preflight", "state": "OPEN", "pr_refs": [9780, 10000, 10500], "commit_refs": []},
        indirect=[
            {"number": 9780, "state": "MERGED", "mergedAt": "2024-01-01T00:00:00Z", "title": "fix(notebooks): add X11 binding", "url": "", "body": ""},
            {"number": 10000, "state": "MERGED", "mergedAt": "2024-06-01T00:00:00Z", "title": "chore(deps): bump Y", "url": "", "body": ""},
            {"number": 10500, "state": "MERGED", "mergedAt": "2025-01-01T00:00:00Z", "title": "feat(api): Z9 endpoint", "url": "", "body": ""},
        ],
    )
    assert r["verdict"] == "AMBIGU", r
    assert r["exit_code"] == 2
    # None of the 3 historical PRs share a keyword with the issue title
    # (issue title: "scripts/check_already_delivered.py preflight cross-check")
    assert r["indirect_merged_prs"] == [9780, 10000, 10500]
    assert r["indirect_credited_prs"] == [], "the keyword filter must reject these"


def test_word_boundary_prefix_collision_filtered():
    """Word-boundary filter : `#1` must NOT match `#10`, `#11`, `#13850` etc.

    The git log --grep="#1" call is SUBSTRING-based on this repo (every commit
    mentioning #10, #11, ..., #13850 starts with "#1"). Without a post-filter,
    the source returns thousands of false positives. The word-boundary filter
    ``(?<![0-9])#1\\b`` keeps only commits where ``#1`` appears as an isolated
    token — i.e. not as the prefix of ``#10``, ``#11411``, ``#13001``.

    This test drives the REAL ``source_git_log`` (no monkey-patch on it) and
    patches only ``_run`` to feed canned git output, so the filter logic runs.
    """
    import check_already_delivered as mod

    # All 4 commits have `#1` as a SUBSTRING of a longer number → ALL must be
    # dropped by the word-boundary filter. The commit with "reference #1" in
    # a textual position is NOT what the substring-based grep returns.
    canned_git_output = "\n".join([
        "abc1234 fix(ict,#10): ten",
        "def1234 fix(ict,#11): eleven",
        "ghi1234 fix(ict,#11411): eleven-thousand",
        "jkl1234 fix(ict,#13001): thirteen-thousand-one",
    ])
    orig_run = mod._run

    def fake_run(cmd, cwd=None):
        if cmd and cmd[0] == "git" and any(c.startswith("--grep") for c in cmd):
            return 0, canned_git_output, ""
        if cmd and cmd[0] == "gh" and "pr" in cmd and "list" in cmd:
            return 0, "[]", ""
        if cmd and cmd[0] == "gh" and "issue" in cmd and "view" in cmd:
            return 0, json.dumps({"number": 1, "title": "feat: add stiegler", "body": "", "state": "OPEN"}), ""
        return orig_run(cmd, cwd=cwd)

    mod._run = fake_run
    try:
        r = mod.check(1, title="feat: add stiegler or tools")
    finally:
        mod._run = orig_run
    gl = r["sources"]["git_log"]
    # Without a real `#1` token, the filter drops ALL 4 prefix-only commits.
    assert gl["count"] == 0, gl["commits"]
    # raw_count preserves the unfiltered count for forensics.
    assert gl["raw_count"] == 4, gl
    # Verdict must drop to NON LIVRÉ (no commit, no PR, no body ref).
    assert r["verdict"] == "NON LIVRÉ", r
    assert r["exit_code"] == 0
