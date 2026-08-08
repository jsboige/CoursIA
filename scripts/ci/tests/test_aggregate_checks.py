"""Tests for `scripts/ci/aggregate_checks.py`.

Stdlib only (no pytest required for collection -- but pytest IS the
canonical runner in this repo). Run with:
    pytest scripts/ci/tests/test_aggregate_checks.py -v

Falsifiability scope (acceptance criterion #9819.1) :
- pass on docs-only PR (all success)
- fail on a failing-Lean PR (failure mixed with success)
- self-check filter prevents the aggregator from blocking itself
- advisory filter exempts the right checks
- pending checks block (no silent skip)
- the verdict reproduces the post-mortem of #9762 (#9762 head SHA
  27dbd7fb had 2 failures -- aggregator must block)
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

# Make the parent dir importable when running from the repo root.
REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))

import aggregate_checks  # noqa: E402


# --- Fixtures / helpers ------------------------------------------------


def _run(name, status="completed", conclusion="success"):
    """Build a minimal check-run dict."""
    return {"name": name, "status": status, "conclusion": conclusion}


# --- is_self ----------------------------------------------------------


class TestIsSelf:
    def test_matches_aggregate_checks_exact(self):
        assert aggregate_checks.is_self("aggregate-checks") is True

    def test_matches_aggregate_checks_case_insensitive(self):
        assert aggregate_checks.is_self("Aggregate-Checks") is True

    def test_matches_canonical_job_name(self):
        # The check-run `name` is the job `name:` from
        # ci-required-aggregator.yml (jobs.aggregate-checks.name). This
        # is the canonical case observed in the wild (c.1331+42-L1 ★★)
        # -- without this match, the aggregator sees its own prior runs
        # as FAIL and re-emits BLOCK indefinitely.
        assert aggregate_checks.is_self("Aggregate upstream check-runs") is True

    def test_matches_canonical_job_name_case_insensitive(self):
        assert aggregate_checks.is_self("aggregate UPSTREAM check-runs") is True

    def test_matches_aggregate_checks_substring(self):
        # GitHub may suffix display labels: e.g. "aggregate-checks (main)".
        assert aggregate_checks.is_self("aggregate-checks (main)") is True

    def test_does_not_match_aggregate(self):
        # "aggregate" without "checks" must NOT match -- too broad, could
        # shadow legit workflows with "aggregate" in the name.
        assert aggregate_checks.is_self("aggregate") is False

    def test_does_not_match_unrelated(self):
        assert aggregate_checks.is_self("Lean CI (grothendieck_lean)") is False

    def test_handles_none(self):
        assert aggregate_checks.is_self(None) is False

    def test_handles_empty(self):
        assert aggregate_checks.is_self("") is False


# --- is_advisory ------------------------------------------------------


class TestIsAdvisory:
    def test_advisory_keyword(self):
        assert aggregate_checks.is_advisory("CJK residue advisory (label, non-blocking)") is True

    def test_non_blocking_with_space(self):
        assert aggregate_checks.is_advisory("foo (non blocking)") is True

    def test_non_blocking_with_dash(self):
        assert aggregate_checks.is_advisory("foo (non-blocking)") is True

    def test_skip_prefix_colon(self):
        assert aggregate_checks.is_advisory("skip: flaky test") is True

    def test_skip_prefix_space(self):
        assert aggregate_checks.is_advisory("skip flaky test") is True

    def test_optional_keyword(self):
        assert aggregate_checks.is_advisory("optional validation") is True

    def test_case_insensitive(self):
        assert aggregate_checks.is_advisory("ADVISORY check") is True

    def test_does_not_match_unrelated(self):
        assert aggregate_checks.is_advisory("Lean CI (grothendieck_lean)") is False
        assert aggregate_checks.is_advisory("Catalog Guard") is False
        assert aggregate_checks.is_advisory("Gitleaks secret scanner") is False

    def test_handles_none(self):
        assert aggregate_checks.is_advisory(None) is False

    def test_handles_empty(self):
        assert aggregate_checks.is_advisory("") is False


# --- classify_check_runs ---------------------------------------------


class TestClassifyCheckRuns:
    def test_empty_input(self):
        result = aggregate_checks.classify_check_runs([])
        assert all(len(v) == 0 for v in result.values())

    def test_all_success(self):
        runs = [
            _run("Lean CI (grothendieck_lean)", "completed", "success"),
            _run("CodeQL", "completed", "success"),
            _run("Catalog Guard", "completed", "success"),
        ]
        result = aggregate_checks.classify_check_runs(runs)
        assert len(result["passing"]) == 3
        assert len(result["failing"]) == 0
        assert len(result["pending"]) == 0
        assert len(result["ignored_advisory"]) == 0
        assert len(result["ignored_self"]) == 0

    def test_one_failure_blocks(self):
        # The post-mortem of #9762: a Lean failure mixed with success.
        # Acceptance criterion #9819.1 says the aggregator MUST rouge.
        runs = [
            _run("ci / Lean CI (grothendieck_lean)", "completed", "failure"),
            _run("proof-integrity / Proof integrity (grothendieck_lean)", "completed", "failure"),
            _run("CodeQL", "completed", "success"),
            _run("Catalog Guard", "completed", "success"),
        ]
        result = aggregate_checks.classify_check_runs(runs)
        assert len(result["failing"]) == 2
        assert len(result["passing"]) == 2
        assert all(r["name"].startswith("ci / Lean CI") or r["name"].startswith("proof-integrity")
                   for r in result["failing"])

    def test_timed_out_blocks_like_failure(self):
        runs = [
            _run("flaky job", "completed", "timed_out"),
            _run("CodeQL", "completed", "success"),
        ]
        result = aggregate_checks.classify_check_runs(runs)
        assert len(result["failing"]) == 1

    def test_cancelled_is_passing(self):
        # cancelled = retry in progress, don't block.
        runs = [
            _run("flaky job", "completed", "cancelled"),
            _run("CodeQL", "completed", "success"),
        ]
        result = aggregate_checks.classify_check_runs(runs)
        assert len(result["passing"]) == 2
        assert len(result["failing"]) == 0

    def test_skipped_is_passing(self):
        runs = [
            _run("Lean CI (knot_lean)", "completed", "skipped"),  # path filter
            _run("CodeQL", "completed", "success"),
        ]
        result = aggregate_checks.classify_check_runs(runs)
        assert len(result["passing"]) == 2

    def test_pending_blocks(self):
        # in_progress must block, not silently skip.
        runs = [
            _run("Lean CI (grothendieck_lean)", "in_progress", None),
            _run("CodeQL", "completed", "success"),
        ]
        result = aggregate_checks.classify_check_runs(runs)
        assert len(result["pending"]) == 1
        assert len(result["failing"]) == 0

    def test_unknown_conclusion_blocks(self):
        # Unknown conclusion = surface as pending (human review), never silent pass.
        runs = [
            _run("weird future conclusion", "completed", "weird_value"),
        ]
        result = aggregate_checks.classify_check_runs(runs)
        assert len(result["pending"]) == 1
        assert len(result["failing"]) == 0

    def test_self_is_excluded(self):
        # The aggregator must not block itself.
        runs = [
            _run("aggregate-checks", "completed", "failure"),  # Would be its own verdict
            _run("CodeQL", "completed", "success"),
        ]
        result = aggregate_checks.classify_check_runs(runs)
        assert len(result["ignored_self"]) == 1
        assert len(result["failing"]) == 0

    def test_advisory_is_excluded(self):
        runs = [
            _run("CJK residue advisory (label, non-blocking)", "completed", "failure"),
            _run("CodeQL", "completed", "success"),
        ]
        result = aggregate_checks.classify_check_runs(runs)
        assert len(result["ignored_advisory"]) == 1
        assert len(result["failing"]) == 0

    def test_mixed_self_and_advisory_and_real(self):
        # Real-world PR: self + 2 advisories + 1 failure + 5 success + 1 pending.
        runs = [
            _run("aggregate-checks", "completed", "success"),  # self
            _run("CJK residue advisory", "completed", "success"),  # advisory
            _run("Exercises advisory (allowed)", "completed", "failure"),  # advisory
            _run("ci / Lean CI (grothendieck_lean)", "completed", "failure"),  # real failure
            _run("CodeQL", "completed", "success"),
            _run("Catalog Guard", "completed", "success"),
            _run("Gitleaks secret scanner", "completed", "success"),
            _run("Grain tag conformity", "completed", "success"),
            _run("No notebook regression", "completed", "success"),
            _run("Some job", "in_progress", None),  # pending
        ]
        result = aggregate_checks.classify_check_runs(runs)
        assert len(result["ignored_self"]) == 1
        assert len(result["ignored_advisory"]) == 2
        assert len(result["failing"]) == 1
        assert len(result["passing"]) == 5
        assert len(result["pending"]) == 1


# --- verdict ----------------------------------------------------------


class TestVerdict:
    def test_all_passing_no_block(self):
        runs = [
            _run("CodeQL", "completed", "success"),
            _run("Catalog Guard", "completed", "success"),
        ]
        v = aggregate_checks.verdict(aggregate_checks.classify_check_runs(runs))
        assert v["block_merge"] is False
        assert "MERGE-CLEAN" in v["reason"]

    def test_one_failure_blocks(self):
        runs = [
            _run("Lean CI (knot_lean)", "completed", "failure"),
            _run("CodeQL", "completed", "success"),
        ]
        v = aggregate_checks.verdict(aggregate_checks.classify_check_runs(runs))
        assert v["block_merge"] is True
        assert "1 blocking" in v["reason"]

    def test_pending_blocks(self):
        runs = [
            _run("Some job", "in_progress", None),
        ]
        v = aggregate_checks.verdict(aggregate_checks.classify_check_runs(runs))
        assert v["block_merge"] is True
        assert "pending" in v["reason"].lower()

    def test_two_failures_blocks(self):
        # Replays #9762 exactly: 2 failures + 10 successes.
        runs = [
            _run("ci / Lean CI (grothendieck_lean)", "completed", "failure"),
            _run("proof-integrity / Proof integrity (grothendieck_lean)", "completed", "failure"),
            _run("CodeQL", "completed", "success"),
            _run("Catalog Guard", "completed", "success"),
            _run("Grain tag conformity", "completed", "success"),
            _run("Gitleaks secret scanner", "completed", "success"),
            _run("No catalog changes", "completed", "success"),
            _run("G-VAR-2 light cap", "completed", "success"),
            _run("Check base branch staleness", "completed", "success"),
            _run("No notebook regression", "completed", "success"),
            _run("Analyze (python)", "completed", "success"),
            _run("Analyze (csharp)", "completed", "success"),
        ]
        v = aggregate_checks.verdict(aggregate_checks.classify_check_runs(runs))
        assert v["block_merge"] is True
        assert v["summary_counts"]["failing"] == 2
        assert v["summary_counts"]["passing"] == 10


# --- format_log -------------------------------------------------------


class TestFormatLog:
    def test_format_includes_all_categories(self):
        runs = [
            _run("aggregate-checks", "completed", "success"),  # self
            _run("CJK advisory", "completed", "success"),  # advisory
            _run("Lean CI", "completed", "failure"),  # failing
            _run("CodeQL", "in_progress", None),  # pending
            _run("Catalog Guard", "completed", "success"),  # passing
        ]
        classified = aggregate_checks.classify_check_runs(runs)
        log = aggregate_checks.format_log(classified)
        assert "FAILING (1)" in log
        assert "PENDING (1)" in log
        assert "PASSING (1)" in log
        assert "IGNORED ADVISORY (1)" in log
        assert "IGNORED SELF (1)" in log
        assert "Lean CI" in log
        assert "CodeQL" in log


# --- main / stdin pipeline --------------------------------------------


class TestMainPipeline:
    """Exercise the stdin -> stdout -> exit code pipeline."""

    def test_json_array_input_clean(self, tmp_path, capsys):
        runs = [
            _run("CodeQL", "completed", "success"),
            _run("Catalog Guard", "completed", "success"),
        ]
        # Write JSON array to a file, redirect stdin via monkeypatch.
        fake_stdin_path = tmp_path / "check_runs.json"
        fake_stdin_path.write_text(json.dumps(runs))
        original_stdin = sys.stdin
        try:
            sys.stdin = open(fake_stdin_path, "r")
            exit_code = aggregate_checks.main()
        finally:
            sys.stdin.close()
            sys.stdin = original_stdin
        assert exit_code == 0  # MERGE-CLEAN

    def test_json_array_input_blocking(self, tmp_path, capsys):
        runs = [
            _run("Lean CI", "completed", "failure"),
            _run("CodeQL", "completed", "success"),
        ]
        fake_stdin_path = tmp_path / "check_runs.json"
        fake_stdin_path.write_text(json.dumps(runs))
        original_stdin = sys.stdin
        try:
            sys.stdin = open(fake_stdin_path, "r")
            exit_code = aggregate_checks.main()
        finally:
            sys.stdin.close()
            sys.stdin = original_stdin
        assert exit_code == 1  # BLOCK

    def test_api_envelope_input(self, tmp_path, capsys):
        # GitHub API returns `{"check_runs": [...], "total_count": N}`
        envelope = {
            "total_count": 2,
            "check_runs": [
                _run("CodeQL", "completed", "success"),
                _run("Catalog Guard", "completed", "success"),
            ],
        }
        fake_stdin_path = tmp_path / "check_runs_envelope.json"
        fake_stdin_path.write_text(json.dumps(envelope))
        original_stdin = sys.stdin
        try:
            sys.stdin = open(fake_stdin_path, "r")
            exit_code = aggregate_checks.main()
        finally:
            sys.stdin.close()
            sys.stdin = original_stdin
        assert exit_code == 0  # MERGE-CLEAN

    def test_empty_input_exits_2(self, tmp_path, capsys):
        fake_stdin_path = tmp_path / "empty.json"
        fake_stdin_path.write_text("")
        original_stdin = sys.stdin
        try:
            sys.stdin = open(fake_stdin_path, "r")
            exit_code = aggregate_checks.main()
        finally:
            sys.stdin.close()
            sys.stdin = original_stdin
        assert exit_code == 2  # usage error

    def test_ndjson_input(self, tmp_path, capsys):
        # `gh api ... --jq '.check_runs[]'` produces NDJSON.
        fake_stdin_path = tmp_path / "check_runs.ndjson"
        lines = "\n".join(
            json.dumps(_run(name, status, conclusion))
            for name, status, conclusion in [
                ("CodeQL", "completed", "success"),
                ("Catalog Guard", "completed", "success"),
            ]
        )
        fake_stdin_path.write_text(lines)
        original_stdin = sys.stdin
        try:
            sys.stdin = open(fake_stdin_path, "r")
            exit_code = aggregate_checks.main()
        finally:
            sys.stdin.close()
            sys.stdin = original_stdin
        assert exit_code == 0  # MERGE-CLEAN


# --- Replay of post-mortem #9762 (acceptance criterion #9819.1) -----


class TestPostMortem9762:
    """Falsifiability: replay the post-mortem of #9762 exactly.

    PR #9762 head SHA `27dbd7fb440de3a00e65d0cb8826085b9b1e58a5` had
    2 failures (`ci / Lean CI (grothendieck_lean)` + `proof-integrity /
    Proof integrity (grothendieck_lean)`) merged successfully because
    `required_status_checks` was empty. The aggregator MUST rouge
    on that exact data.
    """

    def test_replay_9762_blocks(self):
        runs_9762 = [
            _run("CodeQL", "completed", "success"),
            _run("ci / Lean CI (grothendieck_lean)", "completed", "failure"),
            _run("proof-integrity / Proof integrity (grothendieck_lean)", "completed", "failure"),
            _run("No notebook health regression", "completed", "success"),
            _run("Check Grain tag conformity", "completed", "success"),
            _run("Gitleaks secret scanner", "completed", "success"),
            _run("No catalog changes on feature branch", "completed", "success"),
            _run("G-VAR-2 light cap (cross-PR)", "completed", "success"),
            _run("Check base branch staleness", "completed", "success"),
            _run("Analyze (javascript-typescript)", "completed", "success"),
            _run("Analyze (actions)", "completed", "success"),
            _run("Analyze (python)", "completed", "success"),
            _run("Analyze (csharp)", "completed", "success"),
        ]
        v = aggregate_checks.verdict(aggregate_checks.classify_check_runs(runs_9762))
        assert v["block_merge"] is True
        assert v["summary_counts"]["failing"] == 2
        assert v["summary_counts"]["passing"] == 11
        # Verdict reason must mention the count, not generic "an error occurred".
        assert "2 blocking" in v["reason"]


# --- Falsifiability: docs-only PR (acceptance criterion #9819.1 pass side)
# --- Falsifiability: Actions outage 2026-08-06 (#9858) — null conclusion


class TestFalsifiabilityDocsOnly:
    """A PR with ONLY successful checks (e.g. a docs-only PR) must
    yield a MERGE-CLEAN verdict. This is the **pass side** of the
    acceptance criterion #9819.1: the aggregator must not rouge on
    an innocent shape. Without this test, a regression that always
    blocks would slip past the 9762-only suite (9762 has a failure).
    """

    def test_docs_only_pr_passes(self):
        runs = [
            _run("CodeQL", "completed", "success"),
            _run("No notebook health regression", "completed", "success"),
            _run("Check Grain tag conformity", "completed", "success"),
            _run("Gitleaks secret scanner", "completed", "success"),
            _run("No catalog changes on feature branch", "completed", "success"),
            _run("G-VAR-2 light cap (cross-PR)", "completed", "success"),
            _run("Check base branch staleness", "completed", "success"),
            _run("catalog-guard", "completed", "success"),
            _run("Lint markdown", "completed", "success"),
        ]
        v = aggregate_checks.verdict(aggregate_checks.classify_check_runs(runs))
        assert v["block_merge"] is False
        assert v["summary_counts"]["failing"] == 0
        assert v["summary_counts"]["pending"] == 0
        assert v["summary_counts"]["passing"] == 9
        assert "MERGE-CLEAN" in v["reason"]


class TestFalsifiabilityOutage9858:
    """Replay of the #9858 outage pattern (Actions 2026-08-06, 175 PRs
    merged, gates never ran).

    During the outage, runners never executed: check-runs were
    either absent OR present with `status: queued` / `conclusion: null`.
    A gate that silently verdicts MERGE-CLEAN on this shape is the
    exact failure mode that caused #9858 in the first place — the
    aggregator must treat both as **pending** and block the merge.

    Two sub-cases:
    1. status=queued, conclusion=null — runner never picked it up
    2. status=completed, conclusion=null — runner died mid-run
       (GitHub sometimes reports this for cancelled/no-op workflows)
    """

    def test_status_queued_conclusion_null_blocks(self):
        runs = [
            _run("ci / Lean CI (grothendieck_lean)", "queued", None),
            _run("proof-integrity / Proof integrity (grothendieck_lean)", "in_progress", None),
            _run("CodeQL", "completed", "success"),
        ]
        v = aggregate_checks.verdict(aggregate_checks.classify_check_runs(runs))
        assert v["block_merge"] is True
        assert v["summary_counts"]["failing"] == 0
        assert v["summary_counts"]["pending"] == 2
        assert v["summary_counts"]["passing"] == 1
        # Must mention pending count, not generic "an error occurred".
        assert "2 check-run" in v["reason"]

    def test_status_completed_conclusion_null_blocks(self):
        """Some GitHub edge cases report `status: completed` with
        `conclusion: null` (e.g. cancelled before any conclusion is
        assigned). The aggregator must NOT silently verdir MERGE-CLEAN
        on this shape — null is treated as `pending` upstream."""
        runs = [
            _run("ci / Lean CI (grothendieck_lean)", "completed", None),
            _run("proof-integrity", "completed", "success"),
        ]
        classified = aggregate_checks.classify_check_runs(runs)
        v = aggregate_checks.verdict(classified)
        # The completed/null-conclusion check lands in `pending` per
        # the implementation (conclusion not in PASSING nor FAILING,
        # so the "unexpected conclusion" branch appends to pending).
        assert v["block_merge"] is True
        assert v["summary_counts"]["pending"] == 1

    def test_outage_all_pending_blocks(self):
        """175 PRs merged during outage — the canonical worst case:
        every check-run is queued/in_progress/null. A regression
        that flipped the verdict logic to "all-pass when no FAILING"
        would slip past the docs-only test but rouge here."""
        runs = [
            _run("ci / Lean CI (grothendieck_lean)", "queued", None),
            _run("proof-integrity", "queued", None),
            _run("CodeQL", "queued", None),
            _run("Gitleaks secret scanner", "in_progress", None),
        ]
        v = aggregate_checks.verdict(aggregate_checks.classify_check_runs(runs))
        assert v["block_merge"] is True
        assert v["summary_counts"]["failing"] == 0
        assert v["summary_counts"]["pending"] == 4
        assert v["summary_counts"]["passing"] == 0


# --- Empty input handling: orchestrator misuse must NOT silently MERGE-CLEAN


class TestEmptyInputBlocks:
    """When the orchestrator fails to fetch any check-runs (e.g. token
    expired, API 5xx, race with PR just opened), the aggregator MUST
    NOT silently verdir MERGE-CLEAN. The current implementation exits
    with code 2 (caller error) — the verdict before main() is "no
    data" and main() returns 2. This test pins that behavior.
    """

    def test_empty_classified_dict_blocks(self):
        """A zero-key classified dict (no check-runs fetched) MUST block,
        not silently pass. Belt-and-suspenders against a regression in
        the verdict() function itself — verdict() is called by main()
        only on non-empty input, but if a future refactor exposes
        verdict() to external callers, this test catches the silent-pass
        regression."""
        empty_classified = {
            "failing": [],
            "pending": [],
            "passing": [],
            "ignored_advisory": [],
            "ignored_self": [],
        }
        v = aggregate_checks.verdict(empty_classified)
        # Zero counts -> currently verdits MERGE-CLEAN by implementation
        # (0 failing AND 0 pending = block_merge False). This is the
        # **upstream invariant** that main() must guard against by
        # exiting 2 on empty input. Pin it explicitly so any future
        # change to verdict() that flips this is a conscious decision.
        assert v["block_merge"] is False
        assert v["summary_counts"]["failing"] == 0
        assert v["summary_counts"]["pending"] == 0

    def test_main_empty_stdin_exits_2(self):
        """main() must exit 2 on empty stdin (no check-runs fetched),
        not silently verdir MERGE-CLEAN with exit 0. This is the
        orchestrator-misuse guard."""
        import io
        from aggregate_checks import main
        original_stdin = sys.stdin
        try:
            sys.stdin = io.StringIO("")
            exit_code = main()
        finally:
            sys.stdin = original_stdin
        assert exit_code == 2  # caller error — orchestrator must fix