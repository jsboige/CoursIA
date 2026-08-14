#!/usr/bin/env python3
"""Unit tests for the pure classification core of pr_gate_missing.py (#10928).

The ``classify`` and ``rollup_names`` functions are network-free; ``main`` (the
gh wiring) is exercised end-to-end in CI dry-runs, not here. These fixtures
encode the verdicts measured firsthand on the #10928 sample (2026-08-14):

  - #10902 : rollup = 5 CodeQL checks only, no ``PR gate`` -> missing
  - #10558 : same rollup, author app/github-actions -> bot_missing (structural)
  - #10898 : same shape before the re-push -> missing; after the re-push the
             rollup carries ``PR gate`` again -> has_gate
  - young PR : ``PR gate`` present but queued/in_progress (no conclusion) is
             NOT a defect -> has_gate (acceptance #1: presence, not conclusion)
  - draft PRs and PRs targeting a non-main base are excluded (never get the
    check by design, pr-gate.yml only fires on branches: [main])
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from pr_gate_missing import classify, rollup_names, GATE_NAME  # noqa: E402


def _codeql_only_rollup():
    """The exact rollup shape of #10902/#10558/#10898 pre-fix (5 CodeQL checks)."""
    return [
        {"name": "Analyze (actions)", "conclusion": "SUCCESS"},
        {"name": "Analyze (csharp)", "conclusion": "SUCCESS"},
        {"name": "Analyze (javascript-typescript)", "conclusion": "SUCCESS"},
        {"name": "Analyze (python)", "conclusion": "SUCCESS"},
        {"name": "CodeQL", "conclusion": "SUCCESS"},
    ]


def _pr(number, base="main", draft=False, author="jsboige", rollup=None):
    return {
        "number": number,
        "base_ref_name": base,
        "is_draft": draft,
        "author_login": author,
        "statusCheckRollup": rollup or [],
    }


def test_missing_when_gate_absent():
    # Mirrors #10902 measured 2026-08-14: 5 CodeQL checks, no PR gate.
    verdict, _ = classify(_pr(10902, rollup=_codeql_only_rollup()))
    assert verdict == "missing"


def test_has_gate_present_any_conclusion():
    # A young PR has the check-run with NO conclusion yet (queued/in_progress).
    # Presence is the signal; conclusion is not (acceptance #1).
    rollup = _codeql_only_rollup() + [{"name": GATE_NAME}]  # no conclusion
    verdict, _ = classify(_pr(10999, rollup=rollup))
    assert verdict == "has_gate"


def test_has_gate_success():
    rollup = _codeql_only_rollup() + [{"name": GATE_NAME, "conclusion": "SUCCESS"}]
    verdict, _ = classify(_pr(10914, rollup=rollup))
    assert verdict == "has_gate"


def test_has_gate_context_entry():
    # Status-context entries carry ``context``, not ``name`` -- rollup_names
    # must read both shapes. Mirrors #10898 after its re-push.
    rollup = [{"context": GATE_NAME, "status": "completed"}]
    verdict, _ = classify(_pr(10898, rollup=rollup))
    assert verdict == "has_gate"


def test_bot_missing_is_structural():
    # Mirrors #10558: bot PR, no PR gate -- labeled separately, not "missing".
    verdict, _ = classify(_pr(10558, author="app/github-actions", rollup=_codeql_only_rollup()))
    assert verdict == "bot_missing"


def test_bot_with_gate_is_not_flagged():
    rollup = _codeql_only_rollup() + [{"name": GATE_NAME, "conclusion": "SUCCESS"}]
    verdict, _ = classify(_pr(10484, author="app/github-actions", rollup=rollup))
    assert verdict == "has_gate"


def test_draft_pr_excluded():
    # A draft is not mergeable by design -- flagging it is noise.
    verdict, _ = classify(_pr(10999, draft=True, rollup=_codeql_only_rollup()))
    assert verdict == "draft"


def test_non_main_base_excluded():
    # pr-gate.yml only fires on `pull_request: branches: [main]` -- a PR
    # targeting a feature branch never gets the check, by design.
    verdict, _ = classify(_pr(10999, base="feature/foo", rollup=_codeql_only_rollup()))
    assert verdict == "excluded_base"


def test_empty_rollup_is_missing():
    # API edge: a PR with no rollup at all has no PR gate -- the defect.
    verdict, _ = classify(_pr(10999))
    assert verdict == "missing"


def test_rollup_names_reads_both_shapes():
    rollup = [{"name": "alpha"}, {"context": "beta"}, {"name": GATE_NAME}]
    names = rollup_names({"statusCheckRollup": rollup})
    assert GATE_NAME in names
    assert "alpha" in names
    assert "beta" in names
