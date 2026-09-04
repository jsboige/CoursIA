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

from pr_gate_missing import (  # noqa: E402
    classify,
    rollup_names,
    GATE_NAME,
    prescribe,
    remediation_for,
    REMEDIATION_CONFLICT,
    REMEDIATION_SKIP_CI,
)


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


# ---------------------------------------------------------------------------
# prescribe() -- remediation by CAUSE (#14477 design-gate)
# ---------------------------------------------------------------------------


def _candidate(number, mergeable_state="clean", base_changed_at=None,
               last_pr_run_at=None, subject="feat: x", author="jsboige"):
    return {
        "number": number,
        "mergeable_state": mergeable_state,
        "base_changed_at": base_changed_at,
        "last_pr_run_at": last_pr_run_at,
        "head_subject": subject,
        "author_login": author,
    }


def test_dirty_pr_remedy_is_conflict_never_repush():
    # Controle positif du faux positif (acceptance #14477) : une PR dirty
    # (no. #14220, mesuree 2026-09-03) DOIT produire le remede conflit, et le
    # remede re-poussee doit en etre ABSENT -- le test echoue si le remede
    # re-poussee ("un nouveau push", texte de REMEDIATION_SKIP_CI) est emis.
    pr = _candidate(14220, mergeable_state="dirty",
                    base_changed_at="2026-09-02T06:00:00Z")
    cause, _ = prescribe(pr)
    assert cause == "conflict"
    remedy = remediation_for(cause, "")
    assert remedy is REMEDIATION_CONFLICT
    assert "un nouveau push" not in remedy  # le remede re-poussee est interdit
    assert "resoudre le conflit" in remedy


def test_dirty_dominates_every_other_cause():
    # Le dirty prime (ordre impose par #14477) : meme avec un basculement de
    # base et un sujet [skip ci], la cause reste conflict.
    pr = _candidate(14441, mergeable_state="dirty",
                    base_changed_at="2026-09-03T11:55:48Z",
                    subject="chore: [skip ci] bump", author="app/github-actions")
    cause, _ = prescribe(pr)
    assert cause == "conflict"


def test_retarget_after_last_run_gets_wake_recipe():
    # Cause 4 mesuree sur #14441 : base_ref_changed posterieur au dernier run
    # du workflow PR gate -> remede commit vide a arbre identique (commit-tree).
    pr = _candidate(14441, base_changed_at="2026-09-03T11:55:48Z",
                    last_pr_run_at="2026-09-02T08:00:00Z")
    cause, detail = prescribe(pr)
    assert cause == "retarget"
    assert "2026-09-03T11:55:48Z" in detail  # la valeur lue est nommee
    remedy = remediation_for(cause, detail)
    assert "commit-tree" in remedy
    assert "7 runs -> 31" in remedy  # l'efficacite mesuree sur #14441 est citee


def test_retarget_not_claimed_when_more_recent_run_exists():
    # Si un run du workflow PR gate posterieur au basculement existe, le
    # retarget ne peut pas etre la cause : on retombe sur unknown.
    pr = _candidate(14441, base_changed_at="2026-09-03T11:55:48Z",
                    last_pr_run_at="2026-09-03T12:00:00Z")
    cause, _ = prescribe(pr)
    assert cause == "unknown"


def test_skip_ci_token_in_head_subject():
    # Cause 1 (#10898) : token dans le sujet de tete -> remede re-push nu.
    pr = _candidate(10898, subject="chore(nb): [skip ci] re-attestation")
    cause, detail = prescribe(pr)
    assert cause == "skip_ci"
    assert "[skip ci]" in detail
    assert "un nouveau push" in remediation_for(cause, detail)


def test_bot_pr_is_structural():
    pr = _candidate(10558, author="app/github-actions")
    cause, _ = prescribe(pr)
    assert cause == "bot"


def test_bot_dirty_is_conflict_first():
    # Le dirty prime meme sur la cause structurelle bot (#14477 : le conflit
    # bloque les runs de quiconque).
    pr = _candidate(10558, mergeable_state="dirty", author="app/github-actions")
    cause, _ = prescribe(pr)
    assert cause == "conflict"


def test_unknown_names_the_measurements():
    # Aucune des quatre causes -> « cause non determinee », les mesures faites
    # nommees, et le texte ne prescrit AUCUN remede git.
    pr = _candidate(10902, subject="feat: add monitoring")
    cause, detail = prescribe(pr)
    assert cause == "unknown"
    assert "mergeable_state=clean" in detail  # la valeur lue, pas une hypothese
    remedy = remediation_for(cause, detail)
    assert "pas determinee" in remedy
    assert "git merge" not in remedy
    assert "commit-tree" not in remedy
