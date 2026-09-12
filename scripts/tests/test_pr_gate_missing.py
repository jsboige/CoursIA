#!/usr/bin/env python3
"""Unit tests for the pure classification core of pr_gate_missing.py (#10928).

The ``classify`` and ``rollup_names`` functions are network-free. ``main``'s
gh wiring is exercised end-to-end in CI dry-runs -- but since #15621 the
PRODUCER's row shape is also pinned here (see the contract tests at the
bottom): the CI dry-run compares the organ's verdicts to no expectation, and
the fixtures below used to build the CONSUMER's shape by hand, which is
exactly how a producer/consumer re-map lived silently for days. These fixtures
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


# ---------------------------------------------------------------------------
# #15621 -- the producer's shape, pinned (not the consumer's)
# ---------------------------------------------------------------------------
#
# Every fixture above builds the row the CONSUMER wants (see `_pr`). That is
# the blind spot that let the collapse live: `list_open_prs()` was migrated to
# REST (flat `base_ref_name` / `is_draft` / `author_login`) while `main()` kept
# rebuilding each row with the GraphQL names (`baseRefName` / `isDraft` /
# `author`). A `.get()` on a missing key raises nothing -- it renders the
# default, and `classify()`'s truthy guards made `excluded_base`, `draft` and
# `bot_missing` structurally UNREACHABLE. Measured 2026-09-12: 7 healthy PRs
# (5 with a base != main, 2 drafts) published as defects, empty author field,
# a comment demanding a manual investigation of a by-design non-defect, and
# three labels that had never existed (description over GitHub's 100-char
# ceiling, creation failing silently). The tests below drive the PRODUCER.

import pr_gate_missing as pm  # noqa: E402  (post-fixtures: the module under test)


def _rest_rows():
    """Raw rows as the producer's jq projection emits them."""
    return [
        # #15620-shaped: base != main -- never sees pr-gate.yml by design.
        {"number": 15620, "draft": False,
         "base": "fix/15489-kernel-suffix-canon-guard",
         "author": "jsboige", "sha": "aa1", "labels": ["pr-gate-missing"]},
        # #15610-shaped: draft.
        {"number": 15610, "draft": True, "base": "main", "author": "jsboige",
         "sha": "bb2", "labels": []},
        # #10902-shaped: healthy base/main, no PR gate in the rollup.
        {"number": 10902, "draft": False, "base": "main", "author": "jsboige",
         "sha": "cc3", "labels": []},
        # #10558-shaped: bot author, GraphQL spelling.
        {"number": 10558, "draft": False, "base": "main",
         "author": "app/github-actions", "sha": "dd4", "labels": []},
        # #15678-shaped: the SAME app bot, REST spelling -- what /pulls
        # actually returns (`github-actions[bot]`, not `app/github-actions`).
        # Measured live 2026-09-12: this spelling classified `missing`.
        {"number": 15678, "draft": False, "base": "main",
         "author": "github-actions[bot]", "sha": "ee5", "labels": []},
    ]


def _patch_producer(monkeypatch):
    calls = {"check_runs": []}
    monkeypatch.setattr(pm, "_gh_rows", lambda _args: _rest_rows())

    def fake_check_runs(args):
        calls["check_runs"].append(args[1])
        return ["Analyze (python)", "CodeQL"]

    monkeypatch.setattr(pm, "_gh_json", fake_check_runs)
    return calls


def test_producer_rows_satisfy_the_declared_contract(monkeypatch):
    """Acceptance 1: one declared shape, pinned against the PRODUCER's real
    output. A future re-map that drops or renames a key fails HERE -- before
    any verdict silently becomes unreachable."""
    _patch_producer(monkeypatch)
    rows = pm.list_open_prs("o/r")
    assert rows, "le producteur doit emettre des lignes"
    for row in rows:
        missing = pm.PR_ROW_KEYS - set(row)
        assert not missing, f"cle(s) absente(s) de la ligne produite: {missing}"


def test_producer_does_not_pay_the_rollup_call_for_excluded_rows(monkeypatch):
    """The documented optimization stays true through the fix: excluded rows
    (base != main, draft) never trigger the per-PR check-runs call."""
    calls = _patch_producer(monkeypatch)
    pm.list_open_prs("o/r")
    fetched = [c for c in calls["check_runs"] if "/check-runs?" in c]
    assert len(fetched) == 3, "seules les PRs base=main non-draft sont sondees"


def test_the_three_unreachable_verdicts_are_reachable(monkeypatch):
    """The defect itself, end to end from the producer's rows: excluded_base,
    draft and bot_missing must all be returned. Before #15621 all four of
    these rows classified as `missing`."""
    _patch_producer(monkeypatch)
    verdicts = {
        row["number"]: pm.classify(pm.normalize_row(row))
        for row in pm.list_open_prs("o/r")
    }
    assert verdicts[15620][0] == "excluded_base"
    assert verdicts[15610][0] == "draft"
    assert verdicts[10558][0] == "bot_missing"
    assert verdicts[15678][0] == "bot_missing", (
        "l'orthographe REST du bot doit compter comme le bot"
    )
    assert verdicts[10902][0] == "missing"


def test_producer_emits_the_labels_the_migration_reads(monkeypatch):
    """`labels` was never emitted, so `has_label()` was always false and the
    generic -> conflict migration never fired. The producer now owes it."""
    _patch_producer(monkeypatch)
    rows = {row["number"]: row for row in pm.list_open_prs("o/r")}
    assert rows[15620]["labels"] == ["pr-gate-missing"]


def test_graphql_aliases_are_not_read():
    """The collapse in one assertion: a row carrying ONLY the GraphQL names
    normalizes to the falsy defaults that killed three verdicts. Pinned so a
    future re-map cannot quietly reintroduce the alias."""
    graphql_row = {
        "number": 1, "baseRefName": "feature/x", "isDraft": True,
        "author": {"login": "app/github-actions"},
        "labels": [{"name": "pr-gate-missing"}],
    }
    normalized = pm.normalize_row(graphql_row)
    assert normalized["base_ref_name"] is None
    assert normalized["is_draft"] is False
    assert normalized["author_login"] == ""
    # The false defect the collapse manufactured: a healthy feature-branch PR
    # published as `missing`.
    assert pm.classify(normalized)[0] == "missing"


def test_has_label_reads_the_producers_string_names():
    """#15621: the label list is a list of NAME STRINGS (the producer's jq
    `.labels[].name`), not the GraphQL list of objects. `has_label` must
    answer on that shape -- this is the generic -> conflict migration's
    `if`, and it was always false."""
    pr = {"labels": ["pr-gate-missing"]}
    assert pm.has_label(pr, "pr-gate-missing") is True
    assert pm.has_label(pr, "pr-gate-conflict") is False
    # An object-shaped entry (the old assumption) must not crash and must not
    # match: a mismatched shape reads as "label absent", never as an error.
    assert pm.has_label({"labels": [{"name": "x"}]}, "x") is False


def test_label_descriptions_fit_the_github_ceiling():
    """Acceptance 2: `gh label create` fails on a description over 100 chars
    (measured: 108/121/145 -> HTTP 404, labels never existed)."""
    for name in ("LABEL_DESC", "LABEL_BOT_DESC", "LABEL_CONFLICT_DESC"):
        desc = getattr(pm, name)
        assert len(desc) <= pm.MAX_LABEL_DESC, f"{name} = {len(desc)} chars"


def test_ensure_label_names_a_failed_creation(capsys, monkeypatch):
    """Acceptance 3: a failed creation is VISIBLE. Before #15621 the exit
    code was dropped (check=False, stderr captured but never read)."""
    class _Refused:
        returncode = 1
        stdout = ""
        stderr = "HTTP 404: Not Found"

    monkeypatch.setattr(pm.subprocess, "run", lambda *_a, **_k: _Refused())
    ok = pm.ensure_label("o/r", "pr-gate-missing", "b60205", pm.LABEL_DESC, False)
    assert ok is False
    out = capsys.readouterr().out
    assert "WARN -- label" in out
    assert "404" in out


def test_ensure_label_silent_when_the_write_succeeds(capsys, monkeypatch):
    """Positive control of the previous test: a green creation prints
    nothing -- the warning is diagnostic, not ambient noise."""
    class _Done:
        returncode = 0
        stdout = ""
        stderr = ""

    monkeypatch.setattr(pm.subprocess, "run", lambda *_a, **_k: _Done())
    assert pm.ensure_label("o/r", "pr-gate-missing", "b60205", pm.LABEL_DESC, False) is True
    assert capsys.readouterr().out == ""


def test_draft_and_excluded_base_retract_their_stale_label(monkeypatch, capsys):
    """3rd effet (#15621): the label fall-through existed only on `has_gate`.
    A PR misclassified by the shape collapse, then correctly reclassified,
    would keep its label AND its comment for life. The retraction is what
    makes the correction retroactive."""
    monkeypatch.setattr(pm, "ensure_label", lambda *_a, **_k: True)
    monkeypatch.setattr(pm, "list_open_prs", lambda _repo: [
        {"number": 15620, "base_ref_name": "fix/15489-kernel-suffix",
         "is_draft": False, "author_login": "jsboige",
         "statusCheckRollup": [], "labels": ["pr-gate-missing"]},
        {"number": 15610, "base_ref_name": "main", "is_draft": True,
         "author_login": "jsboige", "statusCheckRollup": [], "labels": []},
    ])
    monkeypatch.setattr(pm, "labeled_prs",
                        lambda _repo, _label: {15620: True, 15610: True})
    removed = []
    monkeypatch.setattr(pm, "remove_label",
                        lambda _repo, number, name, _dry: removed.append((number, name)))
    code = pm.main(["--repo", "o/r"])
    assert code == 0
    assert (15620, pm.LABEL_DEFAULT) in removed, "excluded_base doit retirer le label"
    assert (15610, pm.LABEL_DEFAULT) in removed, "draft doit retirer le label"
    out = capsys.readouterr().out
    assert "done: {'missing': 0" in out, "plus aucun faux defaut publie"
    assert "'excluded_base': 1" in out and "'draft': 1" in out
