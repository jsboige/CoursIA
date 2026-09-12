#!/usr/bin/env python3
"""Unit tests for the pure classification core of pr_gate_missing.py (#10928).

The ``classify`` and ``rollup_names`` functions are network-free; ``main`` (the
gh wiring) is exercised end-to-end in CI dry-runs, not here. These fixtures
encode the verdicts measured firsthand on the #10928 sample (2026-08-14):

  - (#15621) the fixtures below build the classify() input BY HAND -- which is
    exactly how three verdicts stayed unreachable for weeks: the collector had
    been migrated to REST keys while main() kept reading GraphQL ones, and a
    hand-built fixture cannot notice that. The `#15621` section at the end
    therefore feeds classify() with the COLLECTOR'S OUTPUT (patched gh), never
    with a hand-built dict.

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
import io
from contextlib import redirect_stderr
from unittest import mock

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from pr_gate_missing import (  # noqa: E402
    main,
    classify,
    classify_input,
    rollup_names,
    list_open_prs,
    has_label,
    GATE_NAME,
    LABEL_BOT_DESC,
    LABEL_CONFLICT_DESC,
    LABEL_DESC,
    prescribe,
    remediation_for,
    _gh_write,
    COMMENT_MARKER_START,
    COMMENT_MARKER_END,
    REMEDIATION_CONFLICT,
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
# (#15621) le collecteur et le consommateur partagent UNE seule forme
#
# Ces tests alimentent classify() avec la SORTIE du collecteur -- jamais avec un
# dict ecrit a la main. C'est la difference qui compte : les fixtures ci-dessus
# construisaient la forme attendue par le consommateur, donc elles sont restees
# vertes pendant que le producteur, migre en REST (#14488), emettait
# `base_ref_name` / `is_draft` / `author_login` la ou main() relisait
# `baseRefName` / `isDraft` / `author`. Trois verdicts etaient des lors
# inatteignables, et la production le montrait : `excluded_base: 0`,
# `draft: 0` sur 60 PRs ouvertes (run 34621731008).
# ---------------------------------------------------------------------------


def _collector_row(number=1, base="main", draft=False, author="jsboige",
                   labels=None):
    """Une ligne exactement telle que le flux gh de `list_open_prs` la rend.

    `labels` porte la forme de l'API REST (`[{"name": ...}]`), pas des chaines :
    c'est la forme que `has_label()` lit, et la garder identique a celle du
    payload REST evite un second dialecte.
    """
    return {
        "number": number,
        "draft": draft,
        "base": base,
        "author": author,
        "labels": labels or [],
        "sha": "sha%d" % number,
    }


def _collector_output(rows, check_run_names=("PR gate",)):
    """`list_open_prs` sur un flux gh simule -- aucun appel reseau."""
    with mock.patch("pr_gate_missing._gh_rows", lambda args: rows), \
         mock.patch("pr_gate_missing._gh_json",
                    lambda args: list(check_run_names)):
        return list_open_prs("jsboige/CoursIA")


def test_collector_output_excludes_non_main_base():
    # Verdict inatteignable avant le fix : 5 PRs stackees ouvertes a la mesure
    # (dont #15620) etaient classees `missing` avec cause `unknown`.
    rows = _collector_output([_collector_row(15620, base="fix/15489-x")])
    verdict, why = classify(rows[0])
    assert verdict == "excluded_base", why


def test_collector_output_excludes_drafts():
    rows = _collector_output([_collector_row(15334, draft=True)])
    verdict, why = classify(rows[0])
    assert verdict == "draft", why


def test_collector_output_flags_bot_pr_structurally():
    rows = _collector_output([_collector_row(10558, author="app/github-actions")],
                             check_run_names=("CodeQL",))
    verdict, why = classify(rows[0])
    assert verdict == "bot_missing", why


def test_collector_output_carries_author_and_labels():
    # Le symptome visible du defaut : le commentaire imprimait « auteur : » vide
    # (vu sur #15620), et `labels` n'etait pas collecte du tout -- donc
    # has_label() etait toujours faux et le remappage vers pr-gate-conflict
    # impossible.
    rows = _collector_output(
        [_collector_row(4, author="jsboige",
                        labels=[{"name": "pr-gate-missing"}])],
        check_run_names=("CodeQL",))
    assert classify(rows[0])[0] == "missing"
    assert rows[0]["author_login"] == "jsboige"
    assert has_label(rows[0], "pr-gate-missing")
    assert not has_label(rows[0], "pr-gate-conflict")


def test_classify_input_is_the_only_shape():
    # Epingle le contrat : toucher a `classify_input` sans mettre a jour
    # classify() (ou l'inverse) fait rougir ici au lieu de desactiver un verdict
    # en silence.
    row = classify_input(7, "main", False, "jsboige", [{"name": GATE_NAME}],
                         [{"name": "pr-gate-missing"}])
    assert set(row) == {"number", "base_ref_name", "is_draft",
                        "author_login", "statusCheckRollup", "labels"}
    assert row["labels"] == [{"name": "pr-gate-missing"}]
    assert classify(row)[0] == "has_gate"


# ---------------------------------------------------------------------------
# (#15758) le login du bot depend de l'API qui le mesure
#
# Le collecteur lit REST `.user.login` -> `github-actions[bot]` ; GraphQL
# renvoie `app/github-actions` ; le slug nu `github-actions` apparait selon
# l'endpoint. Comparer a UNE seule orthographe rendait `bot_missing`
# inatteignable avec la forme meme du producteur (convention partagee avec
# guard_comment_upsert.GUARD_BOT_LOGINS et pick_idle_grain.AUTOMATION_AUTHORS).
# Chaque orthographe passe par `classify_input()` -- la fabrique reelle --
# jamais par un dict construit a la main avec les cles du consommateur.
# ---------------------------------------------------------------------------


def test_bot_verdict_reachable_for_every_measured_spelling():
    # Critere 1 : quelle que soit l'orthographe mesuree, la PR bot est
    # `bot_missing` / cause `bot` -- pas `missing`/`unknown`.
    for spelling in ("github-actions[bot]", "app/github-actions",
                     "github-actions"):
        row = classify_input(10558, "main", False, spelling,
                             _codeql_only_rollup())
        verdict, why = classify(row)
        assert verdict == "bot_missing", "%s: %s" % (spelling, why)
        cause, detail = prescribe(row)
        assert cause == "bot", spelling
        assert spelling in detail  # la valeur lue, pas une orthographe supposee


def test_human_pr_not_absorbed_by_bot_predicate():
    # Critere 2 : le predicat bot ne s'attrape pas les auteurs humains.
    row = classify_input(10902, "main", False, "jsboige", _codeql_only_rollup())
    verdict, why = classify(row)
    assert verdict == "missing", why
    assert prescribe(row)[0] == "unknown"


def test_bot_with_gate_still_has_gate_any_spelling():
    # Critere 4 : elargir le predicat bot ne derobe pas `has_gate`.
    rollup = _codeql_only_rollup() + [{"name": GATE_NAME, "conclusion": "SUCCESS"}]
    for spelling in ("github-actions[bot]", "app/github-actions",
                     "github-actions"):
        row = classify_input(10558, "main", False, spelling, rollup)
        assert classify(row)[0] == "has_gate", spelling


def test_label_descriptions_within_github_limit():
    # GitHub refuse une description de plus de 100 caracteres. Mesure #15621 :
    # 108 / 121 / 145 -- `gh label create` echouait, l'echec etait avale, et les
    # trois labels etaient absents du depot (404) alors que le sweep lisait
    # `mode=apply` sept jours de suite.
    for name, desc in (("pr-gate-missing", LABEL_DESC),
                       ("pr-gate-missing-bot", LABEL_BOT_DESC),
                       ("pr-gate-conflict", LABEL_CONFLICT_DESC)):
        assert len(desc) <= 100, "%s: %d caracteres" % (name, len(desc))


def _gh_proc(returncode, stderr=""):
    class _Proc:
        pass
    p = _Proc()
    p.returncode = returncode
    p.stderr = stderr
    p.stdout = ""
    return p


def test_write_failure_is_reported_not_swallowed():
    # Critere d'acceptation 3 : un refus de gh n'est plus silencieux.
    err = io.StringIO()
    with mock.patch("pr_gate_missing.subprocess.run",
                    lambda *a, **k: _gh_proc(1, "description is too long\n")), \
         redirect_stderr(err):
        ok = _gh_write(["label", "create", "pr-gate-missing"], "label create")
    assert ok is False
    assert "WARNING" in err.getvalue()
    assert "too long" in err.getvalue()


def test_write_success_stays_quiet():
    err = io.StringIO()
    with mock.patch("pr_gate_missing.subprocess.run",
                    lambda *a, **k: _gh_proc(0)), redirect_stderr(err):
        ok = _gh_write(["label", "create", "pr-gate-missing"], "label create")
    assert ok is True
    assert err.getvalue() == ""


# ---------------------------------------------------------------------------
# (#15621, Hermes point 3) la reclassee retracte ses artefacts faux
# ---------------------------------------------------------------------------


def _run_main(pr_row, labeled_map=None, comment_id=None):
    """Drive main() in apply mode with every network touch patched.

    The retraction path for `excluded_base`/`draft` is WIRLING (labels map +
    comment lookup + writes), invisible to a classify()-only test -- the same
    blind spot that let the GraphQL/REST mismatch live for weeks.
    """
    labeled_map = labeled_map or {}
    with mock.patch("pr_gate_missing.ensure_label", lambda *a, **k: None), \
         mock.patch("pr_gate_missing.list_open_prs", lambda repo: [pr_row]), \
         mock.patch("pr_gate_missing.labeled_prs",
                    lambda repo, label: labeled_map.get(label, {})), \
         mock.patch("pr_gate_missing.existing_comment",
                    lambda repo, number: comment_id), \
         mock.patch("pr_gate_missing.remove_label") as remove, \
         mock.patch("pr_gate_missing.retract_comment") as retract, \
         mock.patch("pr_gate_missing.apply_label") as apply_l, \
         mock.patch("pr_gate_missing.post_comment") as post:
        rc = main(["--repo", "jsboige/CoursIA"])
    return rc, remove, retract, apply_l, post


def test_reclassified_pr_loses_label_and_false_comment():
    # #15620 telle que mesuree par Hermes : stackee (base != main), classee
    # `missing` par le collapse de forme, label + commentaire faux poses.
    row = classify_input(15620, "fix/15489-kernel-suffix-canon-guard", False,
                         "jsboige", [], [{"name": "pr-gate-missing"}])
    rc, remove, retract, apply_l, post = _run_main(
        row, labeled_map={"pr-gate-missing": {15620: True}}, comment_id=42)
    assert rc == 0
    assert remove.call_count == 1
    assert remove.call_args[0] == ("jsboige/CoursIA", 15620,
                                   "pr-gate-missing", False)
    assert retract.call_count == 1
    repo, cid, body, dry = retract.call_args[0]
    assert (repo, cid, dry) == ("jsboige/CoursIA", 42, False)
    # La retraction est SANS marqueurs : une rechute reelle doit reposter une
    # remediation fraiche, pas rester muette sur un commentaire retracte.
    assert COMMENT_MARKER_START not in body and COMMENT_MARKER_END not in body
    assert "excluded_base" in body
    assert apply_l.call_count == 0 and post.call_count == 0


def test_reclassified_draft_retracts_too():
    row = classify_input(15334, "main", True, "jsboige", [],
                         [{"name": "pr-gate-conflict"}])
    rc, remove, retract, _, _ = _run_main(
        row, labeled_map={"pr-gate-conflict": {15334: True}}, comment_id=None)
    assert rc == 0
    assert remove.call_count == 1
    assert remove.call_args[0][2] == "pr-gate-conflict"
    assert retract.call_count == 0  # pas de commentaire marque -> rien a reecrire


def test_retraction_is_idempotent():
    # Deuxieme passage : plus de label, plus de commentaire -> aucun geste.
    row = classify_input(15609, "feature/15479-ict-torch-hooks", False,
                         "jsboige", [])
    rc, remove, retract, apply_l, post = _run_main(row)
    assert rc == 0
    assert remove.call_count == 0
    assert retract.call_count == 0
    assert apply_l.call_count == 0 and post.call_count == 0
