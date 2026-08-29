#!/usr/bin/env python3
"""Wiring tests for the OVERRIDE unblock path of variation-tag-guard (#13401).

The defect #13401 pins: the `[G-VAR-3 OVERRIDE]` marker made the comment job
post a SUCCESS check-run under a DISTINCT name (`Require genre diversity vs
prev: (...)`, colon form) -- an informational breadcrumb -- while the
REQUIRED check (the pull_request job's name) and the `PR gate` aggregate
(the only check required by branch protection) kept their stale red. A human
had to `gh run rerun` by hand (measured live on PR #13387 head 2202fcb864).

Renaming the POST to the required name is dead on arrival (#11519): GitHub
requires EVERY check-run bearing a required check's name to be green -- an
AND, not latest-wins -- so a green POST beside the old red run unblocks
nothing. The validated mechanism is RE-RUN, NEVER POST: re-running the
original run produces a check-run in the SAME suite, where latest-wins
holds. These tests pin that wiring:

  1. the comment job carries `actions: write` (job-level permissions
     REPLACE workflow-level ones -- without it, `gh run rerun` fails);
  2. the verdict-green branch re-runs this workflow's own pull_request run
     (filtered by `--event pull_request`, so the comment run itself is
     never the target) AND the latest "PR gate" run for the same head SHA;
  3. the reruns sit ONLY in the RC=0 branch -- the failure path (RC != 0)
     exits 1 before reaching them, and the out-of-scope early exits
     (bot author / fork PR) live before the RC=0 marker;
  4. the re-run degrades LOUDLY (`::warning::` + breadcrumb summary) when
     no completed target run exists -- never silently.

Run:
    python -m pytest scripts/tests/test_variation_tag_override_rerun.py
"""
from __future__ import annotations

from pathlib import Path

import yaml

WORKFLOW = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "variation-tag-guard.yml"
COMMENT_JOB = "check-variation-adjacency-comment"


def _load() -> dict:
    return yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))


def _comment_job_run_script() -> str:
    """Concatenated `run:` bodies of the comment job (single big step today;
    the concatenation keeps the assertions robust to a later step split)."""
    job = _load()["jobs"][COMMENT_JOB]
    return "\n".join(step.get("run", "") for step in job["steps"])


def test_comment_job_has_actions_write_permission():
    """`gh run rerun` exige actions:write ; les permissions job-level
    REMPLACENT (ne fusionnent pas) celles du workflow -- il faut la
    redeclarer sur CE job, pas seulement au niveau workflow."""
    perms = _load()["jobs"][COMMENT_JOB].get("permissions") or {}
    assert perms.get("actions") == "write", (
        "actions:write absente du job commentaire : le `gh run rerun` du run "
        "original echouerait et l'OVERRIDE #13401 ne deverrouillerait toujours rien"
    )


def test_verdict_green_branch_re_runs_original_guard_pull_request_run():
    run = _comment_job_run_script()
    assert "gh run rerun" in run, (
        "recette de re-run absente : le POST sous nom distinct ne deverrouille rien (#13401)"
    )
    assert "--workflow variation-tag-guard.yml" in run, (
        "le rerun du garde doit cibler CE workflow (variation-tag-guard.yml)"
    )
    assert "--event pull_request" in run, (
        "le rerun du garde doit filtrer --event pull_request : le run issue_comment "
        "de ce job ne porte pas le nom du check requis"
    )


def test_verdict_green_branch_re_runs_pr_gate_aggregate():
    run = _comment_job_run_script()
    assert 'select(.name == "PR gate")' in run, (
        "le rerun doit AUSSI cibler l'agregat PR gate (le seul check requis par la "
        "branch protection) pour le meme SHA -- recette pr-gate-rerun.yml (#11519)"
    )
    assert "head_sha=${HEAD_SHA}" in run, (
        "le ciblage des runs doit etre le SHA de tete resolu de la PR, pas le SHA de l'evenement"
    )


def test_rerun_is_gated_to_the_verdict_green_branch():
    """Le rerun doit sieger dans la branche RC=0 (verdict vert : OVERRIDE
    accepte ou adjacence reellement OK) -- le chemin bloquant (RC != 0)
    sort en exit 1 AVANT de l'atteindre, et les sorties anticipees
    hors-scope (bot / fork) sont avant le marqueur RC=0."""
    run = _comment_job_run_script()
    rc0 = run.find('"$RC" -eq 0')
    assert rc0 != -1, "marqueur RC=0 introuvable dans le script du job commentaire"
    rerun = run.find("gh run rerun")
    assert rerun > rc0, (
        "gh run rerun doit etre APRES le marqueur RC=0 (branche verdict vert) : un "
        "rerun place avant executerait aussi sur le chemin bloquant et les cas hors-scope"
    )
    # La sortie verte de la branche RC=0 est APRES le rerun : le chemin
    # echec (fall-through, exit 1) ne peut pas l'avoir traverse.
    green_exit = run.find("exit 0", rc0)
    assert -1 < rerun < green_exit, "le rerun doit etre contenu dans la branche RC=0 (avant son exit 0)"
    # Chemin echec : post_check failure ... exit 1, sans aucun rerun entre
    # les deux (verdict rouge = on bloque, on ne re-run rien).
    fail_post = run.find("post_check failure")
    fail_exit = run.find("exit 1", fail_post)
    assert fail_post != -1 and fail_exit != -1, "chemin bloquant (post_check failure / exit 1) introuvable"
    assert "gh run rerun" not in run[fail_post:fail_exit], (
        "le chemin bloquant ne doit PAS re-runner les gates (#13401 : le rerun est la "
        "recompense du verdict vert, pas du rouge)"
    )
    # Hors-scope (bot, fork) : sorties anticipees AVANT le marqueur RC=0,
    # donc hors de portee du rerun.
    assert "gh run rerun" not in run[:rc0], (
        "un rerun avant le marqueur RC=0 toucherait aussi les cas hors-scope (bot/fork) "
        "qui sortent en succes sans verdict de garde"
    )


def test_rerun_degrades_loudly_not_silently():
    """Pas de run cible termine (ou rerun rejete par l'API) => ::warning::
    explicite demandant un rerun manuel -- un deverrouillage qui echoue en
    silence laisse croire que l'OVERRIDE a marche (#13401)."""
    run = _comment_job_run_script()
    warnings = [ln for ln in run.splitlines() if "::warning::" in ln]
    assert warnings and any("rerun" in ln.lower() for ln in warnings), (
        "le fallback d'un rerun impossible doit se voir (::warning:: ... rerun MANUEL requis)"
    )


def test_success_breadcrumb_summary_mentions_the_rerun():
    """Le temoin de succes (POST sous le nom distinct) doit signaler que les
    runs requis ont ete re-declenches -- sinon le lecteur de la vue PR ne
    fait pas le lien temoin vert <-> deverrouillage en cours."""
    run = _comment_job_run_script()
    rc0 = run.find('"$RC" -eq 0')
    green = run[rc0 : run.find("exit 0", rc0)]
    success_calls = [ln for ln in green.splitlines() if "post_check success" in ln]
    assert success_calls, "post_check success absent de la branche RC=0"
    assert "RERUN_NOTES" in success_calls[0], (
        "le summary du temoin de succes doit mentionner l'etat du re-trigger des runs requis"
    )
