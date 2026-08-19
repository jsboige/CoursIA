#!/usr/bin/env python3
"""Wiring tests for the issue_comment path of variation-tag-guard (#11718).

The defect #11718 pins is a WIRING defect, not a logic defect: the
`[G-VAR-3 OVERRIDE]` marker lives in PR *comments*, but the workflow only
triggered on pull_request events -- posting the marker relaunched nothing.
The pure decision logic (variation_adjacency_guard.py) is already covered by
test_variation_adjacency_guard.py; this file pins the YAML harness so the
wiring cannot silently regress:

  1. issue_comment (created + edited) is a trigger;
  2. every job that reads `github.event.pull_request.*` is gated out of
     issue_comment runs (that context does not exist there -- ungated, the
     jobs would run red on every comment);
  3. the dedicated comment job exists, filters to PRs (not issues), skips
     bot comments (anti-loop: the block path of the pull_request job posts
     as github-actions[bot]), and resolves the PR head SHA itself;
  4. the check-run it posts carries the SAME name as the pull_request job
     so the aggregator (pr_gate) sees the fresh verdict supersede the stale
     one on the PR head.
  5. an entry guard keeps the job off comments that carry no
     [G-VAR-3 OVERRIDE] marker (#11782) -- a comment without the marker is
     information-free for this gate and must cost zero runner time.

Run:
    python -m pytest scripts/tests/test_variation_tag_comment_trigger.py
"""
from __future__ import annotations

from pathlib import Path

import yaml

WORKFLOW = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "variation-tag-guard.yml"

ADJACENCY_CHECK_NAME = "Require genre diversity vs prev: (block on LIGHT adjacency, #11170)"
COMMENT_JOB = "check-variation-adjacency-comment"


def _load() -> dict:
    return yaml.safe_load(WORKFLOW.read_text(encoding="utf-8"))


def _on(wf: dict) -> dict:
    # YAML 1.1 parses the bare `on:` key as boolean True.
    return wf.get(True, wf.get("on", {}))


def test_issue_comment_is_a_trigger_with_created_and_edited():
    trig = _on(_load()).get("issue_comment")
    assert trig is not None, "issue_comment trigger absent (#11718: le marqueur OVERRIDE vit en commentaire)"
    assert "created" in trig["types"], "created manquant : poster le marqueur ne relance rien"
    assert "edited" in trig["types"], "edited manquant : corriger un marqueur ne relance rien"


def test_every_pull_request_job_is_gated_out_of_issue_comment():
    """github.event.pull_request n'existe pas sur issue_comment : tout job qui
    le lit doit refuser de tourner sur cet evenement (sinon rouge systematique
    a chaque commentaire)."""
    wf = _load()
    offenders = []
    for jid, job in wf["jobs"].items():
        if jid == COMMENT_JOB:
            continue
        reads_pr_ctx = "github.event.pull_request" in yaml.safe_dump(job)
        if not reads_pr_ctx:
            continue
        cond = str(job.get("if", ""))
        assert cond, f"job {jid} lit github.event.pull_request sans if: ( Crash sur issue_comment)"
        if "github.event_name != 'issue_comment'" not in cond:
            offenders.append(jid)
    assert not offenders, f"jobs non gates hors issue_comment : {offenders}"


def test_comment_job_exists_and_filters_to_prs_and_bots():
    wf = _load()
    job = wf["jobs"].get(COMMENT_JOB)
    assert job is not None, f"{COMMENT_JOB} absent"
    cond = str(job.get("if", ""))
    assert "github.event.issue.pull_request" in cond, (
        "le job doit se limiter aux commentaires de PR (issue_comment fire aussi sur les issues)"
    )
    assert "github.event.comment.user.login != 'github-actions[bot]'" in cond, (
        "anti-boucle absent : le commentaire bloquant du chemin pull_request (github-actions[bot]) redeclencherait ce job a l'infini"
    )


def test_comment_job_resolves_head_sha_and_posts_check_run_on_it():
    """Le check-run doit se poser sur le SHA de TETE de la PR -- pas sur le SHA
    de l'evenement (branche par defaut), sinon l'agregateur PR gate ne le voit
    pas (fantome workflow_run, cf #11718 commentaire ai-01)."""
    wf = _load()
    job = wf["jobs"][COMMENT_JOB]
    run = ""
    for step in job["steps"]:
        run += step.get("run", "") + "\n"
    assert 'pulls/${ISSUE_NUMBER}' in run, "la PR doit etre resolue depuis github.event.issue.number (github.event.pull_request n'existe pas)"
    assert "['head']['sha']" in run or "head.sha" in run, "le SHA de tete doit etre extrait explicitement"
    assert "/check-runs" in run, "le verdict doit etre poste en check-run sur la tete"
    assert 'os.environ["HEAD_SHA"]' in run, "le check-run doit porter head_sha (pas le SHA de l'evenement)"


def test_comment_job_check_run_name_matches_pull_request_job():
    """Meme nom que le job pull_request : le verdict recent supplant le rouge
    gele dans la vue PR et l'agregateur."""
    wf = _load()
    names = {j.get("name") for j in wf["jobs"].values()}
    assert wf["jobs"][COMMENT_JOB]["name"] == ADJACENCY_CHECK_NAME
    # ... et ce nom est bien celui du job pull_request (unicite du porteur)
    bearers = [jid for jid, j in wf["jobs"].items() if j.get("name") == ADJACENCY_CHECK_NAME]
    assert sorted(bearers) == sorted([COMMENT_JOB, "check-variation-adjacency-required"])


def test_comment_job_checks_out_default_branch_code():
    """Sur issue_comment le checkout est la branche par defaut : c'est le
    POINT (gate courant, jamais la version gelee dans refs/pull/N/merge).
    Un `with: ref:` revenu sur ce job reintroduirait le gel."""
    wf = _load()
    checkout = [s for s in wf["jobs"][COMMENT_JOB]["steps"] if "checkout" in str(s.get("uses", ""))][0]
    assert "ref" not in checkout.get("with", {}), (
        "le checkout du chemin commentaire ne doit PAS pin de ref : il execute le gate de la branche par defaut (diagnostic #11718)"
    )


def test_comment_job_entry_guard_requires_override_marker():
    """#11782 : le job ne doit tourner QUE sur les commentaires portant le
    marqueur -- un if: de job est evalue sans allouer de runner, donc un
    commentaire sans [G-VAR-3 OVERRIDE] ne coute rien. Sans ce garde, chaque
    commentaire de PR (steer, ACK, review, reponse) relance le job pour ne
    rien decider : le guard ne lit les commentaires QUE pour le marqueur
    (variation_adjacency_guard.parse_override), tout le reste est du passage
    a vide.

    Le garde doit rester COMBINE en ET a `github.event_name == 'issue_comment'`
    : la forme `event_name != 'issue_comment' || contains(...)` (esquissee
    dans l'issue) laisserait aussi entrer les evenements pull_request dans ce
    job chemin-commentaire -- doublon du job pull_request (acceptance 3).
    """
    wf = _load()
    cond = str(wf["jobs"][COMMENT_JOB].get("if", ""))
    assert "github.event_name == 'issue_comment'" in cond, (
        "le garde marqueur ne doit pas remplacer la restriction issue_comment (acceptance 3 de #11782)"
    )
    assert "contains(github.event.comment.body, '[G-VAR-3 OVERRIDE]')" in cond, (
        "garde d'entree absent : tout commentaire de PR relance le job (#11782 -- 11 runs/edition mesures sur #11405)"
    )
