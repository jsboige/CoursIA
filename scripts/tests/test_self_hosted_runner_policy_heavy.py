#!/usr/bin/env python3
"""Le routage par label de la famille LOURDE (#21978).

La famille `coursia-persistent` (les slots `persist` de po-2024, 4 Gio /
512 pids) doit recevoir les jobs dont la consommation depasse le cap du
pool ordinaire. Le routage est une CHAINE de gardes : la famille lourde
quand un operateur l'active, la famille ordinaire sinon.

Ce que ces tests tiennent :

1. **Controle positif** -- la forme hybride a jambe lourde (un seul
   repli heberge) et la forme chaine (deux jambes + repli) sont admises
   dans les workflows autorises ;
2. **Controle negatif** -- la famille lourde est REFUSEE hors de la liste
   des workflows qui peuvent porter un job lourd ;
3. **Controle negatif** -- une jambe dont la garde ou le jeu de labels
   n'est pas enumere reste hors audit (DYNAMIC_RUNS_ON, refus inchange) ;
4. **Controle negatif** -- la selection STATIQUE de la famille lourde reste
   refusee : la famille n'est atteignable que par la forme auditee.

Run: python -m pytest scripts/tests/test_self_hosted_runner_policy_heavy.py
"""
from __future__ import annotations

import sys
import textwrap
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import check_self_hosted_runner_policy as policy  # noqa: E402

SAME_REPO = "github.event.pull_request.head.repo.full_name == github.repository"

#: Forme hybride a jambe lourde : le golden-set (repli heberge).
HEAVY_HYBRID = (
    "${{ (" + SAME_REPO + " && vars.CI_HEAVY_PERSISTENT == 'true') "
    "&& fromJSON('[\"self-hosted\",\"coursia-persistent\",\"coursia-linux\"]') "
    "|| 'ubuntu-latest' }}"
)

#: Forme chaine : la famille lourde, sinon le pool de debordement, sinon
#: l'offre GitHub (le job ICT).
HEAVY_CHAIN = (
    "${{ (" + SAME_REPO + " && vars.CI_HEAVY_PERSISTENT == 'true') "
    "&& fromJSON('[\"self-hosted\",\"coursia-persistent\",\"coursia-linux\"]') "
    "|| (" + SAME_REPO + " && vars.CI_OVERFLOW_LOCAL == 'true') "
    "&& fromJSON('[\"self-hosted\",\"coursia-ephemeral\",\"coursia-linux\"]') "
    "|| 'ubuntu-latest' }}"
)

#: Chaine a repli AUTO-HEBERGE (le job CPU) : la garde meme-depot du job
#: devient obligatoire, comme pour le slot reserve de `main`.
HEAVY_CHAIN_SELF_HOSTED_FALLBACK = (
    "${{ (github.event_name == 'push') "
    "&& fromJSON('[\"self-hosted\",\"coursia-main\",\"coursia-linux\"]') "
    "|| (" + SAME_REPO + " && vars.CI_HEAVY_PERSISTENT == 'true') "
    "&& fromJSON('[\"self-hosted\",\"coursia-persistent\",\"coursia-linux\"]') "
    "|| fromJSON('[\"self-hosted\",\"coursia-ephemeral\",\"coursia-linux\"]') }}"
)

JOB_GUARD = (
    "(github.event.pull_request.head.repo.full_name == null || "
    "github.event.pull_request.head.repo.full_name == github.repository)"
)


def write_workflow(tmp_path: Path, name: str, body: str) -> Path:
    path = tmp_path / f"{name}.yml"
    path.write_text(textwrap.dedent(body), encoding="utf-8")
    return path


def codes(result: policy.ScanResult) -> set[str]:
    return {item.code for item in result.violations}


# ---------------------------------------------------------------------------
# 1. controles positifs
# ---------------------------------------------------------------------------


def test_la_forme_hybride_lourde_est_admise_dans_un_workflow_autorise(tmp_path):
    """POSITIVE CONTROL: the heavy hybrid form is accepted.

    The guard lives inside the expression (same-repo AND the operator
    switch), so a fork payload cannot reach the family.
    """
    write_workflow(tmp_path, "notebook-execution-required", """
        name: Notebook Execution Required
        on: [pull_request]
        jobs:
          golden-set-execute:
            name: Golden-set execution (H.7 P3)
            runs-on: RUNSON
            timeout-minutes: 20
            steps:
              - run: echo golden
        """.replace("RUNSON", HEAVY_HYBRID))
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert result.violations == []
    assert result.self_hosted_jobs == 1


def test_la_forme_chaine_lourde_est_admise_dans_un_workflow_autorise(tmp_path):
    """POSITIVE CONTROL: the routing chain is accepted.

    Two legs, each with its own enumerated guard, and a hosted fallback:
    the audited form of the heavy routing.
    """
    write_workflow(tmp_path, "ict-tests", """
        name: ICT-Series Tests
        on: [pull_request]
        jobs:
          ict-tests:
            name: ICT suite
            runs-on: RUNSON
            timeout-minutes: 30
            steps:
              - run: echo ict
        """.replace("RUNSON", HEAVY_CHAIN))
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert result.violations == []
    assert result.self_hosted_jobs == 1


def test_la_chaine_a_repli_auto_heberge_exige_la_garde_du_job(tmp_path):
    """NEGATIVE CONTROL: a self-hosted fallback demands the job-level guard.

    The fallback leg is reached by ANY pull request, a fork included: the
    guard of the job is what protects the local park, exactly as for the
    reserved `main` slot.
    """
    write_workflow(tmp_path, "scripts-tests", """
        name: Scripts Tests
        on: [pull_request]
        jobs:
          scripts-tests:
            name: Scripts Tests (CPU)
            runs-on: RUNSON
            timeout-minutes: 40
            steps:
              - run: echo cpu
        """.replace("RUNSON", HEAVY_CHAIN_SELF_HOSTED_FALLBACK))
    without_guard = policy.scan_workflows(tmp_path)
    assert "SAME_REPO_GUARD" in codes(without_guard)

    write_workflow(tmp_path, "scripts-tests", """
        name: Scripts Tests
        on: [pull_request]
        jobs:
          scripts-tests:
            name: Scripts Tests (CPU)
            if: JOBGUARD
            runs-on: RUNSON
            timeout-minutes: 40
            steps:
              - run: echo cpu
        """.replace("RUNSON", HEAVY_CHAIN_SELF_HOSTED_FALLBACK)
            .replace("JOBGUARD", JOB_GUARD))
    with_guard = policy.scan_workflows(tmp_path)
    assert with_guard.broken == []
    assert with_guard.violations == []


# ---------------------------------------------------------------------------
# 2. la famille lourde est reservee
# ---------------------------------------------------------------------------


def test_la_famille_lourde_est_refusee_hors_des_workflows_autorises(tmp_path):
    """NEGATIVE CONTROL: the heavy family is reserved.

    A workflow outside HEAVY_WORKFLOW_ALLOWLIST that names the heavy label
    set is refused -- the switch being on does not authorise it.
    """
    write_workflow(tmp_path, "workflow-inconnu", """
        name: Inconnu
        on: [pull_request]
        jobs:
          job:
            name: job
            runs-on: RUNSON
            timeout-minutes: 10
            steps:
              - run: echo x
        """.replace("RUNSON", HEAVY_HYBRID))
    result = policy.scan_workflows(tmp_path)
    assert "HEAVY_WORKFLOW_NOT_ALLOWED" in codes(result)


def test_la_selection_statique_de_la_famille_lourde_reste_refusee(tmp_path):
    """NEGATIVE CONTROL: a static heavy selection stays refused.

    The family is reachable only through the audited form: a static
    `runs-on` would let any workflow (and any trigger) reach it.
    """
    write_workflow(tmp_path, "scripts-tests", """
        name: Scripts Tests
        on: [pull_request]
        jobs:
          scripts-tests:
            name: Scripts Tests (CPU)
            if: JOBGUARD
            runs-on: [self-hosted, coursia-persistent, coursia-linux]
            timeout-minutes: 40
            steps:
              - run: echo cpu
        """.replace("JOBGUARD", JOB_GUARD))
    result = policy.scan_workflows(tmp_path)
    assert "RUNNER_LABELS" in codes(result)


# ---------------------------------------------------------------------------
# 3. la forme reste auditee : rien d'illustre n'entre
# ---------------------------------------------------------------------------


def test_une_garde_non_enumernee_dans_une_chaine_est_refusee(tmp_path):
    """NEGATIVE CONTROL: an unenumerated guard stays out of audit.

    The chain is audited leg by leg; a guard that is not in
    CHAIN_LEG_LABEL_SETS makes the whole expression unauditable.
    """
    expression = HEAVY_CHAIN.replace(
        "vars.CI_HEAVY_PERSISTENT == 'true'",
        "vars.CI_AUTRE_CHOSE == 'true'",
    )
    write_workflow(tmp_path, "ict-tests", """
        name: ICT-Series Tests
        on: [pull_request]
        jobs:
          ict-tests:
            name: ICT suite
            runs-on: RUNSON
            timeout-minutes: 30
            steps:
              - run: echo ict
        """.replace("RUNSON", expression))
    result = policy.scan_workflows(tmp_path)
    assert codes(result) == {"DYNAMIC_RUNS_ON"}
    assert result.self_hosted_jobs == 0


def test_un_jeu_de_labels_non_admis_dans_une_chaine_est_refuse(tmp_path):
    """NEGATIVE CONTROL: the labels of a leg are not free.

    The heavy guard admits exactly the heavy label set; swapping it for
    another pool leaves the expression unauditable.
    """
    expression = HEAVY_CHAIN.replace(
        "[\"self-hosted\",\"coursia-persistent\",\"coursia-linux\"]",
        "[\"self-hosted\",\"coursia-ephemeral\",\"coursia-linux\"]",
    )
    write_workflow(tmp_path, "ict-tests", """
        name: ICT-Series Tests
        on: [pull_request]
        jobs:
          ict-tests:
            name: ICT suite
            runs-on: RUNSON
            timeout-minutes: 30
            steps:
              - run: echo ict
        """.replace("RUNSON", expression))
    result = policy.scan_workflows(tmp_path)
    assert codes(result) == {"DYNAMIC_RUNS_ON"}
    assert result.self_hosted_jobs == 0


def test_un_repli_auto_heberge_non_enumere_est_refuse(tmp_path):
    """NEGATIVE CONTROL: the self-hosted fallback is enumerated.

    A chain may fall back on the PR pool; any other self-hosted fallback
    is out of audit.
    """
    expression = HEAVY_CHAIN.replace(
        "|| 'ubuntu-latest' }}",
        "|| fromJSON('[\"self-hosted\",\"coursia-waiter\"]') }}",
    )
    write_workflow(tmp_path, "ict-tests", """
        name: ICT-Series Tests
        on: [pull_request]
        jobs:
          ict-tests:
            name: ICT suite
            runs-on: RUNSON
            timeout-minutes: 30
            steps:
              - run: echo ict
        """.replace("RUNSON", expression))
    result = policy.scan_workflows(tmp_path)
    assert codes(result) == {"DYNAMIC_RUNS_ON"}


def test_une_chaine_sans_repli_est_refusee(tmp_path):
    """NEGATIVE CONTROL: a chain without a fallback is not a chain.

    Two legs and no fallback would leave the job without a target when
    every guard is false.
    """
    expression = HEAVY_CHAIN.replace(" || 'ubuntu-latest'", "")
    write_workflow(tmp_path, "ict-tests", """
        name: ICT-Series Tests
        on: [pull_request]
        jobs:
          ict-tests:
            name: ICT suite
            runs-on: RUNSON
            timeout-minutes: 30
            steps:
              - run: echo ict
        """.replace("RUNSON", expression))
    result = policy.scan_workflows(tmp_path)
    assert codes(result) == {"DYNAMIC_RUNS_ON"}


def test_la_forme_simple_hybride_reste_admise_sans_chaine(tmp_path):
    """The single-leg hybrid form is unchanged by the chain work.

    The chain is a second audited form, never a replacement: a workflow
    that uses the plain hybrid keeps its verdicts.
    """
    write_workflow(tmp_path, "always-on-guards", """
        name: Always-on guards
        on: [pull_request]
        jobs:
          guards:
            name: guards
            runs-on: ${{ (github.event.pull_request.head.repo.full_name == github.repository && vars.CI_OVERFLOW_LOCAL == 'true') && fromJSON('["self-hosted","coursia-ephemeral","coursia-linux"]') || 'ubuntu-latest' }}
            timeout-minutes: 20
            steps:
              - run: echo guards
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert result.violations == []
    assert result.self_hosted_jobs == 1
