from __future__ import annotations

import json
import sys
import textwrap
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import check_self_hosted_runner_policy as policy  # noqa: E402


def write_workflow(tmp_path: Path, name: str, body: str, suffix: str = ".yml") -> Path:
    path = tmp_path / f"{name}{suffix}"
    path.write_text(textwrap.dedent(body), encoding="utf-8")
    return path


def codes(result: policy.ScanResult) -> set[str]:
    return {item.code for item in result.violations}


def test_current_repository_self_hosted_jobs_satisfy_isolation_policy(capsys):
    # The baseline is POLICY COMPLIANCE (0 violation), not a count of zero
    # self-hosted jobs: allowlisted workflows (#13135) may legitimately run
    # self-hosted jobs, and asserting the count would make the next legitimate
    # runner workflow redden the same way.
    result = policy.scan_workflows()
    assert result.broken == []
    assert result.violations == []
    assert result.workflows_scanned > 0
    assert policy.main(["--check"]) == policy.EXIT_OK
    out = capsys.readouterr().out
    assert "[self-hosted-policy] OK" in out
    if result.self_hosted_jobs == 0:
        assert "explicit baseline: 0 self-hosted jobs" in out
    else:
        assert "all self-hosted jobs satisfy isolation policy" in out


def test_safe_pull_request_job_is_accepted(tmp_path):
    write_workflow(tmp_path, "pr-gate-stale-sweep", """
        name: safe
        on: [pull_request]
        jobs:
          test:
            if: ${{ github.event.pull_request.head.repo.full_name == github.repository }}
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo safe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert result.violations == []
    assert result.self_hosted_jobs == 1


def test_universal_pull_request_guard_is_accepted(tmp_path):
    """#13874 : la forme universelle (test du repo source sans enumerer
    github.event_name) couvre pull_request ET pull_request_target en un seul
    predicat. Elle doit etre acceptee par le checker au meme titre que la
    forme directe."""
    write_workflow(tmp_path, "pr-gate-stale-sweep", """
        name: safe-universal
        on: [pull_request]
        jobs:
          test:
            if: ${{ github.event.pull_request.head.repo.full_name == null || github.event.pull_request.head.repo.full_name == github.repository }}
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo safe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert result.violations == []
    assert result.self_hosted_jobs == 1


def test_universal_guard_with_combined_target_is_accepted(tmp_path):
    """#13874 : variante parentee -- la garde universelle combinee avec
    une selection de job (inputs.target == '...') reste acceptee. Cas reel :
    windows-self-hosted-tests.yml factorise la garde avec un `&&` de
    selection, le checker ne doit pas confondre ce `&&` avec une
    fragilisation. Trigger pull_request pour exercer le SAME_REPO_GUARD
    (le test serait silently-skipped sur workflow_dispatch seul)."""
    write_workflow(tmp_path, "windows-self-hosted-tests", """
        name: windows-universal
        on: [pull_request]
        jobs:
          test:
            if: ${{ (github.event.pull_request.head.repo.full_name == null || github.event.pull_request.head.repo.full_name == github.repository) && inputs.target == 'confinement' }}
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo safe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert result.violations == []
    assert result.self_hosted_jobs == 1


def test_bare_universal_guard_with_and_selection_is_rejected_with_parenthesis_hint(tmp_path):
    """#14148 (reserve NanoClaw n.1) : la forme universelle NUE combinee a un
    `&&` est refusee -- `&&` lie plus fort que `||`, donc la forme nue se lit
    `A == null || (A == repo && sel)` et tourne sur tout evenement hors
    pull_request quelle que soit la selection -- et le message nomme la
    parenthese requise, pas seulement « must lead with the guard »."""
    write_workflow(tmp_path, "windows-self-hosted-tests", """
        name: bare-universal-and
        on: [pull_request]
        jobs:
          test:
            if: ${{ github.event.pull_request.head.repo.full_name == null || github.event.pull_request.head.repo.full_name == github.repository && inputs.target == 'confinement' }}
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo unsafe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert codes(result) == {"SAME_REPO_GUARD"}
    [violation] = result.violations
    assert "parenthesised" in violation.message
    assert "(<universal guard>) && <selection>" in violation.message


def test_job_without_any_guard_keeps_generic_message(tmp_path):
    """Le message « parenthesised » est reserve a la forme universelle nue +
    `&&` : un job sans garde du tout garde le message generique."""
    write_workflow(tmp_path, "pr-gate-stale-sweep", """
        name: no-guard
        on: [pull_request]
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo unsafe
        """)
    [violation] = policy.scan_workflows(tmp_path).violations
    assert violation.code == "SAME_REPO_GUARD"
    assert "parenthesised" not in violation.message


def test_fork_reachable_comment_triggers_cannot_reach_self_hosted_job(tmp_path):
    """#14148 (reserve NanoClaw n.2) : issue_comment / pull_request_review /
    pull_request_review_comment tournent sur le code de la branche par defaut
    mais leur payload nomme une PR potentiellement issue d'un fork -- un
    `checkout refs/pull/N/head` executerait du code de fork sur le runner.
    Refuses comme pull_request_target, garde ou pas."""
    write_workflow(tmp_path, "pr-gate-stale-sweep", """
        name: comment-driven
        on: [issue_comment, pull_request_review, workflow_dispatch]
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo unsafe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    fork_reachable = [v for v in result.violations if v.code == "FORK_REACHABLE_TRIGGER"]
    assert sorted(v.message.split(" ")[0] for v in fork_reachable) == [
        "issue_comment",
        "pull_request_review",
    ]


def test_push_and_schedule_triggers_remain_accepted_with_universal_guard(tmp_path):
    """Contre-controle de la reserve n.2 : push / schedule / workflow_dispatch
    ne portent que des refs du depot -- la branche `== null` de la garde
    universelle y est sure par construction. Cas reels sur main :
    banner-guard.yml (pull_request + push), hooks-parity.yml (+ schedule)."""
    write_workflow(tmp_path, "pr-gate-stale-sweep", """
        name: push-schedule
        on:
          pull_request:
          push:
            branches: [main]
          schedule:
            - cron: '7 3 * * *'
          workflow_dispatch:
        jobs:
          test:
            if: ${{ github.event.pull_request.head.repo.full_name == null || github.event.pull_request.head.repo.full_name == github.repository }}
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo safe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert result.violations == []
    assert result.self_hosted_jobs == 1


def test_check_run_and_check_suite_fail_closed(tmp_path):
    """#14201 (tranche 2) : le denylist de #14148 (FORK_REACHABLE_TRIGGERS) est
    fail-OPEN sur tout trigger non enumere. check_run / check_suite portent
    pull_requests[] et un head_sha -- un `checkout ${{ ... head_sha }}`
    executerait du code de fork sur le runner, comme les triggers de
    commentaire que #14148 a fermes. L'allowlist default-deny doit les rejeter."""
    write_workflow(tmp_path, "pr-gate-stale-sweep", """
        name: check-driven
        on:
          check_run:
            types: [completed]
          check_suite:
            types: [completed]
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo unsafe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    [violation] = result.violations
    assert violation.code == "UNSAFE_TRIGGER"
    assert "check_run" in violation.message
    assert "check_suite" in violation.message


def test_unknown_trigger_is_default_denied(tmp_path):
    """#14201 (tranche 2) : un trigger inconnu du checker doit etre refuse par
    defaut (fail-closed), pas laisse passer parce que la liste des triggers
    dangereux est une enumeration. La plupart des candidats futurs de GitHub
    (release, deployment, registry_package, ...) sont ici rejetes."""
    write_workflow(tmp_path, "pr-gate-stale-sweep", """
        name: future-event
        on:
          release:
            types: [published]
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo unsafe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert "UNSAFE_TRIGGER" in codes(result)


def test_safe_allowlist_triggers_are_accepted(tmp_path):
    """Contre-controle de la frontiere allowlist : les QUATRE triggers du
    depot -- pull_request, push, schedule, workflow_dispatch -- sont acceptes
    ensemble sur un job self-hosted garde. C'est le complement du contre-
    controle de #14148 (push/schedule/workflow_dispatch seuls) : aucun des
    triggers reels de la tranche 1 ne doit devenir UNSAFE_TRIGGER."""
    write_workflow(tmp_path, "pr-gate-stale-sweep", """
        name: allowlist-safe
        on:
          pull_request:
          push:
            branches: [main]
          schedule:
            - cron: '7 3 * * *'
          workflow_dispatch:
        jobs:
          test:
            if: ${{ github.event.pull_request.head.repo.full_name == null || github.event.pull_request.head.repo.full_name == github.repository }}
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo safe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert result.violations == []
    assert result.self_hosted_jobs == 1


def test_universal_guard_weakened_by_or_is_rejected(tmp_path):
    """#13874 FN-safety : meme avec la forme universelle, l'ajout d'un
    `|| always()` ou `|| true` reintroduit le trou. La garde universelle
    doit etre le seul predicat -- le checker refuse tout court-circuit."""
    write_workflow(tmp_path, "pr-gate-stale-sweep", """
        name: weakened
        on: [pull_request]
        jobs:
          test:
            if: ${{ (github.event.pull_request.head.repo.full_name == null || github.event.pull_request.head.repo.full_name == github.repository) || always() }}
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo unsafe
        """)
    assert "SAME_REPO_GUARD" in codes(policy.scan_workflows(tmp_path))


def test_event_name_or_pattern_is_rejected(tmp_path):
    """#13874 FN-safety : la forme `github.event_name != 'pull_request' ||`
    (l'ancienne garde faible qui laisse passer pull_request_target) doit
    toujours etre refusee par le checker -- c'est precisement le defaut
    que l'issue signale. Le test pose les DEUX triggers pour reproduire
    le scenario d'evolution : quelqu'un ajoute pull_request_target a un
    workflow qui avait deja pull_request."""
    write_workflow(tmp_path, "pr-gate-stale-sweep", """
        name: weak-old
        on:
          pull_request:
          pull_request_target:
        jobs:
          test:
            if: ${{ github.event_name != 'pull_request' || github.event.pull_request.head.repo.full_name == github.repository }}
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo unsafe
        """)
    codes_set = codes(policy.scan_workflows(tmp_path))
    # La policy doit signaler le PULL_REQUEST_TARGET (deja couvert) ET le
    # SAME_REPO_GUARD (la forme ne correspond ni a la garde directe ni a
    # la forme universelle, elle est dans la zone grise entre les deux et
    # doit etre refusee).
    assert "PULL_REQUEST_TARGET" in codes_set
    assert "SAME_REPO_GUARD" in codes_set


def test_allowed_workflow_dispatch_job_does_not_need_pr_guard(tmp_path):
    write_workflow(tmp_path, "pr-gate-stale-sweep", """
        name: manual
        on: workflow_dispatch
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo safe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.violations == []
    assert result.self_hosted_jobs == 1


def test_exact_labels_outside_allowlist_are_rejected(tmp_path):
    write_workflow(tmp_path, "other-workflow", """
        name: other
        on: workflow_dispatch
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo unsafe
        """)
    assert codes(policy.scan_workflows(tmp_path)) == {"WORKFLOW_NOT_ALLOWED"}


def test_group_is_rejected_even_in_allowed_workflow(tmp_path):
    write_workflow(tmp_path, "pr-gate-stale-sweep", """
        name: group
        on: workflow_dispatch
        jobs:
          test:
            runs-on:
              group: coursia-ephemeral
              labels: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo unsafe
        """)
    assert codes(policy.scan_workflows(tmp_path)) == {"RUNNER_GROUP_UNAVAILABLE"}


def test_missing_label_is_rejected_in_allowed_workflow(tmp_path):
    write_workflow(tmp_path, "pr-gate-stale-sweep", """
        name: labels
        on: workflow_dispatch
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral]
            steps:
              - run: echo unsafe
        """)
    assert codes(policy.scan_workflows(tmp_path)) == {"RUNNER_LABELS"}


def test_linux_label_set_is_accepted_in_allowlisted_workflow(tmp_path):
    # Mission #13378: the containerized Linux runner (po-2024) carries its
    # own dedicated label set -- coursia-linux routes only to the container,
    # never to the Windows fast-guards runners.
    write_workflow(tmp_path, "linux-self-hosted-tests", """
        name: linux
        on: workflow_dispatch
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-linux]
            steps:
              - run: echo safe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.violations == []
    assert result.self_hosted_jobs == 1


def test_lean_label_set_is_accepted_in_allowlisted_workflow(tmp_path):
    # #14337: the specialised Lean pool (po-2024) carries its own dedicated
    # label set -- coursia-lean routes lake builds to the elan image with the
    # warm .lake work volume, never to the minimal linux image or the Windows
    # runners.
    write_workflow(tmp_path, "linux-self-hosted-tests", """
        name: lean
        on: workflow_dispatch
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-lean]
            steps:
              - run: echo safe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.violations == []
    assert result.self_hosted_jobs == 1


def test_mixed_lean_and_linux_labels_are_rejected(tmp_path):
    # Mixing the lean and linux dedicated sets must stay a violation: a job
    # eligible for both pools would make the routing guarantee meaningless.
    write_workflow(tmp_path, "linux-self-hosted-tests", """
        name: mixed
        on: workflow_dispatch
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-linux, coursia-lean]
            steps:
              - run: echo unsafe
        """)
    result = policy.scan_workflows(tmp_path)
    assert codes(result) == {"RUNNER_LABELS"}


def test_translation_hot_drift_advisory_is_allowlisted(tmp_path):
    """#15322/#15438 : le vehicule workflow_dispatch-ONLY du garde hot-drift
    par-PR (absorbe fast-lane TRANCHE2) est autorise sur la jambe Linux
    containerisee -- precedent repeated-prose-advisory / markdown-deaccent
    (cible d'identite + re-run manuel du self-test). Son non-allowlistage
    etait exactement le WORKFLOW_NOT_ALLOWED prouve par le run CPU frais."""
    assert "translation-hot-drift-advisory.yml" in policy.SELF_HOSTED_WORKFLOW_ALLOWLIST
    write_workflow(tmp_path, "translation-hot-drift-advisory", """
        name: translation-hot-drift
        on: workflow_dispatch
        jobs:
          advisory:
            runs-on: [self-hosted, coursia-ephemeral, coursia-linux]
            steps:
              - run: echo safe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert result.violations == []
    assert result.self_hosted_jobs == 1


def test_mixed_linux_and_fast_guards_labels_are_rejected(tmp_path):
    # Mixing the two dedicated sets must stay a violation: a job eligible
    # for both the Windows runners and the Linux container would make the
    # routing guarantee meaningless.
    write_workflow(tmp_path, "linux-self-hosted-tests", """
        name: mixed
        on: workflow_dispatch
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-linux, coursia-fast-guards]
            steps:
              - run: echo unsafe
        """)
    assert codes(policy.scan_workflows(tmp_path)) == {"RUNNER_LABELS"}


def test_unexpected_label_is_rejected_in_allowed_workflow(tmp_path):
    write_workflow(tmp_path, "pr-gate-stale-sweep", """
        name: labels
        on: workflow_dispatch
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards, windows]
            steps:
              - run: echo unsafe
        """)
    assert codes(policy.scan_workflows(tmp_path)) == {"RUNNER_LABELS"}


def test_yaml_extension_cannot_alias_allowlisted_workflow(tmp_path):
    write_workflow(tmp_path, "pr-gate-stale-sweep", """
        name: extension-alias
        on: workflow_dispatch
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo unsafe
        """, suffix=".yaml")
    assert codes(policy.scan_workflows(tmp_path)) == {"WORKFLOW_NOT_ALLOWED"}


def test_generic_self_hosted_scalar_is_rejected(tmp_path):
    write_workflow(tmp_path, "unsafe", """
        name: unsafe
        on: [pull_request]
        jobs:
          test:
            runs-on: self-hosted
            steps:
              - run: echo unsafe
        """)
    result = policy.scan_workflows(tmp_path)
    assert {"WORKFLOW_NOT_ALLOWED", "RUNNER_LABELS", "SAME_REPO_GUARD"} <= codes(result)


def test_self_hosted_list_without_group_is_rejected(tmp_path):
    write_workflow(tmp_path, "unsafe", """
        name: unsafe
        on: workflow_dispatch
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral]
            steps:
              - run: echo unsafe
        """)
    assert "WORKFLOW_NOT_ALLOWED" in codes(policy.scan_workflows(tmp_path))


def test_custom_label_without_self_hosted_token_is_still_self_hosted(tmp_path):
    write_workflow(tmp_path, "custom", """
        name: custom
        on: workflow_dispatch
        jobs:
          test:
            runs-on: coursia-ephemeral
            steps:
              - run: echo unsafe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.self_hosted_jobs == 1
    assert {"WORKFLOW_NOT_ALLOWED", "RUNNER_LABELS"} == codes(result)


def test_hosted_looking_custom_label_is_rejected_fail_closed(tmp_path):
    write_workflow(tmp_path, "custom-looking", """
        name: custom-looking
        on: workflow_dispatch
        jobs:
          test:
            runs-on: ubuntu-custom
            steps:
              - run: echo unsafe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.self_hosted_jobs == 1
    assert {"WORKFLOW_NOT_ALLOWED", "RUNNER_LABELS"} == codes(result)


def test_group_selection_is_self_hosted_even_without_labels(tmp_path):
    write_workflow(tmp_path, "group", """
        name: group
        on: workflow_dispatch
        jobs:
          test:
            runs-on:
              group: coursia-ephemeral
            steps:
              - run: echo unsafe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.self_hosted_jobs == 1
    assert codes(result) == {
        "RUNNER_GROUP_UNAVAILABLE",
        "RUNNER_LABELS",
        "WORKFLOW_NOT_ALLOWED",
    }


def test_self_hosted_label_is_case_insensitive(tmp_path):
    write_workflow(tmp_path, "case", """
        name: case
        on: workflow_dispatch
        jobs:
          test:
            runs-on: [Self-Hosted, coursia-ephemeral]
            steps:
              - run: echo unsafe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.self_hosted_jobs == 1
    assert "WORKFLOW_NOT_ALLOWED" in codes(result)


def test_wrong_group_and_missing_label_are_both_named(tmp_path):
    write_workflow(tmp_path, "unsafe", """
        name: unsafe
        on: workflow_dispatch
        jobs:
          test:
            runs-on:
              group: Default
              labels: [self-hosted, windows]
            steps:
              - run: echo unsafe
        """)
    result = policy.scan_workflows(tmp_path)
    assert {
        "RUNNER_GROUP_UNAVAILABLE",
        "RUNNER_LABELS",
        "WORKFLOW_NOT_ALLOWED",
    } == codes(result)


def test_dynamic_runs_on_is_rejected_fail_closed(tmp_path):
    write_workflow(tmp_path, "dynamic", """
        name: dynamic
        on: workflow_dispatch
        jobs:
          test:
            runs-on: ${{ matrix.runner }}
            strategy:
              matrix:
                runner: [ubuntu-latest, self-hosted]
            steps:
              - run: echo opaque
        """)
    result = policy.scan_workflows(tmp_path)
    assert codes(result) == {"DYNAMIC_RUNS_ON"}
    assert result.self_hosted_jobs == 0


HYBRID_RUNS_ON = (
    "${{ (github.event.pull_request.head.repo.full_name == github.repository)"
    " && fromJSON('[\"self-hosted\",\"coursia-waiter\"]') || 'ubuntu-latest' }}"
)


def test_hybrid_runs_on_waiter_form_is_accepted(tmp_path):
    # #13363 jambe B: the ONE audited dynamic form. pr-gate.yml is the only
    # consumer; the same-repo guard lives inside the expression, so no job
    # `if:` is required (the self-hosted labels are unreachable for forks).
    write_workflow(tmp_path, "pr-gate", """
        name: PR gate
        on:
          pull_request:
            branches: [main]
          workflow_dispatch:
        jobs:
          gate:
            name: PR gate
            runs-on: RUNSON
            steps:
              - run: echo aggregate
        """)
    (tmp_path / "pr-gate.yml").write_text(
        (tmp_path / "pr-gate.yml").read_text(encoding="utf-8").replace(
            "RUNSON", HYBRID_RUNS_ON
        ),
        encoding="utf-8",
    )
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert result.violations == []
    assert result.self_hosted_jobs == 1


def test_hybrid_runs_on_wrong_labels_is_rejected(tmp_path):
    write_workflow(tmp_path, "pr-gate", """
        name: PR gate
        on: workflow_dispatch
        jobs:
          gate:
            runs-on: ${{ (github.event.pull_request.head.repo.full_name == github.repository) && fromJSON('["self-hosted","coursia-linux"]') || 'ubuntu-latest' }}
            steps:
              - run: echo aggregate
        """)
    result = policy.scan_workflows(tmp_path)
    assert codes(result) == {"DYNAMIC_RUNS_ON"}
    assert result.self_hosted_jobs == 0


def test_hybrid_runs_on_wrong_fallback_is_rejected(tmp_path):
    write_workflow(tmp_path, "pr-gate", """
        name: PR gate
        on: workflow_dispatch
        jobs:
          gate:
            runs-on: ${{ (github.event.pull_request.head.repo.full_name == github.repository) && fromJSON('["self-hosted","coursia-waiter"]') || 'ubuntu-24.04' }}
            steps:
              - run: echo aggregate
        """)
    result = policy.scan_workflows(tmp_path)
    assert codes(result) == {"DYNAMIC_RUNS_ON"}


def test_hybrid_runs_on_universal_guard_is_rejected(tmp_path):
    # The universal guard (|| null) inside the hybrid form would route
    # workflow_dispatch runs to the waiter pool; only the strict same-repo
    # equality is audited.
    write_workflow(tmp_path, "pr-gate", """
        name: PR gate
        on: workflow_dispatch
        jobs:
          gate:
            runs-on: ${{ (github.event.pull_request.head.repo.full_name == null || github.event.pull_request.head.repo.full_name == github.repository) && fromJSON('["self-hosted","coursia-waiter"]') || 'ubuntu-latest' }}
            steps:
              - run: echo aggregate
        """)
    result = policy.scan_workflows(tmp_path)
    assert codes(result) == {"DYNAMIC_RUNS_ON"}


def test_hybrid_runs_on_in_non_allowlisted_workflow_is_rejected(tmp_path):
    write_workflow(tmp_path, "other-aggregator", """
        name: other
        on: workflow_dispatch
        jobs:
          gate:
            runs-on: RUNSON
            steps:
              - run: echo aggregate
        """)
    (tmp_path / "other-aggregator.yml").write_text(
        (tmp_path / "other-aggregator.yml").read_text(encoding="utf-8").replace(
            "RUNSON", HYBRID_RUNS_ON
        ),
        encoding="utf-8",
    )
    result = policy.scan_workflows(tmp_path)
    assert codes(result) == {"WORKFLOW_NOT_ALLOWED"}


def test_hybrid_runs_on_pull_request_target_is_rejected(tmp_path):
    write_workflow(tmp_path, "pr-gate", """
        name: PR gate
        on: [pull_request_target]
        jobs:
          gate:
            runs-on: RUNSON
            steps:
              - run: echo aggregate
        """)
    (tmp_path / "pr-gate.yml").write_text(
        (tmp_path / "pr-gate.yml").read_text(encoding="utf-8").replace(
            "RUNSON", HYBRID_RUNS_ON
        ),
        encoding="utf-8",
    )
    result = policy.scan_workflows(tmp_path)
    assert "PULL_REQUEST_TARGET" in codes(result)


# c.509 (dispatch c.2180) : the audited hybrid form now also accepts the
# Linux runner label set [self-hosted, coursia-ephemeral, coursia-linux].
# The same-repo guard, the ubuntu-latest fallback and the trigger policy
# are reused -- only the label set widens.
HYBRID_RUNS_ON_LINUX = (
    "${{ (github.event.pull_request.head.repo.full_name == github.repository)"
    " && fromJSON('[\"self-hosted\",\"coursia-ephemeral\",\"coursia-linux\"]') "
    "|| 'ubuntu-latest' }}"
)


def test_hybrid_runs_on_linux_form_is_accepted(tmp_path):
    """c.509 : the LINUX_RUNNER_LABELS triplet is the second audited
    dynamic form, alongside the WAITER_LABELS form. A pure-Python guard
    (no kernel, no GPU, no docker) routed to the containerized Linux leg
    goes through the same-repo guard the same way pr-gate.yml does.

    The carrier workflow is allowlisted (always-on-metadata-guards.yml
    is the twin of always-on-guards.yml, both on main). The audit gates
    the form AND the carrier -- widening the audited label set is not
    enough to widen the allowlist; that is tested separately by
    test_hybrid_runs_on_linux_in_non_allowlisted_workflow_is_rejected."""
    write_workflow(tmp_path, "always-on-metadata-guards", """
        name: always-on-metadata-guards
        on:
          pull_request:
            branches: [main]
          workflow_dispatch:
        jobs:
          guard:
            name: kernel-drift-guard
            runs-on: RUNSON
            steps:
              - run: echo pure-python
        """)
    (tmp_path / "always-on-metadata-guards.yml").write_text(
        (tmp_path / "always-on-metadata-guards.yml").read_text(
            encoding="utf-8"
        ).replace("RUNSON", HYBRID_RUNS_ON_LINUX),
        encoding="utf-8",
    )
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert result.violations == []
    assert result.self_hosted_jobs == 1


def test_hybrid_runs_on_linux_wrong_labels_is_rejected(tmp_path):
    """Negative control : swapping any label in the LINUX trio
    (dropping coursia-ephemeral, swapping coursia-linux for coursia-waiter,
    adding a fourth label) keeps the DYNAMIC_RUNS_ON rejection -- the
    audited set is a TUPLE of exact sets, not a prefix/super-set check."""
    write_workflow(tmp_path, "kernel-drift-canonical-env-hint", """
        name: kernel-drift
        on: workflow_dispatch
        jobs:
          guard:
            runs-on: ${{ (github.event.pull_request.head.repo.full_name == github.repository) && fromJSON('["self-hosted","coursia-linux"]') || 'ubuntu-latest' }}
            steps:
              - run: echo partial
        """)
    result = policy.scan_workflows(tmp_path)
    assert codes(result) == {"DYNAMIC_RUNS_ON"}
    assert result.self_hosted_jobs == 0


def test_hybrid_runs_on_linux_swap_to_lean_is_rejected(tmp_path):
    """Negative control : the LEAN set shares coursia-ephemeral but
    lands on a different image (elan + toolchain baked). The
    LINUX_RUNNER_LABELS form must not accept a swap to coursia-lean --
    routing a pure-Python guard to a lean slot would star a Lean build
    behind a 10-second scan."""
    write_workflow(tmp_path, "kernel-drift-canonical-env-hint", """
        name: kernel-drift
        on: workflow_dispatch
        jobs:
          guard:
            runs-on: ${{ (github.event.pull_request.head.repo.full_name == github.repository) && fromJSON('["self-hosted","coursia-ephemeral","coursia-lean"]') || 'ubuntu-latest' }}
            steps:
              - run: echo swap
        """)
    result = policy.scan_workflows(tmp_path)
    assert codes(result) == {"DYNAMIC_RUNS_ON"}
    assert result.self_hosted_jobs == 0


def test_hybrid_runs_on_linux_in_non_allowlisted_workflow_is_rejected(tmp_path):
    """Positive form, wrong workflow : the same hybrid Linux form inside
    a workflow that is not on the SELF_HOSTED_WORKFLOW_ALLOWLIST is
    rejected with WORKFLOW_NOT_ALLOWED. The audit gates the form AND
    the carrier -- widening one does not widen the other."""
    write_workflow(tmp_path, "ad-hoc-guard", """
        name: ad-hoc
        on:
          pull_request:
            branches: [main]
          workflow_dispatch:
        jobs:
          guard:
            runs-on: RUNSON
            steps:
              - run: echo unlisted
        """)
    (tmp_path / "ad-hoc-guard.yml").write_text(
        (tmp_path / "ad-hoc-guard.yml").read_text(encoding="utf-8").replace(
            "RUNSON", HYBRID_RUNS_ON_LINUX
        ),
        encoding="utf-8",
    )
    result = policy.scan_workflows(tmp_path)
    assert codes(result) == {"WORKFLOW_NOT_ALLOWED"}


def test_hybrid_runs_on_linux_wrong_fallback_is_rejected(tmp_path):
    """Same fallback rule as the waiter form : the github-hosted
    fallback must be the exact string 'ubuntu-latest'. A version pin
    (ubuntu-24.04) or a windows runner (windows-latest) keeps the
    DYNAMIC_RUNS_ON rejection -- only the exact literal is audited."""
    write_workflow(tmp_path, "kernel-drift-canonical-env-hint", """
        name: kernel-drift
        on: workflow_dispatch
        jobs:
          guard:
            runs-on: ${{ (github.event.pull_request.head.repo.full_name == github.repository) && fromJSON('["self-hosted","coursia-ephemeral","coursia-linux"]') || 'ubuntu-24.04' }}
            steps:
              - run: echo bad-fallback
        """)
    result = policy.scan_workflows(tmp_path)
    assert codes(result) == {"DYNAMIC_RUNS_ON"}


# #22461 (dispatch ai-01 2026-10-27) : seconde garde enumeree de la forme
# hybride -- la garde meme-depot conjoine a la variable de debordement
# vars.CI_OVERFLOW_LOCAL == 'true'. Le nom de la variable et sa valeur sont
# ENUMERES : le pool local ne recoit le job que si un operateur a bascule
# la variable de depot (phase A) ; hors bascule (variable absente, fausse,
# renommee, ou `||` de contournement) la forme n'est pas auditee.
HYBRID_RUNS_ON_OVERFLOW = (
    "${{ (github.event.pull_request.head.repo.full_name == github.repository"
    " && vars.CI_OVERFLOW_LOCAL == 'true')"
    " && fromJSON('[\"self-hosted\",\"coursia-ephemeral\",\"coursia-linux\"]') "
    "|| 'ubuntu-latest' }}"
)


def test_hybrid_runs_on_overflow_form_is_accepted(tmp_path):
    """#22461 : la garde overflow (meme-depot && vars.CI_OVERFLOW_LOCAL ==
    'true') est la seconde forme hybride auditee -- labels LINUX uniquement,
    repli ubuntu-latest. Porteur reel : les jobs deports par #22820/#22821/
    #22822 (ici always-on-guards.yml, allowliste)."""
    write_workflow(tmp_path, "always-on-guards", """
        name: always-on-guards
        on:
          pull_request:
            branches: [main]
          workflow_dispatch:
        jobs:
          always-on-guards:
            name: "Always-on guards"
            runs-on: RUNSON
            steps:
              - run: echo overflow
        """)
    (tmp_path / "always-on-guards.yml").write_text(
        (tmp_path / "always-on-guards.yml").read_text(encoding="utf-8").replace(
            "RUNSON", HYBRID_RUNS_ON_OVERFLOW
        ),
        encoding="utf-8",
    )
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert result.violations == []
    assert result.self_hosted_jobs == 1


def test_hybrid_runs_on_overflow_renamed_variable_is_rejected(tmp_path):
    """#22461 : le NOM de la variable est enumere. CI_OVERFLOW_LOCAL_2 ou
    CI_OVERFLOW seul -> la garde n'est pas celle auditee, DYNAMIC_RUNS_ON
    (fail-closed : une variable renommee serait une bascule invisible pour
    l'audit)."""
    for name, variable in (
        ("renamed-suffix", "CI_OVERFLOW_LOCAL_2"),
        ("renamed-prefix", "CI_OVERFLOW"),
    ):
        write_workflow(tmp_path, name, f"""
            name: {name}
            on:
              pull_request:
                branches: [main]
              workflow_dispatch:
            jobs:
              guard:
                runs-on: ${{{{ (github.event.pull_request.head.repo.full_name == github.repository && vars.{variable} == 'true') && fromJSON('["self-hosted","coursia-ephemeral","coursia-linux"]') || 'ubuntu-latest' }}}}
                steps:
                  - run: echo renamed
            """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert codes(result) == {"DYNAMIC_RUNS_ON"}
    assert len(result.violations) == 2


def test_hybrid_runs_on_overflow_without_same_repo_guard_is_rejected(tmp_path):
    """#22461 : la clause meme-depot est INTEGREE a la garde enumeree. La
    variable seule (vars.CI_OVERFLOW_LOCAL == 'true') sans le test du repo
    source -> refusee : un fork avec la variable basculee atteindrait le
    pool local sans garde anti-fork."""
    write_workflow(tmp_path, "var-only", """
        name: var-only
        on:
          pull_request:
            branches: [main]
          workflow_dispatch:
        jobs:
          guard:
            runs-on: ${{ (vars.CI_OVERFLOW_LOCAL == 'true') && fromJSON('["self-hosted","coursia-ephemeral","coursia-linux"]') || 'ubuntu-latest' }}
            steps:
              - run: echo unguarded
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert codes(result) == {"DYNAMIC_RUNS_ON"}
    assert result.self_hosted_jobs == 0


def test_hybrid_runs_on_overflow_bypassed_by_or_is_rejected(tmp_path):
    """#22461 : aucun `||` ne peut court-circuiter la garde. Deux variantes
    refusees : (a) `|| true` en fin de garde -- toujours vrai, la garde
    meme-depot ne filtre plus rien ; (b) `||` deplace -- la disjunction
    meme-depot || variable rend la variable suffisante SANS le test du repo
    source. Les deux restent DYNAMIC_RUNS_ON."""
    write_workflow(tmp_path, "or-true", """
        name: or-true
        on:
          pull_request:
            branches: [main]
          workflow_dispatch:
        jobs:
          guard:
            runs-on: ${{ (github.event.pull_request.head.repo.full_name == github.repository && vars.CI_OVERFLOW_LOCAL == 'true' || true) && fromJSON('["self-hosted","coursia-ephemeral","coursia-linux"]') || 'ubuntu-latest' }}
            steps:
              - run: echo bypass
        """)
    write_workflow(tmp_path, "or-displaced", """
        name: or-displaced
        on:
          pull_request:
            branches: [main]
          workflow_dispatch:
        jobs:
          guard:
            runs-on: ${{ (github.event.pull_request.head.repo.full_name == github.repository || vars.CI_OVERFLOW_LOCAL == 'true') && fromJSON('["self-hosted","coursia-ephemeral","coursia-linux"]') || 'ubuntu-latest' }}
            steps:
              - run: echo displaced
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert codes(result) == {"DYNAMIC_RUNS_ON"}
    assert len(result.violations) == 2


def test_hybrid_runs_on_overflow_admits_only_linux_labels(tmp_path):
    """#22461 : la garde overflow n'admet QUE LINUX_RUNNER_LABELS -- le trio
    waiter sous cette garde est refuse (le debordement vise le pool Linux
    containerise, pas les 16 slots d'attente du PR gate)."""
    write_workflow(tmp_path, "overflow-waiter", """
        name: overflow-waiter
        on:
          pull_request:
            branches: [main]
          workflow_dispatch:
        jobs:
          guard:
            runs-on: ${{ (github.event.pull_request.head.repo.full_name == github.repository && vars.CI_OVERFLOW_LOCAL == 'true') && fromJSON('["self-hosted","coursia-waiter"]') || 'ubuntu-latest' }}
            steps:
              - run: echo wrong-pool
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert codes(result) == {"DYNAMIC_RUNS_ON"}
    assert result.self_hosted_jobs == 0


def test_overflow_guard_does_not_narrow_existing_hybrid_forms(tmp_path):
    """#22461 non-regression : la garde d'origine (#13363) garde SES deux
    pools -- la forme waiter (pr-gate.yml) et la forme linux sous garde
    simple restent acceptees a l'identique. Ajouter la garde overflow ne
    retrecit rien de ce qui etait admis avant."""
    for carrier, runs_on in (
        ("pr-gate", HYBRID_RUNS_ON),
        ("always-on-metadata-guards", HYBRID_RUNS_ON_LINUX),
    ):
        write_workflow(tmp_path, carrier, f"""
            name: {carrier}
            on:
              pull_request:
                branches: [main]
              workflow_dispatch:
            jobs:
              guard:
                runs-on: RUNSON
                steps:
                  - run: echo legacy
            """)
        (tmp_path / f"{carrier}.yml").write_text(
            (tmp_path / f"{carrier}.yml").read_text(encoding="utf-8").replace(
                "RUNSON", runs_on
            ),
            encoding="utf-8",
        )
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert result.violations == []
    assert result.self_hosted_jobs == 2


def test_pull_request_job_without_guard_is_rejected(tmp_path):
    write_workflow(tmp_path, "unguarded", """
        name: unguarded
        on:
          pull_request:
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo unsafe
        """)
    assert "SAME_REPO_GUARD" in codes(policy.scan_workflows(tmp_path))


def test_step_level_guard_does_not_protect_the_job(tmp_path):
    write_workflow(tmp_path, "step-guard", """
        name: step-guard
        on: [pull_request]
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - if: ${{ github.event.pull_request.head.repo.full_name == github.repository }}
                run: echo too-late
        """)
    assert "SAME_REPO_GUARD" in codes(policy.scan_workflows(tmp_path))


def test_guard_weakened_by_or_is_rejected(tmp_path):
    write_workflow(tmp_path, "weak", """
        name: weak
        on: [pull_request]
        jobs:
          test:
            if: ${{ github.event.pull_request.head.repo.full_name == github.repository || always() }}
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo unsafe
        """)
    assert "SAME_REPO_GUARD" in codes(policy.scan_workflows(tmp_path))


def test_pull_request_target_is_always_rejected(tmp_path):
    write_workflow(tmp_path, "target", """
        name: target
        on: [pull_request_target]
        jobs:
          test:
            if: ${{ github.event.pull_request.head.repo.full_name == github.repository }}
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo unsafe
        """)
    assert "PULL_REQUEST_TARGET" in codes(policy.scan_workflows(tmp_path))


def test_workflow_call_cannot_hide_self_hosted_job(tmp_path):
    write_workflow(tmp_path, "callee", """
        name: callee
        on: workflow_call
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo hidden
        """)
    result = policy.scan_workflows(tmp_path)
    assert "REUSABLE_SELF_HOSTED" in codes(result)


def test_workflow_run_cannot_reach_self_hosted_job(tmp_path):
    write_workflow(tmp_path, "artifact", """
        name: artifact
        on:
          workflow_run:
            workflows: [Build]
            types: [completed]
        jobs:
          test:
            runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
            steps:
              - run: echo artifact
        """)
    assert "WORKFLOW_RUN" in codes(policy.scan_workflows(tmp_path))


def test_external_reusable_workflow_is_rejected(tmp_path):
    write_workflow(tmp_path, "caller", """
        name: caller
        on: [pull_request]
        jobs:
          test:
            uses: attacker/repo/.github/workflows/run.yml@main
        """)
    assert "REMOTE_REUSABLE_WORKFLOW" in codes(policy.scan_workflows(tmp_path))


def test_local_reusable_workflow_remains_auditable(tmp_path):
    write_workflow(tmp_path, "caller", """
        name: caller
        on: [pull_request]
        jobs:
          test:
            uses: ./.github/workflows/callee.yml
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert result.violations == []


def test_same_repository_reusable_workflow_allows_main(tmp_path):
    write_workflow(tmp_path, "caller", """
        name: caller
        on: [pull_request]
        jobs:
          test:
            uses: jsboige/CoursIA/.github/workflows/callee.yml@main
        """)
    assert policy.scan_workflows(tmp_path).violations == []


def test_same_repository_reusable_workflow_rejects_commit_sha(tmp_path):
    sha = "0123456789abcdef0123456789abcdef01234567"
    write_workflow(tmp_path, "caller", f"""
        name: caller
        on: [pull_request]
        jobs:
          test:
            uses: jsboige/CoursIA/.github/workflows/callee.yml@{sha}
        """)
    assert "REMOTE_REUSABLE_WORKFLOW" in codes(policy.scan_workflows(tmp_path))


def test_same_repository_reusable_workflow_rejects_branch_ref(tmp_path):
    write_workflow(tmp_path, "caller", """
        name: caller
        on: [pull_request]
        jobs:
          test:
            uses: jsboige/CoursIA/.github/workflows/callee.yml@feature/unsafe
        """)
    assert "REMOTE_REUSABLE_WORKFLOW" in codes(policy.scan_workflows(tmp_path))


def test_same_repository_reusable_workflow_rejects_short_sha(tmp_path):
    write_workflow(tmp_path, "caller", """
        name: caller
        on: [pull_request]
        jobs:
          test:
            uses: jsboige/CoursIA/.github/workflows/callee.yml@0123456789abcdef
        """)
    assert "REMOTE_REUSABLE_WORKFLOW" in codes(policy.scan_workflows(tmp_path))


def test_missing_trigger_breaks_instrument(tmp_path):
    write_workflow(tmp_path, "broken-trigger", """
        name: broken-trigger
        jobs:
          test:
            runs-on: ubuntu-latest
            steps:
              - run: echo no-trigger
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == ["broken-trigger.yml: missing on trigger"]


def test_empty_runs_on_list_breaks_instrument(tmp_path):
    write_workflow(tmp_path, "broken-runner", """
        name: broken-runner
        on: workflow_dispatch
        jobs:
          test:
            runs-on: []
            steps:
              - run: echo no-runner
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == [
        "broken-runner.yml:test: runs-on list must contain labels"
    ]


def test_missing_jobs_breaks_instrument(tmp_path):
    write_workflow(tmp_path, "broken-jobs", """
        name: broken-jobs
        on: workflow_dispatch
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == ["broken-jobs.yml: missing jobs"]


def test_same_repository_reusable_workflow_rejects_path_traversal(tmp_path):
    write_workflow(tmp_path, "caller", """
        name: caller
        on: [pull_request]
        jobs:
          test:
            uses: jsboige/CoursIA/.github/workflows/../evil.yml@main
        """)
    assert "REMOTE_REUSABLE_WORKFLOW" in codes(policy.scan_workflows(tmp_path))


def test_invalid_yaml_breaks_the_instrument(tmp_path):
    write_workflow(tmp_path, "broken", "on: [pull_request\njobs: [")
    result = policy.scan_workflows(tmp_path)
    assert result.broken
    assert policy.main(["--check", "--workflows-dir", str(tmp_path)]) == policy.EXIT_BROKEN


def test_json_output_names_violations_and_denominators(tmp_path, capsys):
    write_workflow(tmp_path, "unsafe", """
        name: unsafe
        on: workflow_dispatch
        jobs:
          test:
            runs-on: self-hosted
            steps:
              - run: echo unsafe
        """)
    rc = policy.main(["--json", "--workflows-dir", str(tmp_path)])
    payload = json.loads(capsys.readouterr().out)
    assert rc == policy.EXIT_VIOLATION
    assert payload["workflows_scanned"] == 1
    assert payload["jobs_scanned"] == 1
    assert payload["self_hosted_jobs"] == 1
    assert {item["code"] for item in payload["violations"]} == {
        "WORKFLOW_NOT_ALLOWED",
        "RUNNER_LABELS",
    }


def test_missing_runs_on_breaks_instrument_instead_of_silent_skip(tmp_path):
    write_workflow(tmp_path, "broken-job", """
        name: broken-job
        on: workflow_dispatch
        jobs:
          test:
            steps:
              - run: echo no-runner
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == ["broken-job.yml:test: missing runs-on"]


# -- #22954 : cliquet `timeout-minutes` sur les jobs auto-heberges -----------
# Un job qui peut atteindre un runner auto-heberge sans borne au niveau du job
# peut tenir son slot six heures (defaut d'Actions) s'il fige ; le slot manque
# alors aux PR gates. Mesure du 2026-10-29 sur `origin/main` 2f1291f01 : 138
# jobs auto-heberges, 75 sans borne -- 12 hybrides et 63 statiques. La PR qui a
# introduit le cliquet borne les 12 ; les 63 restants vivent dans la baseline
# `scripts/ci/self_hosted_timeout_baseline.txt`, qui ne doit JAMAIS grossir.


def _hybrid_workflow(tmp_path: Path, timeout_minutes: int | None = None) -> Path:
    """Un workflow synthetique a un job hybride, avec ou sans borne #22954."""
    bound = "" if timeout_minutes is None else f"\n            timeout-minutes: {timeout_minutes}"
    body = f"""
        name: always-on-guards
        on:
          pull_request:
            branches: [main]
          workflow_dispatch:
        jobs:
          overflow:
            name: "Overflow"{bound}
            runs-on: {HYBRID_RUNS_ON_OVERFLOW}
            steps:
              - run: echo overflow
        """
    return write_workflow(tmp_path, "always-on-guards", body)


def test_22954_hybrid_job_without_timeout_is_reported(tmp_path):
    """#22954 : la forme hybride sans borne est refusee, sans aucune tolerance.

    Controle POSITIF du cliquet : la meme forme que
    `test_hybrid_runs_on_overflow_form_is_accepted`, a qui l'on retire la seule
    borne `timeout-minutes`.
    """
    _hybrid_workflow(tmp_path)
    result = policy.scan_workflows(tmp_path, check_timeouts=True, baseline=set())
    assert result.broken == []
    assert codes(result) == {"MISSING_TIMEOUT"}
    assert result.self_hosted_jobs == 1
    assert result.timeout_missing == 1
    assert result.timeout_baselined == 0
    assert policy.main(["--check", "--check-timeouts",
                        "--workflows-dir", str(tmp_path),
                        "--baseline", str(tmp_path / "absent.txt")]) == policy.EXIT_VIOLATION


def test_22954_hybrid_job_with_timeout_is_accepted(tmp_path):
    """#22954 : controle NEGATIF -- la borne au niveau du job suffit."""
    _hybrid_workflow(tmp_path, timeout_minutes=10)
    result = policy.scan_workflows(tmp_path, check_timeouts=True, baseline=set())
    assert result.broken == []
    assert result.violations == []
    assert result.timeouts_checked is True
    assert result.timeout_missing == 0


def test_22954_baselined_job_is_tolerated_but_named_in_the_report(tmp_path):
    """#22954 : la dette nommee passe, et le rapport dit combien elle pese.

    Une ligne de baseline est une date, pas un blanc-seing : le compte
    `timeout_baselined` doit rester visible pour que la dette ne disparaisse
    pas du rapport.
    """
    _hybrid_workflow(tmp_path)
    baseline = {"always-on-guards.yml:overflow"}
    result = policy.scan_workflows(tmp_path, check_timeouts=True, baseline=baseline)
    assert result.violations == []
    assert result.timeout_missing == 1
    assert result.timeout_baselined == 1


def test_22954_ratchet_is_opt_in_so_synthetic_workflows_stay_single_purpose(tmp_path):
    """#22954 : sans le drapeau, le cliquet ne parle pas.

    Les tests de ce fichier construisent des workflows synthetiques pour
    eprouver UN invariant a la fois (garde meme-depot, jeu de labels, ...). Le
    cliquet est donc opt-in cote API, et engage cote garde bloquant : c'est
    `scripts/ci/fast_lane_registry.py` qui passe le drapeau, et le test suivant
    l'y verifie.
    """
    _hybrid_workflow(tmp_path)
    result = policy.scan_workflows(tmp_path)
    assert result.violations == []
    assert result.timeouts_checked is False


def test_22954_repository_passes_the_ratchet_with_zero_new_jobs():
    """#22954 : `main` passe le cliquet -- 0 nouveau, la dette en baseline."""
    result = policy.scan_workflows(check_timeouts=True)
    assert result.broken == []
    assert [v for v in result.violations if v.code == "MISSING_TIMEOUT"] == []
    assert result.timeouts_checked is True
    assert policy.main(["--check", "--check-timeouts"]) == policy.EXIT_OK


def test_22954_fast_lane_entry_actually_enforces_the_ratchet():
    """#22954 : le garde BLOQUANT passe le drapeau, et surveille sa baseline.

    Un cliquet opt-in ne vaut que si l'appel bloquant passe le drapeau. Ce test
    est le garde du garde : retirer `--check-timeouts` de l'entree fast-lane, ou
    oublier la baseline dans ses `paths`, rougit ici au lieu de desactiver le
    cliquet en silence.
    """
    import fast_lane_registry as registry

    # Le lot d'accueil d'un garde peut changer au fil des tranches : on cherche
    # dans TOUTE liste de `Guard` du module, pas dans un lot nomme.
    entries = [
        guard
        for value in vars(registry).values()
        if isinstance(value, list)
        for guard in value
        if isinstance(guard, registry.Guard)
        and guard.name == "self-hosted-runner-policy"
    ]
    assert len(entries) == 1, (
        f"attendu exactement une entree fast-lane 'self-hosted-runner-policy', "
        f"trouve {len(entries)}"
    )
    entry = entries[0]
    assert "--check-timeouts" in entry.argv, (
        "l'entree fast-lane doit passer --check-timeouts : sans le drapeau, "
        "MISSING_TIMEOUT n'est jamais evalue (#22954)"
    )
    assert entry.blocking is True
    assert "scripts/ci/self_hosted_timeout_baseline.txt" in entry.paths, (
        "la baseline doit etre dans les paths du garde : sinon une PR qui la "
        "reecrit ne relance pas le cliquet (#22954)"
    )


# #13960 : garde anti-regression sur les doublons de def dans ce fichier.
# Le defaut fondateur (mesure 2026-09-01) : 4 paires byte-identiques
# (`test_missing_trigger_breaks_instrument`, `test_empty_runs_on_list_breaks_instrument`,
# `test_missing_jobs_breaks_instrument`, `test_same_repository_reusable_workflow_rejects_path_traversal`).
# La 2e definition eclipsait la 1re -- couverture neutre mais piege a evolution
# (si une copie evolue, la version executee n'est plus celle visible dans l'editeur).
# Detecte au niveau AST tout doublon de fonction au top-level : aucun nom ne
# doit apparaitre 2 fois comme def dans ce fichier. Si une re-introduction se
# produit (par copier-coller, refactor futur, fusion accidentelle), ce test
# rougit avec le nom et le compte.
def test_13960_no_duplicate_test_function_definitions() -> None:
    """#13960 : garde anti-regression doublons de def au top-level."""
    import ast
    import pathlib
    source = pathlib.Path(__file__).read_text(encoding="utf-8")
    tree = ast.parse(source)
    seen: dict[str, int] = {}
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            seen[node.name] = seen.get(node.name, 0) + 1
    duplicates = {name: count for name, count in seen.items() if count > 1}
    assert not duplicates, (
        f"doublons de def au top-level : {duplicates} "
        f"(cf #13960 fondateur : la 2e def eclipse la 1re silencieusement)"
    )
