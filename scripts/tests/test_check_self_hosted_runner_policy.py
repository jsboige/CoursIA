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


def test_current_repository_has_explicit_zero_self_hosted_baseline(capsys):
    result = policy.scan_workflows()
    assert result.broken == []
    assert result.violations == []
    assert result.self_hosted_jobs == 0
    assert result.workflows_scanned > 0
    assert policy.main(["--check"]) == policy.EXIT_OK
    assert "explicit baseline: 0 self-hosted jobs" in capsys.readouterr().out


def test_safe_pull_request_job_is_accepted(tmp_path):
    write_workflow(tmp_path, "safe", """
        name: safe
        on: [pull_request]
        jobs:
          test:
            if: ${{ github.event.pull_request.head.repo.full_name == github.repository }}
            runs-on:
              group: coursia-ephemeral
              labels: [self-hosted, coursia-ephemeral]
            steps:
              - run: echo safe
        """)
    result = policy.scan_workflows(tmp_path)
    assert result.broken == []
    assert result.violations == []
    assert result.self_hosted_jobs == 1


def test_safe_workflow_dispatch_job_does_not_need_pr_guard(tmp_path):
    write_workflow(tmp_path, "manual", """
        name: manual
        on: workflow_dispatch
        jobs:
          test:
            runs-on:
              group: coursia-ephemeral
              labels: [self-hosted, coursia-ephemeral]
            steps:
              - run: echo safe
        """, suffix=".yaml")
    result = policy.scan_workflows(tmp_path)
    assert result.violations == []
    assert result.self_hosted_jobs == 1


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
    assert {"RUNNER_GROUP", "RUNNER_LABELS", "SAME_REPO_GUARD"} <= codes(result)


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
    assert "RUNNER_GROUP" in codes(policy.scan_workflows(tmp_path))


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
    assert {"RUNNER_GROUP", "RUNNER_LABELS"} == codes(result)


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
    assert codes(result) == {"RUNNER_LABELS"}


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
    assert "RUNNER_GROUP" in codes(result)


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
    assert {"RUNNER_GROUP", "RUNNER_LABELS"} == codes(result)


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


def test_pull_request_job_without_guard_is_rejected(tmp_path):
    write_workflow(tmp_path, "unguarded", """
        name: unguarded
        on:
          pull_request:
        jobs:
          test:
            runs-on:
              group: coursia-ephemeral
              labels: [self-hosted, coursia-ephemeral]
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
            runs-on:
              group: coursia-ephemeral
              labels: [self-hosted, coursia-ephemeral]
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
            runs-on:
              group: coursia-ephemeral
              labels: [self-hosted, coursia-ephemeral]
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
            runs-on:
              group: coursia-ephemeral
              labels: [self-hosted, coursia-ephemeral]
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
            runs-on:
              group: coursia-ephemeral
              labels: [self-hosted, coursia-ephemeral]
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
            runs-on:
              group: coursia-ephemeral
              labels: [self-hosted, coursia-ephemeral]
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


def test_same_repository_reusable_workflow_remains_auditable(tmp_path):
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
        "RUNNER_GROUP",
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
