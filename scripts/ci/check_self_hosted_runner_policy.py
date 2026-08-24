#!/usr/bin/env python3
"""Enforce the isolation policy for future self-hosted Actions jobs (#12704).

The repository is public. A self-hosted job that can receive a fork payload can
execute untrusted code next to the cluster's credentials. This scanner therefore
fails closed: every self-hosted job must use the dedicated runner group and
label, and every pull_request job must carry the exact same-repository guard.
Dynamic ``runs-on`` expressions are rejected because their target cannot be
proved statically.

Exit codes:
  0  policy satisfied (including the explicit baseline of zero self-hosted jobs)
  1  policy violation
  2  broken instrument or unreadable workflow
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

EXIT_OK = 0
EXIT_VIOLATION = 1
EXIT_BROKEN = 2

REQUIRED_GROUP = "coursia-ephemeral"
REQUIRED_LABELS = {"self-hosted", "coursia-ephemeral"}
GITHUB_HOSTED_LABELS = {
    "ubuntu-latest",
    "ubuntu-24.04",
    "ubuntu-22.04",
    "ubuntu-20.04",
    "ubuntu-slim",
    "windows-latest",
    "windows-2025",
    "windows-2022",
    "windows-2019",
    "macos-latest",
    "macos-26",
    "macos-15",
    "macos-14",
    "macos-13",
}
LOCAL_REUSABLE_PREFIX = "./.github/workflows/"
SAME_REPO_REUSABLE_PATTERN = re.compile(
    r"^jsboige/CoursIA/\.github/workflows/[^@]+@(?:main|[0-9a-fA-F]{40})$"
)
SAME_REPO_GUARD = (
    "github.event.pull_request.head.repo.full_name == github.repository"
)
DEFAULT_WORKFLOWS_DIR = Path(__file__).resolve().parents[2] / ".github" / "workflows"


@dataclass(frozen=True)
class Violation:
    workflow: str
    job: str
    code: str
    message: str


@dataclass(frozen=True)
class ScanResult:
    workflows_scanned: int
    jobs_scanned: int
    self_hosted_jobs: int
    violations: list[Violation]
    broken: list[str]


def _load_yaml():
    try:
        import yaml
    except ImportError:
        return None
    return yaml


def _parse_workflow(text: str, yaml: Any) -> dict[str, Any] | None:
    """Parse Actions YAML while preserving the top-level ``on`` key."""
    lines: list[str] = []
    for line in text.splitlines():
        if line.startswith("on:") and (
            len(line) == 3 or line[3] in (" ", "[", "\t")
        ):
            lines.append('"on":' + line[3:])
        else:
            lines.append(line)
    try:
        data = yaml.safe_load("\n".join(lines))
    except yaml.YAMLError:
        return None
    return data if isinstance(data, dict) else None


def _triggers(data: dict[str, Any]) -> set[str]:
    value = data.get("on", data.get(True))
    if isinstance(value, dict):
        return {str(item) for item in value}
    if isinstance(value, list):
        return {str(item) for item in value}
    if isinstance(value, str):
        return {value}
    return set()


def _contains_expression(value: Any) -> bool:
    if isinstance(value, str):
        return "${{" in value
    if isinstance(value, list):
        return any(_contains_expression(item) for item in value)
    if isinstance(value, dict):
        return any(
            _contains_expression(key) or _contains_expression(item)
            for key, item in value.items()
        )
    return False


def _is_github_hosted_label(label: str) -> bool:
    return label.lower() in GITHUB_HOSTED_LABELS


def _runner_selection(runs_on: Any) -> tuple[bool, str | None, set[str]]:
    """Return (is_self_hosted, group, labels) for a static selection.

    Any explicit runner group is self-hosted. A scalar/list label is considered
    GitHub-hosted only when every value names a documented hosted-image family;
    custom labels route to self-hosted runners even when the implicit
    ``self-hosted`` label is omitted from the workflow.
    """
    if isinstance(runs_on, str):
        labels = {runs_on.lower()}
        return not _is_github_hosted_label(runs_on), None, labels
    if isinstance(runs_on, list):
        labels = {str(item).lower() for item in runs_on}
        is_self_hosted = any(not _is_github_hosted_label(item) for item in labels)
        return is_self_hosted, None, labels
    if isinstance(runs_on, dict):
        group = runs_on.get("group")
        raw_labels = runs_on.get("labels", [])
        if isinstance(raw_labels, str):
            labels = {raw_labels.lower()}
        elif isinstance(raw_labels, list):
            labels = {str(item).lower() for item in raw_labels}
        else:
            labels = set()
        is_self_hosted = group is not None or any(
            not _is_github_hosted_label(item) for item in labels
        )
        return is_self_hosted, str(group) if group is not None else None, labels
    return False, None, set()


def _normalise_condition(value: Any) -> str:
    if not isinstance(value, str):
        return ""
    condition = value.strip()
    if condition.startswith("${{") and condition.endswith("}}"):
        condition = condition[3:-2].strip()
    return " ".join(condition.split())


def scan_workflows(workflows_dir: Path = DEFAULT_WORKFLOWS_DIR) -> ScanResult:
    yaml = _load_yaml()
    if yaml is None:
        return ScanResult(0, 0, 0, [], ["PyYAML is unavailable"])

    paths = sorted([*workflows_dir.glob("*.yml"), *workflows_dir.glob("*.yaml")])
    if not paths:
        return ScanResult(0, 0, 0, [], [f"no workflows in {workflows_dir}"])

    violations: list[Violation] = []
    broken: list[str] = []
    jobs_scanned = 0
    self_hosted_jobs = 0

    for path in paths:
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as exc:
            broken.append(f"{path.name}: cannot read: {exc}")
            continue
        data = _parse_workflow(text, yaml)
        if data is None:
            broken.append(f"{path.name}: invalid workflow YAML")
            continue

        triggers = _triggers(data)
        jobs = data.get("jobs", {})
        if not isinstance(jobs, dict):
            broken.append(f"{path.name}: jobs is not a mapping")
            continue

        for job_name, job in jobs.items():
            if not isinstance(job, dict):
                broken.append(f"{path.name}:{job_name}: job is not a mapping")
                continue
            jobs_scanned += 1

            if "uses" in job:
                reusable = str(job["uses"])
                is_local = reusable.startswith(LOCAL_REUSABLE_PREFIX)
                is_auditable_same_repo = bool(
                    SAME_REPO_REUSABLE_PATTERN.fullmatch(reusable)
                )
                if not is_local and not is_auditable_same_repo:
                    violations.append(Violation(
                        path.name,
                        str(job_name),
                        "REMOTE_REUSABLE_WORKFLOW",
                        "reusable workflow must be local or pin jsboige/CoursIA "
                        "to main or a 40-character commit SHA",
                    ))
                continue

            runs_on = job.get("runs-on")
            if runs_on is None:
                broken.append(f"{path.name}:{job_name}: missing runs-on")
                continue

            if _contains_expression(runs_on):
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "DYNAMIC_RUNS_ON",
                    "runs-on contains an expression and cannot be audited statically",
                ))
                continue

            is_self_hosted, group, labels = _runner_selection(runs_on)
            if not is_self_hosted:
                continue
            self_hosted_jobs += 1

            if "pull_request_target" in triggers:
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "PULL_REQUEST_TARGET",
                    "pull_request_target must never reach a self-hosted runner",
                ))
            if "workflow_run" in triggers:
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "WORKFLOW_RUN",
                    "workflow_run artifacts must never reach a self-hosted runner",
                ))
            if "workflow_call" in triggers:
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "REUSABLE_SELF_HOSTED",
                    "self-hosted jobs must not hide inside reusable workflows",
                ))

            if group != REQUIRED_GROUP:
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "RUNNER_GROUP",
                    f"runner group must be {REQUIRED_GROUP!r}, got {group!r}",
                ))

            missing = sorted(REQUIRED_LABELS - labels)
            if missing:
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "RUNNER_LABELS",
                    f"missing dedicated labels: {', '.join(missing)}",
                ))

            if "pull_request" in triggers:
                condition = _normalise_condition(job.get("if"))
                if condition != SAME_REPO_GUARD:
                    violations.append(Violation(
                        path.name,
                        str(job_name),
                        "SAME_REPO_GUARD",
                        "pull_request self-hosted job must use the exact same-repo job guard",
                    ))

    return ScanResult(len(paths), jobs_scanned, self_hosted_jobs, violations, broken)


def _payload(result: ScanResult) -> dict[str, Any]:
    return {
        "ok": not result.violations and not result.broken,
        "workflows_scanned": result.workflows_scanned,
        "jobs_scanned": result.jobs_scanned,
        "self_hosted_jobs": result.self_hosted_jobs,
        "violations": [asdict(item) for item in result.violations],
        "broken": result.broken,
    }


def _print_text(result: ScanResult) -> None:
    print(
        "[self-hosted-policy] "
        f"workflows={result.workflows_scanned} jobs={result.jobs_scanned} "
        f"self_hosted={result.self_hosted_jobs}"
    )
    for item in result.violations:
        print(
            f"  VIOLATION {item.code}: {item.workflow}:{item.job}: "
            f"{item.message}"
        )
    for item in result.broken:
        print(f"  BROKEN: {item}")
    if not result.violations and not result.broken:
        if result.self_hosted_jobs == 0:
            print("[self-hosted-policy] OK -- explicit baseline: 0 self-hosted jobs.")
        else:
            print("[self-hosted-policy] OK -- all self-hosted jobs satisfy isolation policy.")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="print a text verdict")
    parser.add_argument("--json", action="store_true", help="print a JSON verdict")
    parser.add_argument(
        "--workflows-dir",
        type=Path,
        default=DEFAULT_WORKFLOWS_DIR,
        help="workflow directory (used by tests and offline audits)",
    )
    args = parser.parse_args(argv)

    result = scan_workflows(args.workflows_dir)
    if args.json:
        print(json.dumps(_payload(result), indent=2, ensure_ascii=False))
    else:
        _print_text(result)

    if result.broken:
        return EXIT_BROKEN
    if result.violations:
        return EXIT_VIOLATION
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
