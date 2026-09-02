#!/usr/bin/env python3
"""Enforce the isolation policy for future self-hosted Actions jobs (#12704).

The repository is public. A self-hosted job that can receive a fork payload can
execute untrusted code next to the cluster's credentials. This scanner therefore
fails closed: every self-hosted job must belong to an explicitly allowed
workflow, use the exact dedicated label set, and avoid runner groups (unavailable
for this personal-account repository). Every pull_request job must also carry
the exact same-repository guard. A self-hosted job is gated on a trigger
allowlist (pull_request, push, schedule, workflow_dispatch): these only run
repository-owned refs, and are checked for the same-repo guard when
pull_request is present. Any other trigger is rejected fail-closed -- the
known-dangerous ones carry specific codes (pull_request_target, workflow_run,
issue_comment, pull_request_review, pull_request_review_comment), and anything
unlisted (e.g. check_run / check_suite, whose payload can name a fork pull
request) is refused by default. Dynamic ``runs-on`` expressions are rejected
because their target cannot be proved statically.

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

REQUIRED_LABELS = {
    "self-hosted",
    "coursia-ephemeral",
    "coursia-fast-guards",
}
# Dedicated label set for the containerized Linux runner (mission #13378,
# dispatch ai-01 2026-08-31, po-2024): routes ONLY to the Docker container,
# never to the Windows fast-guards runners -- the distinct label is the
# routing guarantee (a windows dispatch must not land on Linux).
LINUX_RUNNER_LABELS = {
    "self-hosted",
    "coursia-ephemeral",
    "coursia-linux",
}
DEDICATED_LABEL_SETS = (REQUIRED_LABELS, LINUX_RUNNER_LABELS)
# Owner-approved additions must cite the lane that owns the runner deployment:
# - pr-gate-stale-sweep.yml: schedule-mutualized re-aggregation (pre-existing).
# - windows-self-hosted-tests.yml: workflow_dispatch-ONLY vehicle for the 9
#   @requires_windows confinement tests (#13063 skip surface), zero fan-out
#   (#13097), executed on an --ephemeral runner (#12704, po-2024, #13135).
# - linux-self-hosted-tests.yml: workflow_dispatch-ONLY pilot vehicle for the
#   containerized Linux runner (#13378, po-2024, dispatch ai-01 2026-08-31),
#   zero fan-out, --ephemeral inside a capped Docker container.
# - tranche 1 (#13378, decision ai-01 2026-09-01, owner myia-po-2024:CoursIA):
#   pure-Python guards, no secret, no GITHUB_TOKEN use, universal same-repo
#   guard (#13874) at job level so fork PRs are skipped (pr_gate.py counts
#   `skipped` as OK). Routed to the containerized Linux leg to relieve the
#   GitHub-hosted queue. Rollback = revert of the routing PR.
SELF_HOSTED_WORKFLOW_ALLOWLIST = {
    "pr-gate-stale-sweep.yml",
    "windows-self-hosted-tests.yml",
    "linux-self-hosted-tests.yml",
    "banner-guard.yml",
    "solution-leak-guard.yml",
    "prose-counts-guard.yml",
    "notebook-interp-positioning.yml",
    "notebook-cell-source-parses.yml",
    "cell-order-gate.yml",
    "pip-leak-guard.yml",
    "hooks-parity.yml",
    "notebook-exec-sequence-ratchet.yml",
    "notebook-navlink-check.yml",
    "notebook-papermill-ratchet.yml",
    # tranche 3b (#14283, meme decision, meme owner) : suite des gardes PR
    #   pure-Python. Fondue dans la meme PR que 3a -- les scinder aurait produit
    #   un conflit sur cette meme ancre pour zero benefice de relecture.
    "markdown-claims-output-advisory.yml",
    "orphaned-delivery-scan.yml",
    "quantconnect-notebook-freshness.yml",
    "scan-md-hierarchy-drift.yml",
    "slides-composition-pr-relay.yml",
    "source-output-ratchet.yml",
    "translation-guard.yml",
    "unique-check-run-names-guard.yml",
    "validation-matrix.yml",
    # tranche 3a (#14283, decision ai-01 2026-09-02, owner myia-ai-01:CoursIA) :
    #   gardes PR pure-Python, garde same-repo au niveau job, runs-on STATIQUE.
    #   Exclus deliberement : pr-gate.yml (agregateur qui poll -- il tiendrait le
    #   slot quil attend), owui-playwright-check.yml (navigateurs hors image),
    #   always-on-guards.yml (trigger pull_request_review = FORK_REACHABLE).
    #   Rollback = revert de la PR de routage.
    "arxiv-attributions-guard.yml",
    "catalog-drift.yml",
    "consecutive-code-cells-advisory.yml",
    "harness-coauthor-guard.yml",
    "ict-tests.yml",
    "label-paths-guard.yml",
    "lean-conway.yml",
    "lean-i18n-drift.yml",
    "lean-knot.yml",
    "manifest-description-visuelle-gate.yml",
    # tranche 3c (#14283, meme decision, meme owner) : jobs individuels d'un
    #   workflow dont les autres jobs restent sur ubuntu-latest.
    #   Exclus deliberement : ml-tests (torch retelecharge a chaque run, pas de
    #   cache persistant), lean-social-
    #   choice/build (merite un pool a cache Mathlib chaud, cf #14337),
    #   notebook-execution-required/golden-set-execute (execution lourde).
    "bash-syntax-advisory.yml",
    "lean-social-choice.yml",
    "notebook-execution-required.yml",
    "secret-scan.yml",
    # secret-scan/gitleaks : exclu en 3c pour la socket Docker, LEVE depuis --
    #   le job scanner n'utilise plus `docker run` mais le binaire epingle
    #   (meme release, meme ${GITLEAKS_VERSION}), forme deja eprouvee sur ce
    #   pool par son job positive-controls. La jambe fork reste GitHub-hosted
    #   sous la forme docker : `gitleaks-fork`.
    # always-on-metadata-guards.yml : routable (triggers pull_request +
    #   workflow_dispatch seulement). Son jumeau always-on-guards.yml ne l'est
    #   PAS -- il porte pull_request_review, classe FORK_REACHABLE (#14294).
    "always-on-metadata-guards.yml",
    "twin-parity.yml",
    # tranche 4 (#14283, meme decision, meme owner) : balayages cron pur-Python.
    #   Declencheur `schedule` seul -- pas de contexte pull_request, donc aucune
    #   garde same-repo requise. 33 creneaux distincts, au plus 2 simultanes
    #   (mesure 2026-09-02) : ils ne peuvent pas affamer les gardes de PR.
    #   Exclus : markdown-table-guard / render-volume-delta-advisory (lourds),
    #   slides-composition-advisory (navigateurs hors image).
    "ascii-flowchart-advisory.yml",
    "candidate-delivered-advisory.yml",
    "catalog-cron.yml",
    "check-resync-only.yml",
    "cjk-residue-advisory.yml",
    "degraded-mode-advisory.yml",
    "detect-dup-selftest.yml",
    "dotnet-nuget-block-advisory.yml",
    "epic-charter-advisory.yml",
    "epic-neglect-sweep.yml",
    "exercises-advisory.yml",
    "grain-orphans-sweep.yml",
    "h1-hygiene-advisory.yml",
    "leaky-fixture-sweep.yml",
    "machine-dep-timing-advisory.yml",
    "machine-dep-timing-inventory.yml",
    "orphan-branch-scan.yml",
    "outputs-text-fragmentation-advisory.yml",
    "pedagogy-density-advisory.yml",
    "pr-gate-missing-advisory.yml",
    "pr-gate-sweep-health-advisory.yml",
    "pr-path-collision-advisory.yml",
    "qc-research-monitor.yml",
    "repo-size-advisory.yml",
    "review-coverage-advisory.yml",
    "slides-build-advisory.yml",
    "slow-lane.yml",
    "stale-guard-red-sweep.yml",
    "translation-parity.yml",
    "twin-parity-cron.yml",
    "twin-parity-drift-audit.yml",
    "workflow-path-filter-audit.yml",

    # - tranche 5 (#13378/#14283, decision ai-01 2026-09-02) : le solde des
    #   gardes routables. Exclus et pourquoi : pr-gate.yml (agregateur qui
    #   poll jusqu'a 28 min -- le router reproduirait la famine mesuree en
    #   #11405), lean-axiom/lean-build (builds Lean sans cache mathlib, cf
    #   #14337 pools specialises), slides-composition-advisory (playwright
    #   --with-deps exige root, le conteneur tourne en uid 1001).
    #   quarto-pages-deploy : jobs build/validate-pr routes en fin de chantier
    #   (tarball, voir l'entree dediee) ; seul `deploy` reste exclu (Pages/OIDC).
    "bare-cross-dir-load-gate.yml",
    "base-not-main-advisory.yml",
    "concurrency-conj-guard.yml",
    "degenerate-figure-gate.yml",
    "docs-link-check.yml",
    "exercise-leak-ci.yml",
    "fabricated-output-gate.yml",
    "fast-lane-shadow.yml",
    "lane-claim-guard.yml",
    "linux-runner-starvation-advisory.yml",
    "markdown-rendering-guard.yml",
    "markdown-table-guard.yml",
    "md-content-loss-gate.yml",
    "ml-tests.yml",
    "notebook-output-failure-ratchet.yml",
    "notebook-validation.yml",
    "owui-playwright-check.yml",
    "perimeter-review-guard.yml",
    "pr-gate-rerun.yml",
    "regression-guard.yml",
    "render-volume-delta-advisory.yml",
    "scripts-tests.yml",
    "series-naming-gate.yml",
    "stale-base-warning.yml",
    # fin de chantier #14283 (feu vert ai-01 2026-09-02) : les jobs
    #   quarto-pages-deploy `build` et `validate-pr` passent au pool — le
    #   setup Quarto se fait par tarball auto-contenu (l'action canonique
    #   exige sudo apt + dpkg, absents de l'image no-new-privileges, mesure
    #   issuecomment-5516335275). Le job `deploy` RESTE ubuntu-latest :
    #   deploy-pages + OIDC/env github-pages, question separee.
    "quarto-pages-deploy.yml",
    "svg-broken-geometry-gate.yml",
    "svg-decimal-comma-gate.yml",
    "svg-empty-display-gate.yml",
    "svg-offscreen-flat-gate.yml",
    "testpaths-coverage-guard.yml",
    "translation-drift.yml",
    "translation-sync.yml",
    "variation-light-genre.yml",
}
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
    r"^jsboige/CoursIA/\.github/workflows/[^/@]+@main$"
)
SAME_REPO_GUARD = (
    "github.event.pull_request.head.repo.full_name == github.repository"
)
# Universal form (#13874): ne s'appuie pas sur la valeur textuelle de
# github.event_name (qui distingue pull_request de pull_request_target,
# le second etant le vecteur d'exfiltration classique sur runner public).
# Teste la presence du champ pull_request + l'identite du repo source,
# couvrant les deux variantes de declencheur en un seul predicat.
# Acceptee en plus de la forme directe SAME_REPO_GUARD.
SAME_REPO_GUARD_UNIVERSAL = (
    "github.event.pull_request.head.repo.full_name == null "
    "|| github.event.pull_request.head.repo.full_name == github.repository"
)
ACCEPTED_SAME_REPO_GUARDS = frozenset({SAME_REPO_GUARD, SAME_REPO_GUARD_UNIVERSAL})
# Evenements dont le code de workflow vient de la branche par defaut mais dont
# le payload nomme une pull request potentiellement issue d'un fork : un job
# peut faire `checkout refs/pull/N/head` et executer du code de fork sur le
# runner. Refuses sur self-hosted au meme titre que pull_request_target
# (#14148, reserve NanoClaw n.2). A l'inverse, push / schedule /
# workflow_dispatch ne portent que des refs du depot : la branche `== null`
# de la garde universelle y est sure par construction, pas par accident.
FORK_REACHABLE_TRIGGERS = frozenset({
    "issue_comment",
    "pull_request_review",
    "pull_request_review_comment",
})
# Safe triggers for a self-hosted job (#14201, tranche 2). push, schedule and
# workflow_dispatch only run repository-owned refs, so the `== null` branch of
# the universal guard is safe there by construction (NanoClaw concern 2,
# measured on the routed workflows: banner-guard.yml / notebook-cell-source-
# parses.yml / hooks-parity.yml rely on push / schedule). pull_request is safe
# only WITH the same-repo guard (enforced above). Everything else is rejected
# fail-closed: a denylist alone (the FORK_REACHABLE_TRIGGERS form of #14148) is
# fail-OPEN on any trigger we have not enumerated -- check_run / check_suite,
# whose payloads carry pull_requests[], and any future GitHub event that does
# the same. Default-deny is the form that does not perish with each new event.
SAFE_SELF_HOSTED_TRIGGERS = frozenset({
    "pull_request",
    "push",
    "schedule",
    "workflow_dispatch",
})
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


def _runner_selection(
    runs_on: Any,
) -> tuple[bool, str | None, set[str], str | None]:
    """Return (is_self_hosted, group, labels, error) for a static selection.

    Any explicit runner group is self-hosted. A scalar/list label is considered
    GitHub-hosted only when every value names a documented hosted-image family;
    custom labels route to self-hosted runners even when the implicit
    ``self-hosted`` label is omitted from the workflow.
    """
    if isinstance(runs_on, str):
        labels = {runs_on.lower()}
        return not _is_github_hosted_label(runs_on), None, labels, None
    if isinstance(runs_on, list):
        if not runs_on or not all(isinstance(item, str) for item in runs_on):
            return False, None, set(), "runs-on list must contain labels"
        labels = {item.lower() for item in runs_on}
        is_self_hosted = any(not _is_github_hosted_label(item) for item in labels)
        return is_self_hosted, None, labels, None
    if isinstance(runs_on, dict):
        group = runs_on.get("group")
        raw_labels = runs_on.get("labels", [])
        if group is None and "labels" not in runs_on:
            return False, None, set(), "runs-on mapping needs group or labels"
        if group is not None and not isinstance(group, str):
            return False, None, set(), "runner group must be a string"
        if isinstance(raw_labels, str):
            labels = {raw_labels.lower()}
        elif isinstance(raw_labels, list) and raw_labels and all(
            isinstance(item, str) for item in raw_labels
        ):
            labels = {item.lower() for item in raw_labels}
        elif raw_labels == [] and group is not None:
            labels = set()
        else:
            return False, None, set(), "runner labels must be a string or list"
        is_self_hosted = group is not None or any(
            not _is_github_hosted_label(item) for item in labels
        )
        return is_self_hosted, group, labels, None
    return False, None, set(), "runs-on has an unsupported type"


def _normalise_condition(value: Any) -> str:
    if not isinstance(value, str):
        return ""
    condition = value.strip()
    if condition.startswith("${{") and condition.endswith("}}"):
        condition = condition[3:-2].strip()
    return " ".join(condition.split())


def _starts_with_accepted_guard(condition: str) -> bool:
    """True iff ``condition`` leads with one of the accepted same-repo
    guards, optionally followed by `&& ...` selection predicates. The guard
    must be the LEAD predicate, and any suffix joined by `||` is rejected
    (the `||` would let the guard fall through). The standalone tests
    ``test_guard_weakened_by_or_is_rejected`` and
    ``test_universal_guard_weakened_by_or_is_rejected`` verify that
    `|| always()` is refused.

    Parentheses: the direct guard may be bare or wrapped. The UNIVERSAL guard
    carries an internal `||`, so it is accepted bare only when it is the whole
    condition; combined with `&& ...` it MUST be wrapped --
    `(<universal>) && <selection>`. This is not a parser limitation to work
    around: in GitHub expressions `&&` binds tighter than `||`, so the bare
    form reads `A == null || (A == repo && sel)` and runs the job on every
    non-pull_request event regardless of the selection. The bare scan below
    splits at the first top-level operator (the internal `||`) and rejects;
    ``_guard_violation_message`` names the required parentheses
    (#14148, NanoClaw concern 1).
    """
    if not condition:
        return False
    # Short-circuit: the whole condition is itself an accepted guard.
    if condition in ACCEPTED_SAME_REPO_GUARDS:
        return True
    lead = condition
    suffix = ""
    if lead.startswith("("):
        depth = 0
        for idx, ch in enumerate(lead):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    lead = lead[: idx + 1]
                    suffix = condition[idx + 1 :].lstrip()
                    break
    else:
        # Bare form: scan character by character for a top-level ` && `
        # or ` || ` (4 chars including surrounding spaces). An external
        # `&&` joining a selection predicate is OK; an external `||` is
        # rejected because it lets the guard fall through. The internal
        # `||` of the universal form is captured by the short-circuit
        # above (whole-condition match), so this branch only fires when
        # the condition is followed by an external operator.
        depth = 0
        i = 0
        while i < len(lead) - 3:
            ch = lead[i]
            if ch == "(":
                depth += 1
                i += 1
                continue
            if ch == ")":
                depth -= 1
                i += 1
                continue
            if depth == 0 and lead[i : i + 4] in (" && ", " || "):
                lead = lead[:i]
                suffix = condition[i:]
                break
            i += 1
    for accepted in ACCEPTED_SAME_REPO_GUARDS:
        if lead == accepted or lead == "(" + accepted + ")":
            if not suffix:
                return True
            if suffix.lstrip().startswith("&&"):
                return True
            return False
    return False


def _guard_violation_message(condition: str) -> str:
    """Name the exact defect: a bare universal guard followed by `&&` is the
    one rejection whose fix is not "add the guard" but "add parentheses"."""
    if condition.startswith(SAME_REPO_GUARD_UNIVERSAL):
        tail = condition[len(SAME_REPO_GUARD_UNIVERSAL):].lstrip()
        if tail.startswith("&&"):
            return (
                "universal same-repo guard combined with `&&` must be parenthesised: "
                "`(<universal guard>) && <selection>` -- `&&` binds tighter than `||`, "
                "so the bare form bypasses the selection outside pull_request context"
            )
    return "pull_request self-hosted job must lead with the same-repo job guard"


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

        if "on" not in data and True not in data:
            broken.append(f"{path.name}: missing on trigger")
            continue
        triggers = _triggers(data)
        if not triggers:
            broken.append(f"{path.name}: on trigger is empty or unsupported")
            continue

        if "jobs" not in data:
            broken.append(f"{path.name}: missing jobs")
            continue
        jobs = data["jobs"]
        if not isinstance(jobs, dict) or not jobs:
            broken.append(f"{path.name}: jobs is not a non-empty mapping")
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
                        "to main",
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

            is_self_hosted, group, labels, selection_error = _runner_selection(runs_on)
            if selection_error is not None:
                broken.append(f"{path.name}:{job_name}: {selection_error}")
                continue
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
            for trigger in sorted(FORK_REACHABLE_TRIGGERS & triggers):
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "FORK_REACHABLE_TRIGGER",
                    f"{trigger} can check out a fork pull request and must never "
                    "reach a self-hosted runner",
                ))
            # Fail-closed default deny (#14201, tranche 2). The known-dangerous
            # triggers above carry specific codes; ANY other trigger outside the
            # safe set is refused by default. A denylist alone (the #14148
            # FORK_REACHABLE_TRIGGERS form) is fail-OPEN on anything unlisted.
            known_unsafe = FORK_REACHABLE_TRIGGERS | {
                "pull_request_target",
                "workflow_run",
                "workflow_call",
            }
            unknown_unsafe = sorted(
                triggers - SAFE_SELF_HOSTED_TRIGGERS - known_unsafe
            )
            if unknown_unsafe:
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "UNSAFE_TRIGGER",
                    "self-hosted job is gated on a trigger outside the safe set "
                    "(pull_request, push, schedule, workflow_dispatch): "
                    + ", ".join(unknown_unsafe),
                ))

            if path.name not in SELF_HOSTED_WORKFLOW_ALLOWLIST:
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "WORKFLOW_NOT_ALLOWED",
                    "self-hosted runners are restricted to explicitly allowed workflows",
                ))

            if group is not None:
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "RUNNER_GROUP_UNAVAILABLE",
                    "runner groups are unavailable for this personal-account repository",
                ))

            if any(set(labels) == allowed for allowed in DEDICATED_LABEL_SETS):
                missing: list[str] = []
                unexpected: list[str] = []
            else:
                missing = sorted(REQUIRED_LABELS - labels)
                unexpected = sorted(labels - REQUIRED_LABELS)
            if missing or unexpected:
                detail = []
                if missing:
                    detail.append(f"missing: {', '.join(missing)}")
                if unexpected:
                    detail.append(f"unexpected: {', '.join(unexpected)}")
                violations.append(Violation(
                    path.name,
                    str(job_name),
                    "RUNNER_LABELS",
                    "dedicated labels must match exactly (" + "; ".join(detail) + ")",
                ))

            if "pull_request" in triggers:
                condition = _normalise_condition(job.get("if"))
                # Accept either the bare guard or the guard followed by a
                # selection predicate (e.g. `&& inputs.target == '...'`)
                # joined with `&&` -- the guard must be the lead predicate,
                # never weakened by `||` (cf. test_guard_weakened_by_or_is_rejected).
                if not _starts_with_accepted_guard(condition):
                    violations.append(Violation(
                        path.name,
                        str(job_name),
                        "SAME_REPO_GUARD",
                        _guard_violation_message(condition),
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
