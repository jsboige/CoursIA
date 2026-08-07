"""CI check-runs aggregator -- logique de classification et verdict.

Appelé par `.github/workflows/ci-required-aggregator.yml` pour décider si
les check-runs d'une PR autorisent un verdict PASS ou FAIL au merge.

Contexte fondateur : #9819 (incident #9762 : PR mergée avec
`ci / Lean CI (grothendieck_lean)` rouge + `proof-integrity` rouge
parce que `required_status_checks` est vide sur `main`). Étape 1
safe : on livre un verdict observable SANS flipper le repo setting.
Étape 2 (inscrire comme `required_status_check`) reste gated user.

La logique :
1. Filtrer le check-run de l'aggregator lui-même (sinon il s'auto-bloque).
2. Filtrer les "advisory" / "non-blocking" (regex sur le nom).
3. Classer en `failing` (failure/timed_out) / `pending` (non completed
   ou conclusion inconnue) / `passing` (success/skipped/neutral/stale/cancelled).
4. Verdict final : `failing > 0` ou `pending > 0` = FAIL (sinon, un
   aggregator qui ne peut pas rougir n'est pas un aggregator, cf.
   critère d'acceptation #9819.1).

Stdlib only (Python 3.10+) -- cohérent avec `scan_d2_window_openness.py`.
"""

from __future__ import annotations

import json
import re
import sys
from typing import Any

# L'aggregator est lui-même un check-run -- il faut l'ignorer sinon il
# s'auto-bloque sur son propre verdict "pending".
AGGREGATOR_SELF_KEY = "aggregate-checks"

# Les checks "advisory" / "non-blocking" par convention_repo sont dans
# le nom du job : "advisory", "non-blocking", "non blocking", préfixe
# "skip:", ou mot "optional". Regex case-insensitive.
ADVISORY_PATTERN = re.compile(r"advisory|non[-\s]?blocking|^skip[:\s]|optional", re.IGNORECASE)

# Conclusions qui BLOQUENT le merge.
FAILING_CONCLUSIONS = frozenset({"failure", "timed_out"})

# Conclusions qui ne bloquent pas (succès, skip volontaire, neutral,
# stale, cancelled = probablement retry en cours).
PASSING_CONCLUSIONS = frozenset(
    {"success", "skipped", "neutral", "stale", "cancelled"}
)


def is_self(name: str | None) -> bool:
    """True si le check-run est l'aggregator lui-même."""
    if not name:
        return False
    return AGGREGATOR_SELF_KEY.lower() in name.lower()


def is_advisory(name: str | None) -> bool:
    """True si le check-run est explicitement marqué advisory/non-blocking."""
    if not name:
        return False
    return bool(ADVISORY_PATTERN.search(name))


def classify_check_runs(
    check_runs: list[dict[str, Any]],
) -> dict[str, list[dict[str, Any]]]:
    """Classify check-runs into failing / pending / passing / ignored_advisory / ignored_self.

    Each input is a dict with at minimum `name`, `status`, `conclusion`.

    Returns a dict with five lists:
    - `failing`: completed AND conclusion in FAILING_CONCLUSIONS -> would-block merge
    - `pending`: not completed yet, or unexpected conclusion -> aggregator waits
    - `passing`: completed AND conclusion in PASSING_CONCLUSIONS -> OK
    - `ignored_advisory`: filtered out, non-blocking by repo convention
    - `ignored_self`: the aggregator itself (prevent self-blocking)
    """
    failing: list[dict[str, Any]] = []
    pending: list[dict[str, Any]] = []
    passing: list[dict[str, Any]] = []
    ignored_advisory: list[dict[str, Any]] = []
    ignored_self: list[dict[str, Any]] = []

    for run in check_runs:
        name = run.get("name")
        if is_self(name):
            ignored_self.append(run)
            continue
        if is_advisory(name):
            ignored_advisory.append(run)
            continue
        status = run.get("status")
        conclusion = run.get("conclusion")
        if status != "completed":
            pending.append(run)
            continue
        if conclusion in FAILING_CONCLUSIONS:
            failing.append(run)
            continue
        if conclusion in PASSING_CONCLUSIONS:
            passing.append(run)
            continue
        # Conclusion inattendue (nouvelle valeur upstream ?) : on remonte
        # en pending pour observabilité humaine plutôt que de classer
        # silencieusement. Tell explicite pour ne jamais verdir un blanc.
        pending.append(run)

    return {
        "failing": failing,
        "pending": pending,
        "passing": passing,
        "ignored_advisory": ignored_advisory,
        "ignored_self": ignored_self,
    }


def verdict(classified: dict[str, list[dict[str, Any]]]) -> dict[str, Any]:
    """Aggregate verdict from a classified check-runs mapping.

    Returns a dict with:
    - `block_merge` (bool): True if the aggregator would block the merge
    - `reason` (str): human-readable explanation (suitable for setFailed)
    - `summary_counts` (dict): counts per category (for log lines)
    """
    n_failing = len(classified["failing"])
    n_pending = len(classified["pending"])
    n_passing = len(classified["passing"])
    n_advisory = len(classified["ignored_advisory"])
    n_self = len(classified["ignored_self"])

    if n_failing > 0:
        return {
            "block_merge": True,
            "reason": (
                f"CI aggregator: {n_failing} blocking check-run(s) failing. "
                f"Inspect the Actions tab or run `gh pr checks <PR>`."
            ),
            "summary_counts": {
                "failing": n_failing,
                "pending": n_pending,
                "passing": n_passing,
                "ignored_advisory": n_advisory,
                "ignored_self": n_self,
            },
        }
    if n_pending > 0:
        return {
            "block_merge": True,
            "reason": (
                f"CI aggregator: {n_pending} check-run(s) still pending or with "
                f"unknown conclusion. The aggregator does not tolerate a blank "
                f"verdict -- wait for upstream checks to settle or cancel orphan "
                f"workflows."
            ),
            "summary_counts": {
                "failing": n_failing,
                "pending": n_pending,
                "passing": n_passing,
                "ignored_advisory": n_advisory,
                "ignored_self": n_self,
            },
        }
    return {
        "block_merge": False,
        "reason": (
            f"CI aggregator: 0 failing, 0 pending. "
            f"{n_passing} passing. MERGE-CLEAN from CI perspective."
        ),
        "summary_counts": {
            "failing": n_failing,
            "pending": n_pending,
            "passing": n_passing,
            "ignored_advisory": n_advisory,
            "ignored_self": n_self,
        },
    }


def format_log(classified: dict[str, list[dict[str, Any]]]) -> str:
    """Render a human-readable log suitable for the workflow step output."""
    lines: list[str] = []
    for category in ("failing", "pending", "passing", "ignored_advisory", "ignored_self"):
        label = category.replace("_", " ").upper()
        runs = classified[category]
        lines.append(f"=== {label} ({len(runs)}) ===")
        if not runs:
            lines.append("  (none)")
        else:
            for r in runs:
                lines.append(
                    f"  - {r.get('name', '?')} :: "
                    f"status={r.get('status', '?')} "
                    f"conclusion={r.get('conclusion', '?')}"
                )
    return "\n".join(lines)


def main() -> int:
    """Entry point invoked by the workflow.

    Reads check-runs JSON from stdin (one object per line, OR a single
    JSON array -- GitHub CLI outputs NDJSON, GitHub API outputs array).
    Prints the verdict log to stderr and exits 1 if the verdict blocks,
    0 otherwise.
    """
    raw = sys.stdin.read().strip()
    if not raw:
        print(
            "ERROR: no check-runs provided on stdin. "
            "Pass JSON array or NDJSON via the workflow.",
            file=sys.stderr,
        )
        return 2

    # Accepte JSON array OU NDJSON (un objet par ligne) -- robuste aux
    # deux formats que l'API et `gh` produisent.
    try:
        parsed = json.loads(raw)
        if isinstance(parsed, list):
            check_runs = parsed
        elif isinstance(parsed, dict) and "check_runs" in parsed:
            check_runs = parsed["check_runs"]
        else:
            check_runs = [parsed]
    except json.JSONDecodeError:
        check_runs = []
        for line in raw.splitlines():
            line = line.strip()
            if not line:
                continue
            check_runs.append(json.loads(line))

    classified = classify_check_runs(check_runs)
    print(format_log(classified), file=sys.stderr)
    v = verdict(classified)
    print(v["reason"], file=sys.stderr)
    return 1 if v["block_merge"] else 0


if __name__ == "__main__":
    sys.exit(main())