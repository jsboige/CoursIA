#!/usr/bin/env python3
"""Mesure les runs redondants d'une meme tete de commit (#22467).

Un run redondant est un **nouvel essai** (`run_attempt == 1`) du meme workflow
sur la meme tete de commit (`head_sha`) : il rejoue un verdict deja rendu sur
l'identique arbre. Ce n'est pas un re-run d'un job interrompu (ceux-la ont
`run_attempt > 1` et sont comptes a part) : c'est un **declencheur** qui
rejoue.

Deux familles distinctes :

* le double declenchement `push` + `pull_request` sur la meme tete ;
* le declencheur `edited`, qui rejoue le workflow a chaque edition du titre
  ou du body d'une PR (le filtre `paths` reste vrai, les fichiers n'ont pas
  bouge).

L'organe **attribue** chaque redondance a la cause mesurable : pour chaque
run redondant, il cherche un evenement `edited` sur la timeline de la PR
concernant, a moins de trois minutes du debut du run. Une redondance sans
cet evenement n'est pas imputable a `edited` -- et le dire est aussi utile
que le chiffre.

Le collecteur de runs est celui de `scripts/ci/measure_runner_demand.py` :
il decoupe la fenetre quand l'API plafonne a 1000 runs, donc la mesure ne
depend pas d'un plafond silencieux.

Exemples
--------
::

    python scripts/ci/measure_redundant_runs.py --repo jsboige/CoursIA \
        --since 2026-10-31T02:00:00Z --until 2026-11-02T02:00:00Z \
        --output redundant.json
    python scripts/ci/measure_redundant_runs.py --input redundant.json
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from measure_runner_demand import (  # noqa: E402
    MeasurementError,
    collect_runs,
    gh_api,
    iso_z,
    parse_time,
)

#: tolerance d'attribution : un evenement `edited` declenche le run dans les
#: secondes qui suivent ; trois minutes couvre la latence de l'API sans
#: confondre deux editions successives.
ATTRIBUTION_WINDOW_SECONDS = 180

EXIT_OK = 0
EXIT_BROKEN = 2


def _edited_events(repo: str, pr_number: int) -> list[str]:
    """Horodatages des evenements `edited` de la timeline d'une issue."""
    payload = gh_api(
        f"repos/{repo}/issues/{pr_number}/timeline?per_page=100"
    )
    if not isinstance(payload, list):
        raise MeasurementError(f"invalid timeline for issue {pr_number}")
    stamps = []
    for entry in payload:
        if isinstance(entry, dict) and entry.get("event") == "edited":
            created = entry.get("created_at")
            if isinstance(created, str):
                stamps.append(created)
    return stamps


def _attributable(run_started: str, edits: list[str]) -> bool:
    start = parse_time(run_started)
    for stamp in edits:
        delta = abs((start - parse_time(stamp)).total_seconds())
        if delta <= ATTRIBUTION_WINDOW_SECONDS:
            return True
    return False


def analyze(runs: list[dict], edits_by_pr: dict[str, list[str]]) -> dict:
    """Redondances par workflow, et attribution a `edited`."""
    per_workflow: dict[str, dict] = defaultdict(
        lambda: {
            "runs": 0,
            "first_attempts": 0,
            "reruns": 0,
            "redundant_first_attempts": 0,
            "redundant_attributed_to_edited": 0,
            "heads": set(),
        }
    )
    by_head: dict[tuple[str, str], list[dict]] = defaultdict(list)
    for run in runs:
        path = run.get("path") or run.get("name") or "?"
        bucket = per_workflow[path]
        bucket["runs"] += 1
        if run.get("run_attempt", 1) == 1:
            bucket["first_attempts"] += 1
            by_head[(path, run.get("head_sha", ""))].append(run)
        else:
            bucket["reruns"] += 1

    for (path, _sha), group in by_head.items():
        bucket = per_workflow[path]
        bucket["heads"].add(_sha)
        if len(group) < 2:
            continue
        ordered = sorted(group, key=lambda r: (r.get("created_at") or "", r["id"]))
        prs = sorted(
            {
                pr["number"]
                for run in ordered
                for pr in (run.get("pull_requests") or [])
                if isinstance(pr, dict) and "number" in pr
            }
        )
        edits: list[str] = []
        for pr in prs:
            edits.extend(edits_by_pr.get(str(pr), []))
        for run in ordered[1:]:
            bucket["redundant_first_attempts"] += 1
            if _attributable(run.get("created_at") or "", edits):
                bucket["redundant_attributed_to_edited"] += 1

    workflows = []
    for path, bucket in per_workflow.items():
        workflows.append(
            {
                "workflow": path,
                "runs": bucket["runs"],
                "first_attempts": bucket["first_attempts"],
                "reruns": bucket["reruns"],
                "heads": len(bucket["heads"]),
                "redundant_first_attempts": bucket["redundant_first_attempts"],
                "redundant_attributed_to_edited": bucket[
                    "redundant_attributed_to_edited"
                ],
            }
        )
    workflows.sort(key=lambda row: -row["redundant_first_attempts"])
    total_redundant = sum(w["redundant_first_attempts"] for w in workflows)
    total_edited = sum(w["redundant_attributed_to_edited"] for w in workflows)
    return {
        "workflows": workflows,
        "totals": {
            "runs": sum(w["runs"] for w in workflows),
            "first_attempts": sum(w["first_attempts"] for w in workflows),
            "reruns": sum(w["reruns"] for w in workflows),
            "heads": len({r.get("head_sha") for r in runs}),
            "redundant_first_attempts": total_redundant,
            "redundant_attributed_to_edited": total_edited,
        },
        "attribution_window_seconds": ATTRIBUTION_WINDOW_SECONDS,
    }


def render(report: dict) -> str:
    totals = report["totals"]
    lines = [
        f"{'workflow':52s} {'runs':>6s} {'tetes':>6s} {'redond.':>8s} {'dont edited':>12s}"
    ]
    for row in report["workflows"]:
        if not row["redundant_first_attempts"]:
            continue
        lines.append(
            f"{row['workflow'][:52]:52s} {row['runs']:6d} {row['heads']:6d} "
            f"{row['redundant_first_attempts']:8d} "
            f"{row['redundant_attributed_to_edited']:12d}"
        )
    lines.append("")
    lines.append(
        f"{totals['runs']} runs, {totals['heads']} tetes, "
        f"{totals['redundant_first_attempts']} premieres tentatives redondantes, "
        f"dont {totals['redundant_attributed_to_edited']} imputables a un "
        f"evenement `edited` (+/- {report['attribution_window_seconds']} s)"
    )
    return "\n".join(lines)


def collect(repo: str, since: str, until: str) -> tuple[list[dict], dict[str, list[str]]]:
    start = parse_time(since)
    end = parse_time(until)
    runs = collect_runs(repo, start, end)
    # Seules les PRs impliquées dans une tete dupliquée peuvent porter une
    # attribution : on ne lit donc pas la timeline de toute la flotte.
    heads: Counter = Counter(
        (run.get("path") or run.get("name"), run.get("head_sha", ""))
        for run in runs
        if run.get("run_attempt", 1) == 1
    )
    prs = sorted(
        {
            pr["number"]
            for run in runs
            if heads[(run.get("path") or run.get("name"), run.get("head_sha", ""))] > 1
            for pr in (run.get("pull_requests") or [])
            if isinstance(pr, dict) and "number" in pr
        }
    )
    edits_by_pr = {str(pr): _edited_events(repo, pr) for pr in prs}
    return runs, edits_by_pr


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default="jsboige/CoursIA")
    parser.add_argument("--since", required=False, help="debut de fenetre (ISO-8601, TZ)")
    parser.add_argument("--until", required=False, help="fin de fenetre (ISO-8601, TZ)")
    parser.add_argument("--output", default=None, help="snapshot JSON")
    parser.add_argument("--input", default=None, help="rejouer un snapshot")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    try:
        if args.input:
            snapshot = json.loads(Path(args.input).read_text(encoding="utf-8"))
            report = analyze(snapshot["runs"], snapshot["edited_events"])
        else:
            if not args.since or not args.until:
                parser.error("--since et --until sont requis hors mode --input")
            runs, edits = collect(args.repo, args.since, args.until)
            report = analyze(runs, edits)
            if args.output:
                snapshot = {
                    "repo": args.repo,
                    "since": iso_z(parse_time(args.since)),
                    "until": iso_z(parse_time(args.until)),
                    "runs": runs,
                    "edited_events": edits,
                }
                Path(args.output).write_text(
                    json.dumps(snapshot, ensure_ascii=False), encoding="utf-8"
                )
    except MeasurementError as exc:
        print(f"mesure impossible : {exc}", file=sys.stderr)
        return EXIT_BROKEN

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=1))
    else:
        print(render(report))
    return EXIT_OK


if __name__ == "__main__":
    raise SystemExit(main())
