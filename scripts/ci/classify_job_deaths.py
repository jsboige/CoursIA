#!/usr/bin/env python3
"""Classify CI job deaths on a branch: infrastructural vs real failures.

Issue #15055 : les 4 rouges de main de la fenetre 2026-09-06T13:32Z ->
2026-09-07T11:05Z ne sont pas des regressions de contenu mais des jobs morts
sur le parc de runners auto-heberges. Le défaut mesuré : le motif de mort
n'est PAS visible au niveau run (la conclusion agrégée masque la cause), et
l'identifier exigeait d'ouvrir chaque job à la main.

Pourtant la cause est LISIBLE PAR API : GitHub pose une annotation sur le
check-run du job quand il meurt d'une cause infrastructurelle. Cet outil la
lit et rend le motif comptable sans intervention manuelle :

  * ``NO_RUNNER_ACQUIRED``   -- "The job was not acquired by Runner of type
    self-hosted even after multiple attempts". Job cancelled, jamais assigne
    (runner_name vide, 0/0 steps), ~3 min entre queue et annulation : le
    dispatcher GitHub a renonce apres echecs repetes d'acquisition du runner.
  * ``RUNNER_LOST_COMM``     -- "The self-hosted runner lost communication
    with the server". Job failure, runner assigne, N/M steps resolues, les
    suivantes en ``null`` : l'agent a perdu la connexion en cours de route.
  * ``TIMEOUT``              -- "has exceeded the maximum execution time"
    (``timeout-minutes`` du workflow).
  * ``REAL_STEP_FAILURE``    -- au moins une etape en ``failure`` : le vrai
    rouge de contenu, le seul qui exige une correction du code.
  * ``CANCELLED_OTHER``      -- cancelled sans annotation d'acquisition :
    concurrence (``cancel-in-progress`` inconditionnel, ex. quarto), annulation
    manuelle ou supersession.

Acceptance #15055 couverte par cette tranche :
  * critere 1 : la cause de l'absence d'assignation est NOMMEE (echec
    d'acquisition, annotation verbatim) et distinguable d'une annulation par
    concurrence dans la trace elle-meme ;
  * critere 2 : le motif de mort est identifiable sans ouvrir le job a la main.

Usage :
  python scripts/ci/classify_job_deaths.py --created 2026-09-06..2026-09-07
  python scripts/ci/classify_job_deaths.py --sha <SHA complet 40 chars> --json
  python scripts/ci/classify_job_deaths.py --run 34066220916

Note : ``actions/runs?head_sha=`` exige le SHA complet -- un prefixe de 12
caracteres rend 0 run, zero propre indiscernable d'une absence reelle
(mesure #15055). L'argument --sha valide donc la longueur.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone

REPO_SLUG = "jsboige/CoursIA"

# Annotations verbatim posees par GitHub sur le check-run du job. Le prefixe
# suffit : le texte integral varie selon la version du service.
ANNOTATION_CLASSES: list[tuple[str, str]] = [
    ("not acquired by Runner", "NO_RUNNER_ACQUIRED"),
    ("lost communication with the server", "RUNNER_LOST_COMM"),
    ("exceeded the maximum execution time", "TIMEOUT"),
    ("The runner has received a shutdown signal", "RUNNER_LOST_COMM"),
]


def gh_api(path: str, params: str = "") -> dict | list:
    """GET un chemin de l'API GitHub via gh, echoue bruyamment."""
    url = f"repos/{REPO_SLUG}/{path}{params}"
    result = subprocess.run(
        ["gh", "api", url],
        capture_output=True,
        text=True,
        timeout=60,
        encoding="utf-8",
        errors="replace",
    )
    if result.returncode != 0:
        raise RuntimeError(f"gh api {url} failed: {result.stderr.strip()[:200]}")
    return json.loads(result.stdout)


def classify_job(job: dict, annotations: list[dict]) -> str:
    """Retourne la classe de mort d'un job terminal non-success.

    Priorite : une etape reellement echouee est un rouge de contenu, meme si
    une annotation infrastructurelle coexiste (le runner peut mourir pendant
    les steps de post-processing d'un echec legitime).
    """
    if job.get("conclusion") == "skipped":
        return "SKIPPED"
    if job.get("conclusion") == "success":
        return "SUCCESS"
    steps = job.get("steps") or []
    if any(s.get("conclusion") == "failure" for s in steps):
        return "REAL_STEP_FAILURE"
    messages = [a.get("message", "") for a in annotations]
    for needle, klass in ANNOTATION_CLASSES:
        if any(needle in m for m in messages):
            return klass
    if job.get("conclusion") == "failure":
        return "UNCATEGORIZED_FAILURE"
    return "CANCELLED_OTHER"


def fetch_run_jobs(run_id: int) -> list[dict]:
    jobs: list[dict] = []
    page = 1
    while True:
        data = gh_api(f"actions/runs/{run_id}/jobs", f"?per_page=100&page={page}")
        batch = data.get("jobs", [])
        jobs.extend(batch)
        if len(batch) < 100:
            return jobs
        page += 1


def fetch_annotations(job_id: int) -> list[dict]:
    try:
        data = gh_api(f"check-runs/{job_id}/annotations")
    except RuntimeError:
        # Les jobs sans annotation peuvent rendre 404 selon l'endpoint ;
        # l'absence d'annotation est une classe valide (CANCELLED_OTHER /
        # UNCATEGORIZED_FAILURE), pas une erreur d'instrument.
        return []
    return data if isinstance(data, list) else []


def parse_created(created: str) -> str:
    if ".." not in created:
        raise SystemExit("--created exige une fenetre START..END (dates ISO)")
    return created


def iter_red_runs(
    branch: str, event: str, created: str, max_runs: int
) -> list[dict]:
    """Runs non-verts de la fenetre, en deux passes (failure puis cancelled)."""
    runs: list[dict] = []
    for status in ("failure", "cancelled"):
        page = 1
        while True:
            params = (
                f"?branch={branch}&event={event}&status={status}"
                f"&created={created}&per_page=100&page={page}"
            )
            data = gh_api("actions/runs", params)
            batch = data.get("workflow_runs", [])
            runs.extend(batch)
            if len(batch) < 100:
                break
            page += 1
        if len(runs) >= max_runs:
            print(
                f"cap --max-runs={max_runs} atteint, fenetre tronquee",
                file=sys.stderr,
            )
            return runs[:max_runs]
    return runs


def dur(started: str | None, completed: str | None) -> str:
    if not started or not completed:
        return "-"
    fmt = "%Y-%m-%dT%H:%M:%SZ"
    try:
        delta = datetime.strptime(completed, fmt) - datetime.strptime(
            started, fmt
        )
    except ValueError:
        return "-"
    minutes = int(delta.total_seconds() // 60)
    return f"{minutes}m{int(delta.total_seconds() % 60):02d}s"


def analyse_runs(runs: list[dict]) -> dict:
    rows: list[dict] = []
    for run in runs:
        run_id = run["id"]
        jobs = fetch_run_jobs(run_id)
        if not jobs and run.get("conclusion") == "cancelled":
            # Run annule avant toute creation de job (signature mesuree le
            # 2026-09-07T23:02:33Z : 5 workflows annules en bloc, 4 s apres
            # la pousse precedente). Distinct de NO_RUNNER_ACQUIRED, ou un
            # job existe et attend ~3 min avant l'annotation d'echec
            # d'acquisition. Sans cette ligne, ces runs seraient comptes
            # dans runs_scanned mais invisibles dans les rows.
            rows.append(
                {
                    "run_id": run_id,
                    "workflow": run.get("name", "?"),
                    "job_id": run_id,
                    "job": "(no jobs created)",
                    "class": "RUN_CANCELLED_NO_JOBS",
                    "conclusion": "cancelled",
                    "runner": "(none)",
                    "steps": "-",
                    "duration": dur(run.get("created_at"), run.get("updated_at")),
                    "run_created": run.get("created_at"),
                    "url": f"https://github.com/{REPO_SLUG}/actions/runs/{run_id}",
                    "head_sha": run.get("head_sha", "")[:10],
                }
            )
            continue
        for job in jobs:
            klass = classify_job(job, fetch_annotations(job["id"]))
            if klass in ("SUCCESS", "SKIPPED"):
                continue
            steps = job.get("steps") or []
            resolved = sum(1 for s in steps if s.get("conclusion") == "success")
            rows.append(
                {
                    "run_id": run_id,
                    "workflow": run.get("name", "?"),
                    "job_id": job["id"],
                    "job": job.get("name", "?"),
                    "class": klass,
                    "conclusion": job.get("conclusion"),
                    "runner": job.get("runner_name") or "(none)",
                    "steps": f"{resolved}/{len(steps)}",
                    "duration": dur(job.get("started_at"), job.get("completed_at")),
                    "run_created": run.get("created_at"),
                    "url": f"https://github.com/{REPO_SLUG}/actions/runs/{run_id}",
                    "head_sha": run.get("head_sha", "")[:10],
                }
            )
    counts: dict[str, int] = {}
    for r in rows:
        counts[r["class"]] = counts.get(r["class"], 0) + 1
    return {"rows": rows, "counts": counts}


def render_markdown(payload: dict) -> str:
    counts = payload["counts"]
    total = sum(counts.values())
    infra = sum(
        counts.get(k, 0) for k in ("NO_RUNNER_ACQUIRED", "RUNNER_LOST_COMM")
    )
    out = ["# Audit job deaths (issue #15055)", ""]
    out.append(
        f"Jobs morts non-skips analyses : **{total}** | "
        f"morts infrastructurelles : **{infra}** "
        f"(NO_RUNNER_ACQUIRED={counts.get('NO_RUNNER_ACQUIRED', 0)}, "
        f"RUNNER_LOST_COMM={counts.get('RUNNER_LOST_COMM', 0)}) | "
        f"REAL_STEP_FAILURE={counts.get('REAL_STEP_FAILURE', 0)} | "
        f"AUTRES={total - infra - counts.get('REAL_STEP_FAILURE', 0)}"
    )
    out.append("")
    out.append(
        "| Run | Workflow | Job | Classe | Runner | Steps | Duree | SHA |"
    )
    out.append("|---|---|---|---|---|---|---|---|")
    for r in payload["rows"]:
        out.append(
            f"| [{r['run_id']}]({r.get('url', '')}) | {r['workflow']} | "
            f"{r['job']} | **{r['class']}** | {r['runner']} | {r['steps']} | "
            f"{r['duration']} | {r['head_sha']} |"
        )
    out.append("")
    return "\n".join(out)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--branch", default="main", help="branche analysee (defaut main)"
    )
    parser.add_argument(
        "--event", default="push", help="evenement (defaut push)"
    )
    parser.add_argument(
        "--created",
        type=parse_created,
        help="fenetre ISO START..END, ex. 2026-09-06..2026-09-07",
    )
    parser.add_argument(
        "--sha",
        help="SHA COMPLET 40 chars (un prefixe rend 0 run, mesure #15055)",
    )
    parser.add_argument(
        "--run", type=int, help="analyser un run unique par son id"
    )
    parser.add_argument(
        "--max-runs",
        type=int,
        default=200,
        help="cap de runs rouges analyses (defaut 200)",
    )
    parser.add_argument("--json", action="store_true", help="JSON sur stdout")
    parser.add_argument(
        "--report",
        type=str,
        default=None,
        help="chemin du rapport markdown a ecrire",
    )
    args = parser.parse_args()

    if args.run:
        run = gh_api(f"actions/runs/{args.run}")
        runs = [run]
    elif args.sha:
        if len(args.sha) != 40:
            print(
                "--sha exige le SHA complet (40 chars) : un prefixe rend "
                "0 run, zero propre indiscernable d'une absence reelle",
                file=sys.stderr,
            )
            return 2
        data = gh_api(
            "actions/runs", f"?head_sha={args.sha}&per_page=100"
        )
        runs = [
            r
            for r in data.get("workflow_runs", [])
            if r.get("conclusion") not in ("success", "skipped")
        ]
    elif args.created:
        runs = iter_red_runs(args.branch, args.event, args.created, args.max_runs)
    else:
        parser.error("--created, --sha ou --run requis")
        return 2

    payload = analyse_runs(runs)
    payload["issue"] = 15055
    payload["generated_at"] = datetime.now(timezone.utc).strftime(
        "%Y-%m-%dT%H:%M:%SZ"
    )
    payload["runs_scanned"] = len(runs)

    if args.json:
        print(json.dumps(payload, indent=2, ensure_ascii=False))
    text = render_markdown(payload)
    if args.report:
        with open(args.report, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(text)
        print(f"Report written: {args.report}", file=sys.stderr)
    if not args.json:
        print(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
