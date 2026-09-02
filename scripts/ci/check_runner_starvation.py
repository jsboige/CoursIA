#!/usr/bin/env python3
"""Organe d'extinction des runners Linux self-hosted (#13378).

POURQUOI CE SCRIPT EXISTE
-------------------------
Le 2026-09-02 entre ~07:00 et 10:25 UTC, le superviseur de conteneurs runner
de myia-po-2024 est mort silencieusement : ses deux slots ont rendu l'ame apres
une generation manglee (bug MSYS), sans qu'aucun signal ne le dise. Sur les 12
workflows routes sur le label `coursia-linux` (#14148), 11 sont bloquants --
un superviseur mort ne degrade pas le CI, il arrete la flotte (3 PRs de
contenu restees rouges ~35 h sur ce seul fait, cf DM ai-01 2026-09-02T07:53Z).

La lecon n'est pas « surveiller le superviseur » (un proxy de proxy), mais de
mesurer le SYMPTOME : des jobs restent-ils non servis ? Deux predicats, dans
l'ordre de fiabilite :

  - EXTINCTION (direct, PAT Administration:read) : plus AUCUN runner online ne
    porte le label. Tant qu'un superviseur vit, ses slots restent enregistres
    online 24/7 -- zero online = extinction, queue vide ou non.
  - STARVATION (symptome, GITHUB_TOKEN seul) : au moins un job libelle queued
    depuis > STARVE_MINUTES minutes, ET aucun job libelle in_progress. Une file
    profonde qui DRAINE (slots busy) est un manque de capacite, pas une
    extinction -- le garde ne rougit pas sur le backlog sain, sinon il serait
    rouge permanent et apprendrait a etre ignore.

Le predicat STARVATION ne demande aucun secret ; le predicat EXTINCTION lit
`/actions/runners` via RUNNERS_READ_PAT (pose 2026-09-02T08:26Z, deliberement
read-only : incapable de minter un registration-token). Sans PAT, l'organe
degrade proprement sur le seul symptome.

Sortie : exit 1 + annotation ::error:: sur EXTINCTION ou STARVATION ;
::warning:: sur perte partielle (online < WARN_FLOOR) sans extinction.
Advisory par construction du workflow appelant (schedule/workflow_dispatch
uniquement, jamais pull_request/push -- il ne peut jamais bloquer une PR).
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import datetime, timezone

DEFAULT_REPO = "jsboige/CoursIA"
DEFAULT_LABEL = "coursia-linux"
DEFAULT_STARVE_MINUTES = 15.0
DEFAULT_WARN_FLOOR = 2
DEFAULT_RUNS_CAP = 30


def _gh_json(args: list[str], token: str | None = None) -> object | None:
    """Run `gh api ...` and parse stdout as JSON. None on failure."""
    env = dict(os.environ)
    if token:
        env["GH_TOKEN"] = token
    proc = subprocess.run(
        ["gh", "api", *args], capture_output=True, text=True,
        check=False, encoding="utf-8", errors="replace", env=env,
    )
    if proc.returncode != 0:
        return None
    if not proc.stdout.strip():
        return None
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        return None


def _parse_iso(value: str | None) -> datetime | None:
    if not value:
        return None
    try:
        return datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return None


@dataclass
class RunnerInventory:
    online: list[str] = field(default_factory=list)
    offline: list[str] = field(default_factory=list)

    @property
    def available(self) -> bool:
        """False = l'inventaire n'a pas pu etre lu (pas de droit admin/PAT)."""
        return True


@dataclass
class InventoryUnavailable(RunnerInventory):
    reason: str = ""

    @property
    def available(self) -> bool:
        return False


@dataclass
class JobRow:
    workflow: str
    run_number: int
    run_id: int
    job_name: str
    status: str
    age_min: float | None


@dataclass
class Starvation:
    starved: list[JobRow] = field(default_factory=list)
    in_progress: list[JobRow] = field(default_factory=list)


def fetch_inventory(repo: str, label: str, token: str | None) -> RunnerInventory:
    data = _gh_json([f"repos/{repo}/actions/runners?per_page=100"], token=token)
    if not isinstance(data, dict) or "runners" not in data:
        return InventoryUnavailable(reason="gh api actions/runners a echoue (droit admin ou RUNNERS_READ_PAT absent)")
    inv = RunnerInventory()
    for r in data.get("runners", []):
        names = [l.get("name") for l in r.get("labels", [])]
        if label not in names:
            continue
        (inv.online if r.get("status") == "online" else inv.offline).append(r.get("name", "?"))
    return inv


def fetch_starvation(repo: str, label: str, starve_minutes: float, cap: int, now: datetime | None = None) -> Starvation:
    now = now or datetime.now(timezone.utc)
    result = Starvation()

    for status, bucket in (("queued", "starved"), ("in_progress", "in_progress")):
        # Query params inline : `-f` forcerait un POST sur un endpoint GET.
        runs = _gh_json([f"repos/{repo}/actions/runs?status={status}&per_page={cap}"])
        if not isinstance(runs, dict):
            continue
        for run in runs.get("workflow_runs", []):
            created = _parse_iso(run.get("created_at"))
            if created is None:
                continue
            jobs = _gh_json([f"repos/{repo}/actions/runs/{run.get('id')}/jobs?filter=latest"])
            if not isinstance(jobs, dict):
                continue
            for job in jobs.get("jobs", []):
                if label not in job.get("labels", []):
                    continue
                if job.get("status") != status:
                    continue
                age_min = (now - created).total_seconds() / 60.0
                row = JobRow(
                    workflow=run.get("name", "?"),
                    run_number=run.get("run_number", 0),
                    run_id=run.get("id", 0),
                    job_name=job.get("name", "?"),
                    status=status,
                    age_min=age_min,
                )
                if bucket == "in_progress":
                    result.in_progress.append(row)
                elif age_min > starve_minutes:
                    result.starved.append(row)
    return result


@dataclass
class Verdict:
    status: str = "OK"  # OK | ERROR -- fixe par evaluate()
    errors: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)


def evaluate(inv: RunnerInventory, st: Starvation, warn_floor: int) -> Verdict:
    v = Verdict()

    if inv.available:
        if not inv.online:
            v.errors.append(
                f"EXTINCTION: aucun runner online ne porte le label -- superviseur(s) mort(s) ? "
                f"(offline: {', '.join(inv.offline) or 'aucun'})"
            )
        elif len(inv.online) < warn_floor:
            v.warnings.append(
                f"perte partielle de capacite: {len(inv.online)} runner(s) online "
                f"(< {warn_floor}) : {', '.join(inv.online)} ; offline: {', '.join(inv.offline) or 'aucun'}"
            )
        else:
            v.notes.append(f"{len(inv.online)} runner(s) online: {', '.join(inv.online)}")
    else:
        v.notes.append(f"inventaire non lisible ({getattr(inv, 'reason', '')}) -- garde sur le seul symptome")

    if st.starved and not st.in_progress:
        oldest = max(r.age_min or 0 for r in st.starved)
        v.errors.append(
            f"STARVATION: {len(st.starved)} job(s) libelle queued > seuil (plus vieux: {oldest:.0f} min) "
            f"et AUCUN job in_progress -- la file ne drainne pas. Exemples: "
            + "; ".join(f"{r.workflow} #{r.run_number} ({r.job_name}, {r.age_min:.0f} min)" for r in st.starved[:5])
        )
    elif st.starved:
        v.notes.append(
            f"file profonde mais saine: {len(st.starved)} job(s) queued > seuil, "
            f"{len(st.in_progress)} job(s) in_progress -- capacite en train de drainer"
        )
    elif st.in_progress:
        v.notes.append(f"{len(st.in_progress)} job(s) in_progress, rien d'affame -- OK")
    else:
        v.notes.append("ni queue affamee ni job en cours -- OK")

    v.status = "ERROR" if v.errors else "OK"
    return v


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default=os.environ.get("REPO", DEFAULT_REPO))
    ap.add_argument("--label", default=os.environ.get("LABEL", DEFAULT_LABEL))
    ap.add_argument("--starve-minutes", type=float,
                    default=float(os.environ.get("STARVE_MINUTES", DEFAULT_STARVE_MINUTES)))
    ap.add_argument("--warn-floor", type=int, default=DEFAULT_WARN_FLOOR)
    ap.add_argument("--runs-cap", type=int, default=DEFAULT_RUNS_CAP)
    ap.add_argument("--json", action="store_true", help="sortie JSON du verdict")
    args = ap.parse_args()

    token = os.environ.get("RUNNERS_READ_PAT") or None
    inv = fetch_inventory(args.repo, args.label, token)
    st = fetch_starvation(args.repo, args.label, args.starve_minutes, args.runs_cap)
    v = evaluate(inv, st, args.warn_floor)

    payload = {
        "status": v.status,
        "errors": v.errors,
        "warnings": v.warnings,
        "notes": v.notes,
        "online_runners": inv.online if inv.available else None,
        "offline_runners": inv.offline if inv.available else None,
        "starved_jobs": [r.__dict__ for r in st.starved],
        "in_progress_jobs": len(st.in_progress),
    }
    if args.json:
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        for n in v.notes:
            print(f"[runner-starvation] {n}")
        for w in v.warnings:
            print(f"::warning::[runner-starvation] {w}")
        for e in v.errors:
            print(f"::error::[runner-starvation] {e}")

    return 1 if v.errors else 0


if __name__ == "__main__":
    sys.exit(main())
