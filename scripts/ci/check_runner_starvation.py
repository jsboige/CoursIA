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

FENETRE D'EXAMEN (correctif fail-open, signe par po-2025 / relais CoursIA-2,
2026-09-02) : l'API rend les runs du plus recent au plus ancien. Une lecture
cappee aux N premiers rend exactement ceux qui n'ont pas eu le temps de
starver -- mesure du jour : 34 runs queued > 15 min, tous en pages 6-7,
tous invisibles au cap=30 (dont des runs abandonnes a ~14 jours). La
collecte pagine donc jusqu'a WINDOW_MAX_MINUTES (les runs plus vieux sont
la classe ABANDONNEE, notee sans jamais rougir : rougir dessus serait le
rouge permanent que la garde anti-FP interdit). L'age d'un job s'ancre sur
jobs[].created_at (un job debloque tard par needs: a attendu moins que le
run n'est vieux), avec repli sur run.created_at. Chaque job est classe par
SON PROPRE statut sur l'union dedupliquee des runs queued/in_progress : un
run in_progress peut porter un job du label reste queued (extinction ciblee
de la jambe Linux pendant que les autres jobs du run progressent) -- le
classer par le statut du run le rendait invisible aux deux passes.

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
DEFAULT_WINDOW_MAX_MINUTES = 360.0
RUNS_PAGE_SIZE = 100


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
    # runs non examines car plus vieux que la fenetre (classe abandonnee) :
    # comptes d'information, jamais un rouge -- cf docstring.
    unexamined: dict[str, int] = field(default_factory=dict)


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


def fetch_starvation(
    repo: str,
    label: str,
    starve_minutes: float,
    window_max_minutes: float = DEFAULT_WINDOW_MAX_MINUTES,
    now: datetime | None = None,
) -> Starvation:
    now = now or datetime.now(timezone.utc)
    result = Starvation()

    # Union dedupliquee des runs queued + in_progress, chaque JOB classe par
    # SON PROPRE statut (faux negatif reproduit par po-2025, 2026-09-02 : un
    # run in_progress peut porter un job coursia-linux reste queued --
    # extinction ciblee de la jambe Linux pendant que les jobs GitHub-hosted
    # du meme run progressent ; le classer par le statut du RUN le rendait
    # invisible aux deux passes). Un run peut transiter queued -> in_progress
    # ENTRE les deux passes : il faut donc re-examiner ses jobs au second
    # passage -- la dedup vit au niveau JOB (cle run_id+job.id, repli nom),
    # l'observation la plus recente REMPLACE TOUTE observation anterieure, y
    # compris vers un etat terminal : un job vu queued puis completed au
    # second passage quitte la liste des affames (sinon faux positif apres
    # drain, repro adjoint 2026-09-02 11:23Z) ; seuls queued/in_progress
    # sont reinseres.
    seen_runs: set[int] = set()
    seen_jobs: dict[tuple[int, str], JobRow] = {}
    # Traçage des listings pour la re-verification du residuel adjoint
    # (2026-09-02 14:24Z) : un run observe au tour queued mais absent des deux
    # listings du tour in_progress a pu devenir terminal ENTRE les deux
    # queries -- sa re-verification directe tranche (voir plus bas).
    listing_failed: set[str] = set()
    listing_seen: dict[int, set[str]] = {}
    for status in ("queued", "in_progress"):
        # Query params inline : `-f` forcerait un POST sur un endpoint GET.
        page = 1
        total: int | None = None
        examined = 0
        while True:
            runs = _gh_json(
                [f"repos/{repo}/actions/runs?status={status}"
                 f"&per_page={RUNS_PAGE_SIZE}&page={page}"]
            )
            if not isinstance(runs, dict):
                listing_failed.add(status)
                break
            if total is None:
                raw_total = runs.get("total_count")
                if isinstance(raw_total, int):
                    total = raw_total
            workflow_runs = runs.get("workflow_runs", [])
            if not workflow_runs:
                break
            # Pages triees du plus recent au plus ancien : des que le PLUS
            # RECENT de la page depasse la fenetre, toutes les suivantes sont
            # plus vieilles -- arret premature, le cout reste borne par la
            # fenetre et non par la profondeur de la file.
            newest = _parse_iso(workflow_runs[0].get("created_at"))
            if newest is not None and (now - newest).total_seconds() / 60.0 > window_max_minutes:
                break
            last_page = len(workflow_runs) < RUNS_PAGE_SIZE
            for run in workflow_runs:
                created = _parse_iso(run.get("created_at"))
                if created is None:
                    continue
                run_age = (now - created).total_seconds() / 60.0
                if run_age > window_max_minutes:
                    # Classe ABANDONNEE, pas affamee : hors predicat (rouge
                    # permanent sinon, cf docstring). Comptee, jamais examinee.
                    continue
                rid = run.get("id")
                if rid not in seen_runs:
                    seen_runs.add(rid)
                    examined += 1
                listing_seen.setdefault(rid, set()).add(status)
                jobs = _gh_json([f"repos/{repo}/actions/runs/{rid}/jobs?filter=latest"])
                if not isinstance(jobs, dict):
                    continue
                for job in jobs.get("jobs", []):
                    if label not in job.get("labels", []):
                        continue
                    # Retrait AVANT filtration terminale : toute observation
                    # d'un job du label retire sa classification anterieure.
                    # Sans ce retrait un job vu queued au 1er passage puis
                    # completed/cancelled au 2eme resterait artificiellement
                    # starved apres drain (repro adjoint po-2025, 11:23Z).
                    # Cle stable : job.id, repli documente sur job.name.
                    key = (rid or 0, job.get("id") if job.get("id") is not None else job.get("name") or "?")
                    old = seen_jobs.pop(key, None)
                    if old is not None:
                        if old in result.starved:
                            result.starved.remove(old)
                        if old in result.in_progress:
                            result.in_progress.remove(old)
                    job_status = job.get("status")
                    if job_status not in ("queued", "in_progress"):
                        continue
                    # Ancrage par JOB : un job debloque tard (needs:, matrice
                    # differree) a attendu moins que le run n'est vieux --
                    # l'age run serait un faux positif, sens inverse du
                    # fail-open de la fenetre.
                    anchor = _parse_iso(job.get("created_at")) or created
                    age_min = (now - anchor).total_seconds() / 60.0
                    row = JobRow(
                        workflow=run.get("name", "?"),
                        run_number=run.get("run_number", 0),
                        run_id=rid or 0,
                        job_name=job.get("name", "?"),
                        status=job_status,
                        age_min=age_min,
                    )
                    seen_jobs[key] = row
                    if job_status == "queued":
                        if age_min > starve_minutes:
                            result.starved.append(row)
                    else:
                        result.in_progress.append(row)
            if last_page:
                break
            page += 1
            # Garde cout : au-dela de 20 pages (2000 runs) dans la fenetre,
            # la file est un incident de profondeur, pas de pagination.
            if page > 20:
                result.unexamined[status] = max(
                    (total or examined) - examined, 0
                )
                break
        if isinstance(total, int) and total > examined and status not in result.unexamined:
            result.unexamined[status] = total - examined

    # Residuel adjoint (po-2025:CoursIA-2, 2026-09-02 14:24Z) : un run observe
    # au tour queued qui transite vers un etat terminal ENTRE les deux listing
    # queries disparait du snapshot 2 -- son job n'est jamais re-observe et
    # l'entree starved du pass 1 survivait (`starved=[('guard-linux','queued',
    # 40.0)]`). Re-verification bornee : chaque run vu SEULEMENT au tour queued
    # et porteur d'une entree vivante est re-interroge directement (une query
    # run, pas ses jobs) ; `status == completed` purge ses entrees -- semantique
    # "l'observation la plus recente gagne" -- tout autre statut les conserve.
    # Fail-open : si UN listing a echoue, aucun purgement (un run invisible par
    # panne d'API n'est pas un run terminal prouve) ; idem si la query directe
    # echoue. Un run queued stable, re-verifie puis encore queued, garde son
    # entree : purger sans re-verifier rendrait l'organe muet sous vraie file
    # profonde.
    if not listing_failed:
        for row in [*result.starved, *result.in_progress]:
            if listing_seen.get(row.run_id) != {"queued"}:
                continue
            run = _gh_json([f"repos/{repo}/actions/runs/{row.run_id}"])
            if isinstance(run, dict) and run.get("status") == "completed":
                if row in result.starved:
                    result.starved.remove(row)
                if row in result.in_progress:
                    result.in_progress.remove(row)
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

    unq = st.unexamined.get("queued", 0)
    if unq:
        v.notes.append(
            f"{unq} run(s) queued plus vieux que la fenetre d'examen -- classe "
            f"ABANDONNEE (hygiene de file), pas extinction : hors predicat, "
            f"jamais un rouge. Cf pr-gate-stale-sweep / cancel-organs."
        )

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
    ap.add_argument("--window-max-minutes", type=float,
                    default=float(os.environ.get("WINDOW_MAX_MINUTES", DEFAULT_WINDOW_MAX_MINUTES)),
                    help="fenetre d'examen ; les runs queued plus vieux sont "
                         "la classe ABANDONNEE, notes sans rouge")
    ap.add_argument("--json", action="store_true", help="sortie JSON du verdict")
    args = ap.parse_args()

    token = os.environ.get("RUNNERS_READ_PAT") or None
    inv = fetch_inventory(args.repo, args.label, token)
    st = fetch_starvation(
        args.repo, args.label, args.starve_minutes,
        window_max_minutes=args.window_max_minutes,
    )
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
        "unexamined_runs": st.unexamined,
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
