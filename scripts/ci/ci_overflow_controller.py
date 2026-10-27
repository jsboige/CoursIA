#!/usr/bin/env python3
"""Controleur automatique de la variable de depot `CI_OVERFLOW_LOCAL`.

Volet 1 / **phase B** du debordement CI (#22937) : la phase A (#22921) a
pose la *forme hybride* des workflows -- une variable de depot unique decide
si un job part sur le parc local ou sur l'offre GitHub-hosted. La phase A est
**manuelle** (un operateur pose la variable) ; cette phase B la pilote.

Regle de decision (celle de l'arbitrage, pas une invention de l'organe) :

- offre hebergee **saturee** (jobs `ubuntu-latest` en file au-dela du seuil
  d'age) **et** parc local libre -> variable a `true` (le local absorbe le
  debordement) ;
- file hebergee **videe** -> variable a `false` (l'offre hebergee suffit, le
  local se libere) ;
- sinon -> **HOLD** (on ne touche a rien : une variable qui oscille est pire
  qu'une variable stable).

Garde de securite : si le **parc local est lui-meme affame** (des jobs
`coursia-linux` attendent), on ne bascule **pas** vers `true` -- on rend la
main a l'offre hebergee.

Le controleur est **fail-CLOSED** : une mesure illisible (API en erreur,
listing incomplet, inventaire des runners non lisible) ne produit **aucune**
ecriture -- un organe qui ne sait pas ne bascule pas.

PREREQUISIT (a installer par l'operateur, jamais suppose) : un jeton
(GitHub App installee ou PAT) dispose du droit **`variables: write`** sur le
depot. **Arbitrage (b) du coordinateur (c.6441695482, 27/10)** : ce jeton
n'est **pas** pose comme secret dans Actions -- le workflow automatise rend
un **verdict en lecture seule** et n'ecrit jamais. La bascule est un geste
d'operateur **ai-01**, joue en local avec le jeton `jsboige` pris commande
par commande :

    GH_TOKEN=$(gh auth token --user jsboige) \
      python scripts/ci/ci_overflow_controller.py --repo jsboige/CoursIA --apply

Sans jeton, l'organe rend `REFUSED` et **n'ecrit rien**.

Usage :

    # lecture seule, verdict seul (defaut : dry-run)
    python scripts/ci/ci_overflow_controller.py --repo jsboige/CoursIA

    # application effective
    python scripts/ci/ci_overflow_controller.py --repo jsboige/CoursIA --apply

Le cout de l'organe est borne : deux lectures de file, plafonnees par
`--job-budget` (defaut 120) et `--local-job-budget` (defaut 40) lectures de
jobs -- le volume d'appels API est justement l'objet du volet 5 de #22937, un
organe de controle ne doit pas en devenir la cause.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_runner_starvation as crs  # noqa: E402  (organe voisin, meme dossier)

EXIT_OK = 0
EXIT_UNREADABLE = 1
EXIT_REFUSED = 2

DEFAULT_REPO = "jsboige/CoursIA"
DEFAULT_VARIABLE = "CI_OVERFLOW_LOCAL"
HOSTED_LABEL = "ubuntu-latest"
LOCAL_LABEL = "coursia-linux"

# Seuil de saturation : au-dela de ce nombre de jobs hebergees en file
# depuis plus de `--saturation-minutes`, l'offre hebergee est saturee.
DEFAULT_SATURATION_JOBS = 3
DEFAULT_SATURATION_MINUTES = 15.0
# En dessous de ce nombre de jobs hebergees en file, l'offre hebergee est
# consideree comme videe (elle rend la main).
DEFAULT_DRAIN_JOBS = 0
# Nombre de slots locaux libres minimum pour accepter le debordement.
DEFAULT_MIN_FREE_SLOTS = 2
# Dwell : minimum entre deux bascules (anti-oscillation).
DEFAULT_DWELL_MINUTES = 30.0


@dataclass
class HostedSample:
    """Etat de l'offre GitHub-hosted, mesure."""

    queued: int = 0
    old: int = 0
    oldest_age_min: float = 0.0
    complete: bool = True
    reason: str = ""


@dataclass
class LocalSample:
    """Etat du parc local, mesure."""

    online: int = 0
    free: int = 0
    starved: int = 0
    complete: bool = True
    reason: str = ""


@dataclass
class Decision:
    """Verdict du controleur."""

    action: str  # SWITCH_TRUE | SWITCH_FALSE | HOLD | UNREADABLE
    reason: str
    current: str | None = None
    target: str | None = None
    details: dict = field(default_factory=dict)


def evaluate(
    hosted: HostedSample,
    local: LocalSample,
    current: str | None,
    *,
    saturation_jobs: int = DEFAULT_SATURATION_JOBS,
    saturation_minutes: float = DEFAULT_SATURATION_MINUTES,
    drain_jobs: int = DEFAULT_DRAIN_JOBS,
    min_free_slots: int = DEFAULT_MIN_FREE_SLOTS,
    dwell_minutes: float = DEFAULT_DWELL_MINUTES,
    last_change_at: datetime | None = None,
    now: datetime | None = None,
) -> Decision:
    """Decide de l'etat voulu de la variable. Fonction PURE (aucun appel).

    L'ordre des regles est significatif : la garde de securite (parc local
    affame) passe avant la saturation, sinon on enverrait du debordement vers
    un parc qui n'absorbe rien.
    """
    now = now or datetime.now(timezone.utc)

    if not hosted.complete or not local.complete:
        parts = []
        if not hosted.complete:
            parts.append(f"offre hebergee non mesuree ({hosted.reason})")
        if not local.complete:
            parts.append(f"parc local non mesure ({local.reason})")
        return Decision(
            action="UNREADABLE",
            reason=" ; ".join(parts) or "mesure incomplete",
            current=current,
            details={"hosted": hosted, "local": local},
        )

    def hold(reason: str, target: str | None = None) -> Decision:
        return Decision(
            action="HOLD",
            reason=reason,
            current=current,
            target=target,
            details={"hosted": hosted, "local": local},
        )

    def switch(target: str, reason: str) -> Decision:
        if target == current:
            return hold(f"deja a {target} -- {reason}", target)
        if (
            dwell_minutes > 0
            and last_change_at is not None
            and (now - last_change_at).total_seconds() < dwell_minutes * 60
        ):
            minutes = (now - last_change_at).total_seconds() / 60.0
            return hold(
                f"bascule vers {target} differee par le dwell "
                f"({minutes:.1f} min < {dwell_minutes:.0f} min depuis la "
                f"derniere ecriture) -- {reason}",
                target,
            )
        return Decision(
            action="SWITCH_TRUE" if target == "true" else "SWITCH_FALSE",
            reason=reason,
            current=current,
            target=target,
            details={"hosted": hosted, "local": local},
        )

    # 1. Garde de securite : le parc local est lui-meme affame.
    if local.starved > 0:
        return switch(
            "false",
            f"le parc local est lui-meme affame ({local.starved} job(s) "
            f"coursia-linux en file) -- on rend la main a l'offre hebergee",
        )

    # 2. Offre hebergee drainee : elle suffit, on libere le local.
    if hosted.queued <= drain_jobs:
        return switch(
            "false",
            f"file hebergee videe ({hosted.queued} job(s) en file) -- "
            f"l'offre GitHub suffit, le parc local se libere",
        )

    # 3. Offre hebergee saturee ET parc local libre : le local absorbe.
    if hosted.old >= saturation_jobs and local.free >= min_free_slots:
        return switch(
            "true",
            f"offre hebergee saturee ({hosted.old} job(s) en file depuis plus "
            f"de {saturation_minutes:.0f} min, plus ancien {hosted.oldest_age_min:.0f} min) "
            f"et parc local libre ({local.free} slot(s)) -- le local absorbe",
        )

    return hold(
        f"conditions non reunies : {hosted.old} job(s) heberge(s) en file "
        f"au-dela de {saturation_minutes:.0f} min (seuil {saturation_jobs}), "
        f"{local.free} slot(s) local(aux) libre(s) (seuil {min_free_slots})",
        None,
    )


def _gh_api(
    args: list[str],
    token: str | None = None,
    method: str | None = None,
    payload: dict | None = None,
) -> tuple[int, str, str]:
    """Appelle `gh api` et rend (code retour, stdout, stderr)."""
    env = dict(os.environ)
    if token:
        env["GH_TOKEN"] = token
    argv = ["gh", "api", *args]
    if method:
        argv[1:1] = ["--method", method]
    stdin = None
    if payload is not None:
        stdin = json.dumps(payload)
        argv[1:1] = ["--input", "-"]
    proc = subprocess.run(
        argv,
        input=stdin,
        capture_output=True,
        text=True,
        check=False,
        encoding="utf-8",
        errors="replace",
        env=env,
    )
    return proc.returncode, proc.stdout, proc.stderr


def read_variable(
    repo: str, name: str, token: str
) -> tuple[str | None, datetime | None, str]:
    """Lit la variable de depot. Rend (valeur, updated_at, motif d'echec)."""
    rc, out, err = _gh_api(
        [f"repos/{repo}/actions/variables/{name}"], token=token
    )
    if rc != 0:
        message = (err or out or "").strip().splitlines()
        return None, None, message[-1] if message else "lecture impossible"
    try:
        data = json.loads(out)
    except json.JSONDecodeError:
        return None, None, "reponse non-JSON"
    value = data.get("value")
    updated = data.get("updated_at")
    parsed = None
    if isinstance(updated, str):
        try:
            parsed = datetime.fromisoformat(updated.replace("Z", "+00:00"))
        except ValueError:
            parsed = None
    return (value if isinstance(value, str) else None), parsed, ""


def write_variable(repo: str, name: str, value: str, token: str) -> tuple[bool, str]:
    """Ecrit la variable de depot. Rend (succes, motif)."""
    payload = {"name": name, "value": value}
    rc, out, err = _gh_api(
        [f"repos/{repo}/actions/variables/{name}"],
        token=token,
        method="PATCH",
        payload=payload,
    )
    if rc == 0:
        return True, "variable mise a jour"
    message = (err or out or "").strip()
    if "404" in message or "Not Found" in message:
        # La variable n'existe pas encore : on la cree.
        rc2, out2, err2 = _gh_api(
            [f"repos/{repo}/actions/variables"],
            token=token,
            method="POST",
            payload=payload,
        )
        if rc2 == 0:
            return True, "variable creee"
        return False, (err2 or out2 or "creation refusee").strip()
    return False, message or "ecriture refusee"


def collect_hosted(
    repo: str,
    saturation_minutes: float,
    job_budget: int,
    now: datetime,
    token: str | None,
) -> HostedSample:
    """Mesure l'offre hebergee : jobs `ubuntu-latest` en file."""
    if token:
        os.environ["GH_TOKEN"] = token
    starv = crs.fetch_starvation(
        repo,
        HOSTED_LABEL,
        starve_minutes=0.0,
        now=now,
        job_read_budget=job_budget,
    )
    if not starv.complete:
        return HostedSample(
            complete=False,
            reason=(
                f"lecture de la file hebergee incomplete "
                f"({len(starv.listing_failed)} listing(s) en echec, "
                f"{starv.stats.failed} appel(s) en echec)"
            ),
        )
    rows = [row for row in starv.starved if row.age_min is not None]
    old = [row for row in rows if row.age_min > saturation_minutes]
    oldest = max((row.age_min for row in rows), default=0.0)
    return HostedSample(
        queued=len(rows),
        old=len(old),
        oldest_age_min=oldest,
        complete=True,
    )


def collect_local(
    repo: str,
    saturation_minutes: float,
    job_budget: int,
    now: datetime,
    token: str | None,
    measure_starvation: bool = True,
) -> LocalSample:
    """Mesure le parc local : slots libres, et affames si demande."""
    if token:
        os.environ["GH_TOKEN"] = token
    inv = crs.fetch_inventory(repo, LOCAL_LABEL, token)
    if not inv.available:
        return LocalSample(
            complete=False, reason=inv.reason or "inventaire des runners illisible"
        )
    starved = 0
    if measure_starvation:
        starv = crs.fetch_starvation(
            repo,
            LOCAL_LABEL,
            starve_minutes=saturation_minutes,
            now=now,
            job_read_budget=job_budget,
        )
        if not starv.complete:
            return LocalSample(
                online=len(inv.online),
                free=inv.free,
                complete=False,
                reason="lecture de la file locale incomplete",
            )
        starved = len(starv.starved)
    return LocalSample(
        online=len(inv.online),
        free=inv.free,
        starved=starved,
        complete=True,
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Pilote la variable de depot CI_OVERFLOW_LOCAL (phase B)."
    )
    parser.add_argument("--repo", default=DEFAULT_REPO)
    parser.add_argument("--variable", default=DEFAULT_VARIABLE)
    parser.add_argument("--token-env", default="GH_TOKEN")
    parser.add_argument(
        "--apply",
        action="store_true",
        help="ecrit la variable (defaut : dry-run, verdict seul)",
    )
    parser.add_argument("--saturation-jobs", type=int, default=DEFAULT_SATURATION_JOBS)
    parser.add_argument(
        "--saturation-minutes", type=float, default=DEFAULT_SATURATION_MINUTES
    )
    parser.add_argument("--drain-jobs", type=int, default=DEFAULT_DRAIN_JOBS)
    parser.add_argument("--min-free-slots", type=int, default=DEFAULT_MIN_FREE_SLOTS)
    parser.add_argument("--dwell-minutes", type=float, default=DEFAULT_DWELL_MINUTES)
    parser.add_argument("--job-budget", type=int, default=crs.DEFAULT_JOB_READ_BUDGET)
    parser.add_argument("--local-job-budget", type=int, default=40)
    parser.add_argument(
        "--no-local-starvation",
        action="store_true",
        help="ne mesure pas l'affamescence du parc local (garde secondaire)",
    )
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--now",
        help="instant de reference (ISO 8601) -- determinisme des tests",
    )
    args = parser.parse_args(argv)

    token = os.environ.get(args.token_env) or os.environ.get("GITHUB_TOKEN")
    if not token:
        message = (
            f"aucun jeton dans {args.token_env} ni GITHUB_TOKEN : le "
            f"controleur ne peut ni lire ni ecrire la variable. "
            f"Prerequisit : un jeton avec le droit `variables: write` sur "
            f"{args.repo} (GitHub App installee ou PAT), pris commande par "
            f"commande par l'operateur (arbitrage (b) : pas de secret dans "
            f"Actions -- le workflow automatise reste en lecture seule)."
        )
        if args.json:
            print(json.dumps({"verdict": "REFUSED", "reason": message}, indent=2))
        else:
            print(f"[ci-overflow] REFUSED -- {message}", file=sys.stderr)
        return EXIT_REFUSED

    now = (
        datetime.fromisoformat(args.now.replace("Z", "+00:00"))
        if args.now
        else datetime.now(timezone.utc)
    )

    current, updated_at, read_error = read_variable(args.repo, args.variable, token)
    if current is None and read_error:
        message = (
            f"lecture de la variable {args.variable} impossible : {read_error}. "
            f"Le jeton a-t-il le droit `variables: read` ?"
        )
        if args.json:
            print(json.dumps({"verdict": "REFUSED", "reason": message}, indent=2))
        else:
            print(f"[ci-overflow] REFUSED -- {message}", file=sys.stderr)
        return EXIT_REFUSED

    hosted = collect_hosted(
        args.repo, args.saturation_minutes, args.job_budget, now, token
    )
    local = collect_local(
        args.repo,
        args.saturation_minutes,
        args.local_job_budget,
        now,
        token,
        measure_starvation=not args.no_local_starvation,
    )

    decision = evaluate(
        hosted,
        local,
        current,
        saturation_jobs=args.saturation_jobs,
        saturation_minutes=args.saturation_minutes,
        drain_jobs=args.drain_jobs,
        min_free_slots=args.min_free_slots,
        dwell_minutes=args.dwell_minutes,
        last_change_at=updated_at,
        now=now,
    )

    written = False
    write_error = ""
    if decision.action in ("SWITCH_TRUE", "SWITCH_FALSE") and args.apply:
        ok, write_error = write_variable(
            args.repo, args.variable, decision.target or "false", token
        )
        written = ok
        if not ok:
            decision.action = "REFUSED"
            decision.reason = f"ecriture refusee : {write_error}"

    report = {
        "verdict": decision.action,
        "reason": decision.reason,
        "repo": args.repo,
        "variable": args.variable,
        "current": decision.current,
        "target": decision.target,
        "written": written,
        "mode": "apply" if args.apply else "dry-run",
        "hosted": {
            "queued": hosted.queued,
            "old": hosted.old,
            "oldest_age_min": round(hosted.oldest_age_min, 1),
            "complete": hosted.complete,
            "reason": hosted.reason,
        },
        "local": {
            "online": local.online,
            "free": local.free,
            "starved": local.starved,
            "complete": local.complete,
            "reason": local.reason,
        },
        "thresholds": {
            "saturation_jobs": args.saturation_jobs,
            "saturation_minutes": args.saturation_minutes,
            "drain_jobs": args.drain_jobs,
            "min_free_slots": args.min_free_slots,
            "dwell_minutes": args.dwell_minutes,
        },
    }
    if write_error:
        report["write_error"] = write_error

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(
            f"[ci-overflow] {decision.action} -- {decision.reason}\n"
            f"  hebergee : {hosted.queued} job(s) en file "
            f"({hosted.old} de plus de {args.saturation_minutes:.0f} min, "
            f"plus ancien {hosted.oldest_age_min:.0f} min)\n"
            f"  local    : {local.online} slot(s) en ligne, {local.free} libre(s), "
            f"{local.starved} affame(s)\n"
            f"  variable : {decision.current} -> {decision.target} "
            f"({'ecrit' if written else 'non ecrit'})"
        )

    if decision.action == "UNREADABLE":
        return EXIT_UNREADABLE
    if decision.action == "REFUSED":
        return EXIT_REFUSED
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
