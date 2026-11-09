#!/usr/bin/env python3
r"""Scheduler liveness organ (#15332) -- measure the SERVED cadence of the
``schedule`` event class, and survive the outage it observes.

## Why

Measured 2026-09-09: the last ``event=schedule`` run of the ENTIRE repository is
``2026-09-09T01:13:03Z``; four hours later nothing planned had fired, while the
workflows stayed ``state=active`` and merges kept flowing. What stopped was the
DELIVERY of the ``schedule`` event, not its execution.

``pr-gate-sweep-health-advisory.yml`` already watches ONE organ (the age of the
last successful ``pr-gate-stale-sweep`` run). Two limits, both named by #15332:

  1. the observer is itself carried by a ``schedule:`` -- it dies of the same
     cause it exists to report (it went quiet at 01:13Z like everything else);
  2. it compares the age of ONE organ to a declared window, and nothing ever
     measures the gap between the DECLARED cadence (``7 * * * *``) and the
     SERVED one (~2.5-3.5 h observed, #15332). A cadence that is never served
     as written never goes red -- until it reaches zero, which is too late.

This organ answers (2) for a small registry of critical scheduled workflows and
renders the served-vs-declared ratio. The ``push`` heartbeat added to the
advisory workflow answers (1): merges keep flowing while the scheduler is mute,
so a push-triggered run still happens during the exact failure it reports.

## What it does NOT do

No red on a degraded-but-alive cadence. A permanently red organ on a chronic
condition gets ignored -- the repository's own doctrine. Age predicates decide
the verdict (OK / LATE / DEAD); the served-vs-declared ratio is rendered as a
NAMED WARNING and left to the human/coordinator read.

## Verdicts

  - ``OK``      : last scheduled run within 2x the declared interval
  - ``LATE``    : within 2x-4x (degraded delivery; visible, not red)
  - ``DEAD``    : beyond max(4x declared, 90 min) -- or no scheduled run at all
                  in history. THIS is what reddens the step (exit 1) -- sauf en
                  mode ``--dead-exit warning``, ou il est nomme et laisse le
                  step vert (cf. le paragraphe suivant).
  - ``DISABLED``: l'age dirait DEAD, mais le workflow est **desactive** a la
                  source (``state`` non actif) -- un workflow desactive ne
                  recoit plus ni ``schedule`` ni ``workflow_run``, donc l'age ne
                  mesure plus une panne de livraison (cf. la section suivante).
  - ``UNKNOWN`` : the gh probe itself failed for that organ -- named, never
                  silently folded into OK or DEAD.

Control against a dead instrument: if EVERY organ returns UNKNOWN or zero runs,
the probe -- not the scheduler -- is the suspect, and the organ exits 1 with
``INSTRUMENT_UNKNOWN`` rather than reporting a fleet-wide green.

## Workflow desactive != cron mort (#22937, volet 6)

Mesure du 2026-10-24T11:46:51Z : ``linux-runner-starvation-advisory.yml`` et
``coursia-waiter-starvation-advisory.yml`` ont ete passes en
``state: "disabled_manually"`` par un operateur, a une seconde d'intervalle. Un
workflow desactive ne recoit PLUS ni ``schedule`` ni ``workflow_run`` : son
dernier run vieillit mecaniquement, et l'organe rendait donc
``DEAD linux-runner-starvation-advisory.yml declare 30 min | servi 291 min |
dernier run 4324 min`` -- un cron mort, alors que la cause est un geste
d'operateur. Deux causes, deux remedes : reactiver le workflow n'est pas la meme
action que reparer une livraison d'evenements.

**Suite (2026-10-27T12:50Z)** : les deux advisories ont ete **reactives**
(arbitrage (a) du coordinateur, c.6441695482 -- la desactivation du 24/10
n'avait pas de trace ecrite du motif). L'organe garde le verdict ``DISABLED``
pour l'avenir : la desactivation **manuale** reste un geste qui doit rester
visible, et la lecture d'etat est ce qui la rend visible. La seconde des deux
advisories (``coursia-waiter-starvation-advisory.yml``) a ete ajoutee au
registre des organes surveilles dans le meme temps.

L'organe lit donc, pour chaque organe evalue, ``state`` et ``updated_at`` via
``GET /repos/{owner}/{repo}/actions/workflows/{file}``. Un ``state`` qui suspend
les declencheurs automatiques (``disabled_manually``, ``disabled_inactivity``)
rend ``DISABLED`` -- meme priorite d'affichage et meme severite qu'un ``DEAD``
(``--dead-exit`` s'y applique a l'identique, pour la meme raison qu'au #18292 :
un etat chronique recopie en rouge sur la jambe ``push`` masque les vrais
rouges), et la ligne nomme ``updated_at``, c'est-a-dire la date du geste.

La lecture d'etat est un **enrichissement**, jamais une source de verdict :

  - un workflow ``active`` garde son verdict d'age -- un cron qui ne livre plus
    reste ``DEAD``, la cause premiere que cet organe existe pour voir ;
  - un appel REST en echec (403 / 404 / timeout) ne fabrique NI ``DISABLED`` NI
    un ``DEAD`` : le verdict d'age est conserve tel quel et l'echec est nomme
    (``WARN etat du workflow illisible``). Un read fail-open qui sur-accuse est
    interdit ; un read fail-close qui bloque l'organe l'est aussi.

## Severite d'un DEAD : deux modes, jamais un seuil deplace (#18292)

Mesure du 2026-09-28 : la livraison ``schedule`` de GitHub sert les crons a 30 et
60 min toutes les ~4 h 30 depuis le 09/09 (#15332), donc un DEAD est CHRONIQUE
et non un incident. Recopie en rouge sur la jambe ``push``, il rougissait **37
des 45 commits** de ``main`` du jour, sans qu'aucun de ces commits ne soit
cassee -- et un rouge sur presque chaque commit masque les vrais rouges, ce que
la docstring ci-dessus dit vouloir eviter.

``--dead-exit warning`` nomme le DEAD (``::warning::``) et laisse le step vert.
Le **verdict est inchange** (``evaluate`` ne bouge pas) et aucun seuil ne monte :
seule la severite imprimee change, et elle se choisit **par jambe** dans le
workflow -- ``push`` en avertissement, ``schedule`` et ``workflow_dispatch``
en rouge. ``INSTRUMENT_UNKNOWN`` garde son rouge dans les deux modes : c'est la
mesure qui est en panne, pas la cadence qu'on excuse.

## Sweep du meme push (#18292)

``sweep_run_alive_for_sha`` repond a une course, pas a une cadence : la jambe
``push`` de l'advisory et celle du sweep partent du meme commit, donc la sonde
d'age -- qui cherche le dernier succes TERMINE -- trouve celui du merge
precedent et rougit un commit dont le sweep tourne encore (instance : run
``36461754953``, sweep ``36461754984``, meme ``head_sha``).
"""
from __future__ import annotations

import argparse
import json
import os
import statistics
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone

LATE_FACTOR = 2
DEAD_FACTOR = 4
DEAD_FLOOR_MIN = 90.0

# Etats de workflow qui suspendent les declencheurs AUTOMATIQUES (#22937 volet 6).
# `disabled_manually` = geste d'operateur ; `disabled_inactivity` = desactivation
# automatique par GitHub apres 60 jours sans activite. Les deux font taire
# `schedule` et `workflow_run`, donc les deux rendent l'age muet sur la CAUSE.
TRIGGER_SUSPENDING_STATES = ("disabled_manually", "disabled_inactivity")

SAMPLE_LIMIT = 20


@dataclass(frozen=True)
class Organ:
    workflow: str
    declared_min: float
    note: str = ""


# Declared cadences read firsthand from each workflow file's `cron:` line.
# KEEP IN SYNC with the `cron:` lines of the workflows listed below: this
# table is a hand-copied snapshot, nothing verifies it against the files. A
# future `cron:` change in any listed workflow diverges SILENTLY -- the
# declared column here would mis-state the cadence (and mis-scale LATE/DEAD
# floors) without failing anything. Update this table in the same PR that
# touches any of these `cron:` lines.
REGISTRY: tuple[Organ, ...] = (
    Organ("pr-gate-stale-sweep.yml", 60.0, "cron '7 * * * *'"),
    # #22946 (point 3 de la review ai-01 du 2026-10-27) : le controleur de
    # debordement declarait '23,53', exactement le cron de
    # linux-runner-version-pin-advisory.yml -- il prend desormais une minute
    # libre, hors :00/:30, et entre dans ce registre pour que son extinction
    # se mesure au lieu de se supposer.
    Organ("ci-overflow-controller.yml", 60.0, "cron '31 * * * *'"),
    Organ("pr-gate-sweep-health-advisory.yml", 30.0, "cron '13,43 * * * *' -- cet observateur"),
    Organ("linux-runner-starvation-advisory.yml", 30.0, "cron '19,49 * * * *'"),
    Organ("coursia-waiter-starvation-advisory.yml", 30.0, "cron '11,41 * * * *'"),
    Organ("stale-guard-red-sweep.yml", 1440.0, "cron '53 4 * * *'"),
    Organ("epic-neglect-sweep.yml", 1440.0, "cron '37 8 * * *'"),
    Organ("grain-orphans-sweep.yml", 1440.0, "cron '23 7 * * *'"),
)


@dataclass
class Liveness:
    organ: Organ
    verdict: str
    age_min: float | None = None
    served_min: float | None = None
    n_runs: int = 0
    detail: str = ""
    warnings: list[str] = field(default_factory=list)
    # Etat du workflow lu a la source (#22937 volet 6). "" = non lu / illisible :
    # l'absence d'etat n'est jamais une preuve de desactivation.
    workflow_state: str = ""
    state_updated_at: str = ""


def parse_times(payload: str) -> list[datetime]:
    """Scheduled run creation times, newest first. Raises on malformed payload."""
    runs = json.loads(payload)
    times: list[datetime] = []
    for run in runs:
        created = (run.get("createdAt") or "").replace("Z", "+00:00")
        if not created:
            continue
        times.append(datetime.fromisoformat(created))
    times.sort(reverse=True)
    return times


def served_interval_minutes(times: list[datetime]) -> float | None:
    """Median gap between consecutive scheduled runs -- the SERVED cadence.

    None when fewer than two runs exist: one point carries no interval, and
    inventing one from a declared number would be the very error this organ
    exists to catch.
    """
    if len(times) < 2:
        return None
    gaps = [
        (times[i] - times[i + 1]).total_seconds() / 60.0
        for i in range(len(times) - 1)
    ]
    return statistics.median(gaps)


def verdict_for(age_min: float, declared_min: float) -> str:
    dead_after = max(declared_min * DEAD_FACTOR, DEAD_FLOOR_MIN)
    if age_min > dead_after:
        return "DEAD"
    if age_min > declared_min * LATE_FACTOR:
        return "LATE"
    return "OK"


def evaluate(organ: Organ, times: list[datetime], now: datetime) -> Liveness:
    """Pure verdict for one organ against its scheduled history."""
    if not times:
        return Liveness(
            organ=organ,
            verdict="DEAD",
            n_runs=0,
            detail=(
                "aucun run planifie dans l'historique -- livraison de l'evenement "
                "'schedule' interrompue pour cet organe (#15332)"
            ),
        )
    age_min = (now - times[0]).total_seconds() / 60.0
    served = served_interval_minutes(times)
    verdict = verdict_for(age_min, organ.declared_min)
    result = Liveness(
        organ=organ,
        verdict=verdict,
        age_min=age_min,
        served_min=served,
        n_runs=len(times),
    )
    if served is not None and served > organ.declared_min * LATE_FACTOR:
        result.warnings.append(
            f"cadence SERVIE degradee: {served:.0f} min observes entre runs "
            f"vs {organ.declared_min:.0f} min declares (ratio {served / organ.declared_min:.1f}x)"
        )
    return result


# --- etat du workflow : desactive != cron mort (#22937 volet 6) --------------


def probe_workflow_state(repo: str, workflow: str) -> tuple[dict | None, str]:
    """(payload, error). payload est None quand la sonde elle-meme a echoue.

    Ne leve jamais : un 403 / 404 / timeout rend ``(None, motif)`` et c'est
    l'appelant qui decide d'un verdict neutre -- jamais un ``DISABLED`` ni un
    ``DEAD`` forge a partir d'une lecture ratee.
    """
    cmd = ["gh", "api", f"repos/{repo}/actions/workflows/{workflow}"]
    try:
        out = subprocess.run(
            cmd, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=60
        )
    except (OSError, subprocess.SubprocessError) as exc:
        return None, f"sonde d'etat gh indisponible: {type(exc).__name__}"
    if out.returncode != 0:
        err = (out.stderr or "").strip().splitlines()
        return None, f"gh rc={out.returncode}: {err[0] if err else 'sans message'}"
    try:
        payload = json.loads(out.stdout or "{}")
    except (ValueError, TypeError) as exc:
        return None, f"payload d'etat illisible: {type(exc).__name__}"
    if not isinstance(payload, dict) or not isinstance(payload.get("state"), str):
        return None, "payload d'etat illisible: champ 'state' absent"
    return payload, ""


def apply_workflow_state(result: Liveness, payload: dict | None, error: str) -> Liveness:
    """Applique l'etat du workflow au verdict d'age -- dans UN sens seulement.

    ``DEAD`` dont le workflow est desactive devient ``DISABLED`` : la cause cesse
    d'etre la livraison des evenements et devient un geste d'operateur (ou une
    desactivation d'inactivite), et les deux remedes n'ont rien a voir.

    Ce que cette fonction ne fait JAMAIS :

      - promouvoir un workflow ``active`` : un cron qui ne livre plus reste
        ``DEAD``, c'est la cause premiere que l'organe existe pour voir ;
      - fabriquer un verdict depuis une lecture ratee : si ``payload`` est None,
        le verdict d'age est conserve tel quel et l'echec est nomme. Un appel
        REST en 403/404/timeout ne rend donc ni ``DISABLED`` ni un faux ``DEAD``,
        et il ne bloque pas l'organe non plus.

    Le cas non-``DEAD`` d'un workflow desactive est nomme en avertissement : le
    dernier run est encore frais, mais le workflow ne livrera plus jamais.
    """
    if payload is None:
        result.warnings.append(
            f"etat du workflow illisible ({error}) -- cause NON tranchee entre "
            "cron mort et desactivation (#22937), le verdict d'age est conserve"
        )
        return result

    state = str(payload.get("state") or "")
    result.workflow_state = state
    result.state_updated_at = str(payload.get("updated_at") or "")

    if state not in TRIGGER_SUSPENDING_STATES:
        if state and state != "active":
            result.warnings.append(
                f"etat de workflow inhabituel: {state!r} -- traite comme actif, "
                "verdict d'age conserve (#22937)"
            )
        return result

    when = result.state_updated_at or "date inconnue"
    if result.verdict == "DEAD":
        result.verdict = "DISABLED"
        result.detail = (
            f"workflow DESACTIVE (state={state}, updated_at={when}) -- un workflow "
            "desactive ne recoit plus ni 'schedule' ni 'workflow_run': l'age du "
            "dernier run ne mesure donc PAS une panne de livraison (#22937 volet 6)"
        )
        cause = (
            "desactivation d'operateur"
            if state == "disabled_manually"
            else "desactivation automatique (inactivite)"
        )
        result.warnings.append(
            f"{cause}: reactiver le workflow s'il doit livrer "
            f"(gh workflow enable {result.organ.workflow} --repo <owner>/<repo>)"
        )
    else:
        freshness = (
            f"alors que son dernier run est encore frais ({result.age_min:.0f} min)"
            if result.age_min is not None
            else "et son historique est vide"
        )
        result.warnings.append(
            f"workflow DESACTIVE (state={state}, updated_at={when}) {freshness} "
            "-- il ne livrera plus, le verdict d'age basculera en DISABLED (#22937)"
        )
    return result


def render(results: list[Liveness]) -> list[str]:
    lines = ["[scheduler-liveness] livraison de l'evenement 'schedule' (#15332)", ""]
    for r in results:
        age = f"{r.age_min:.0f} min" if r.age_min is not None else "n/a"
        served = f"{r.served_min:.0f} min" if r.served_min is not None else "n/a"
        lines.append(
            f"  {r.verdict:<8} {r.organ.workflow:<42} "
            f"declare {r.organ.declared_min:>6.0f} min | servi {served:>8} | "
            f"dernier run {age:>8} | {r.n_runs} runs"
        )
        for w in r.warnings:
            lines.append(f"          WARN {w}")
        if r.verdict in ("DEAD", "DISABLED", "UNKNOWN") and r.detail:
            lines.append(f"          {r.detail}")
    return lines


def probe(repo: str, workflow: str) -> tuple[list[datetime] | None, str]:
    """(times, error). times is None when the probe itself failed."""
    cmd = [
        "gh", "run", "list", "--repo", repo, "--workflow", workflow,
        "--event", "schedule", "--limit", str(SAMPLE_LIMIT),
        "--json", "createdAt",
    ]
    try:
        out = subprocess.run(
            cmd, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=120
        )
    except (OSError, subprocess.SubprocessError) as exc:
        return None, f"sonde gh indisponible: {type(exc).__name__}"
    if out.returncode != 0:
        err = (out.stderr or "").strip().splitlines()
        return None, f"gh rc={out.returncode}: {err[0] if err else 'sans message'}"
    try:
        return parse_times(out.stdout or "[]"), ""
    except (ValueError, TypeError) as exc:
        return None, f"payload illisible: {type(exc).__name__}"


# --- Sweep du meme push (#18292) -------------------------------------------

SWEEP_WORKFLOW = "pr-gate-stale-sweep.yml"

# Etats de file d'Actions qui rendent (ou vont rendre) le service. `completed`
# est traite a part : il ne vaut service que sur `success`.
LIVE_RUN_STATES = ("queued", "in_progress", "waiting", "pending", "requested")


def sweep_run_alive_for_sha(runs: list[dict], sha: str) -> tuple[bool, str]:
    """Un run du sweep porte-t-il CE commit, et rend-il (ou va-t-il rendre) le service ?

    Vivant = ``queued``/``in_progress`` (le service va etre rendu) ou
    ``completed``+``success`` (il vient de l'etre). Un run ``completed`` non
    reussi ne compte PAS : un sweep en echec ne vaut pas service rendu, et la
    sonde d'age doit garder le droit de rougir. Plusieurs runs peuvent porter le
    meme ``head_sha`` (relances) : le premier vivant suffit.
    """
    for run in runs:
        if (run.get("headSha") or "") != sha:
            continue
        status = (run.get("status") or "").lower()
        conclusion = (run.get("conclusion") or "").lower()
        if status in LIVE_RUN_STATES:
            return True, status
        if status == "completed" and conclusion == "success":
            return True, "completed/success"
    return False, ""


def probe_sweep_runs(repo: str) -> tuple[list[dict] | None, str]:
    """(runs, error). runs est None quand la sonde elle-meme a echoue."""
    cmd = [
        "gh", "run", "list", "--repo", repo, "--workflow", SWEEP_WORKFLOW,
        "--limit", str(SAMPLE_LIMIT), "--json", "headSha,status,conclusion",
    ]
    try:
        out = subprocess.run(
            cmd, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=120
        )
    except (OSError, subprocess.SubprocessError) as exc:
        return None, f"sonde gh indisponible: {type(exc).__name__}"
    if out.returncode != 0:
        err = (out.stderr or "").strip().splitlines()
        return None, f"gh rc={out.returncode}: {err[0] if err else 'sans message'}"
    try:
        runs = json.loads(out.stdout or "[]")
    except (ValueError, TypeError) as exc:
        return None, f"payload illisible: {type(exc).__name__}"
    if not isinstance(runs, list):
        return None, "payload illisible: liste de runs attendue"
    return runs, ""


def sweep_alive_verdict(repo: str, sha: str) -> int:
    """0 = sweep vivant pour ce commit, 3 = pas vivant, 4 = sonde en echec.

    3 et 4 laissent la jambe retomber sur le critere d'age : le mode ne remplace
    pas la sonde d'age, il lui retire un faux positif de course.
    """
    runs, error = probe_sweep_runs(repo)
    if runs is None:
        print(
            f"[sweep-health] sonde des runs de {SWEEP_WORKFLOW} en echec ({error}) "
            "-- repli sur le critere d'age",
            file=sys.stderr,
        )
        return 4
    alive, state = sweep_run_alive_for_sha(runs, sha)
    if alive:
        print(
            f"[sweep-health] un run de {SWEEP_WORKFLOW} porte ce commit ({state}) "
            "-- sweep vivant, l'age n'est pas juge"
        )
        return 0
    print(
        f"[sweep-health] aucun run vivant de {SWEEP_WORKFLOW} pour ce commit "
        "-- repli sur le critere d'age"
    )
    return 3


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Scheduler liveness (#15332)")
    ap.add_argument("--repo", default=os.environ.get("REPO", "jsboige/CoursIA"))
    ap.add_argument("--json", action="store_true", help="sortie machine")
    ap.add_argument(
        "--dead-exit",
        choices=("error", "warning"),
        default="error",
        help=(
            "severite d'un verdict DEAD ou DISABLED : 'error' (defaut, exit 1) ou "
            "'warning' (::warning:: nomme, exit 0). Ne deplace AUCUN seuil et ne change "
            "aucun verdict -- separe seulement le rouge de la jambe `push` de "
            "celui des jambes `schedule`/`workflow_dispatch` (#18292). Les deux "
            "verdicts sont chroniques et suivent donc la meme severite (#22937)."
        ),
    )
    ap.add_argument(
        "--sweep-alive-for-sha",
        metavar="SHA",
        default=None,
        help=(
            "mode sonde de course (#18292) : 0 si un run de "
            f"{SWEEP_WORKFLOW} porte ce commit et est vivant, 3 sinon, "
            "4 si la sonde echoue"
        ),
    )
    args = ap.parse_args(argv)

    if args.sweep_alive_for_sha:
        return sweep_alive_verdict(args.repo, args.sweep_alive_for_sha)

    now = datetime.now(timezone.utc)
    results: list[Liveness] = []
    for organ in REGISTRY:
        times, error = probe(args.repo, organ.workflow)
        if times is None:
            result = Liveness(organ=organ, verdict="UNKNOWN", detail=error)
        else:
            result = evaluate(organ, times, now)
        # Etat du workflow lu a la source : il explique un DEAD, il ne le cree pas
        # et ne l'efface pas (#22937 volet 6).
        state_payload, state_error = probe_workflow_state(args.repo, organ.workflow)
        results.append(apply_workflow_state(result, state_payload, state_error))

    unknown = [r for r in results if r.verdict == "UNKNOWN"]
    dead = [r for r in results if r.verdict == "DEAD"]
    disabled = [r for r in results if r.verdict == "DISABLED"]
    late = [r for r in results if r.verdict == "LATE"]
    # Les deux verdicts chroniques qui portent le rouge de l'organe : un cron
    # mort et un workflow desactive appellent deux remedes differents, mais tous
    # deux doivent etre vus (#22937 volet 6).
    red = [r for r in results if r.verdict in ("DEAD", "DISABLED")]

    if args.json:
        print(json.dumps({
            "unknown": len(unknown), "dead": len(dead), "disabled": len(disabled),
            "late": len(late),
            "organs": [
                {
                    "workflow": r.organ.workflow,
                    "declared_min": r.organ.declared_min,
                    "verdict": r.verdict,
                    "age_min": r.age_min,
                    "served_min": r.served_min,
                    "n_runs": r.n_runs,
                    "workflow_state": r.workflow_state,
                    "state_updated_at": r.state_updated_at,
                    "warnings": r.warnings,
                    "detail": r.detail,
                }
                for r in results
            ],
        }, indent=2))
    else:
        for line in render(results):
            print(line)

    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        try:
            with open(summary, "a", encoding="utf-8") as fh:
                fh.write("\n".join(render(results)) + "\n")
        except OSError:
            pass  # a missing summary surface must not change the verdict

    # Control against a dead instrument: no organ yielded any history at all
    # (every probe failed, or every probe came back empty -- a wrong repo or a
    # token without Actions:read looks exactly like a fleet-wide scheduler
    # death). Report the instrument, never a fabricated fleet verdict.
    if all(r.n_runs == 0 for r in results):
        print(
            "::error::[scheduler-liveness] INSTRUMENT_UNKNOWN -- aucune sonde n'a "
            "rendu d'historique: c'est la mesure qui est en panne, pas forcement "
            "le scheduler. Ne pas lire ce rouge comme un verdict flotte (#15332).",
            file=sys.stderr,
        )
        return 1

    dead_marker = "::warning::" if args.dead_exit == "warning" else "::error::"
    for r in dead:
        print(
            f"{dead_marker}[scheduler-liveness] {r.organ.workflow}: {r.detail or 'dernier run planifie trop ancien'} "
            f"-- cadence declaree {r.organ.declared_min:.0f} min ({r.organ.note}). Voir #15332.",
            file=sys.stderr,
        )
    # Meme priorite d'affichage et meme severite qu'un DEAD : un workflow
    # desactive est un etat CHRONIQUE lui aussi, et il n'etait jusqu'ici nomme
    # nulle part (#22937 volet 6).
    for r in disabled:
        print(
            f"{dead_marker}[scheduler-liveness] {r.organ.workflow}: workflow DESACTIVE "
            f"(state={r.workflow_state}, updated_at={r.state_updated_at or 'inconnu'}) "
            f"-- l'age du dernier run ne mesure pas une panne de livraison. "
            f"Voir #22937.",
            file=sys.stderr,
        )
    if red and args.dead_exit == "warning":
        print(
            f"::warning::[scheduler-liveness] {len(red)} verdict(s) "
            f"DEAD/DISABLED ({len(dead)} DEAD, {len(disabled)} DISABLED) rendus en "
            "avertissement sur cette jambe : la livraison 'schedule' est un etat "
            "CHRONIQUE (#15332), et un rouge sur presque chaque commit masque les "
            "vrais rouges. Le rouge reste porte par les jambes 'schedule' et "
            "'workflow_dispatch' (#18292).",
            file=sys.stderr,
        )
    for r in unknown:
        print(
            f"::warning::[scheduler-liveness] {r.organ.workflow}: sonde en echec ({r.detail}) "
            "-- verdict UNKNOWN, non compte comme defaut.",
            file=sys.stderr,
        )
    for r in late:
        print(
            f"::warning::[scheduler-liveness] {r.organ.workflow}: livraison en retard "
            f"({r.age_min:.0f} min pour {r.organ.declared_min:.0f} min declares).",
            file=sys.stderr,
        )

    if red and args.dead_exit == "error":
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
