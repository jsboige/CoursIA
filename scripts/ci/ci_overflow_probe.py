#!/usr/bin/env python3
"""Sonde legere de debordement CI (#26939) -- elle reveille, elle ne decide pas.

Le controleur (`ci-overflow-controller.yml`, organe `ci_overflow_controller.py`)
decide sur un instantane, au rythme de ses declencheurs (cron '31 * * * *' +
timer local ai-01, ~2 passages/h). Entre deux passages, RIEN ne reactit a une
montee de la file : l'episode du 16/11 a fait passer la file de ~0 a 386 runs
en ~40 min sans qu'aucun passage ne s'intercale. La sonde comble exactement ce
trou, au budget de 2 appels `gh` au repos :

1. appel 1 -- total des runs en file : `actions/runs?status=queued&per_page=1`
   (seul le champ `total_count` est lu) ;
2. appel 2 -- variable de depot `CI_OVERFLOW_LOCAL` (false = herberge par
   defaut, true = reorientation locale en cours) ;
3. si cet etat justifie un passage du controleur, appel 3 (EVENTUEL, seulement
   sur candidat) -- age du dernier passage du controleur, pour l'anti-repetition ;
4. si le candidat survit au gap, appel 4 (EVENTUEL) -- dispatch du controleur
   complet (`workflow_dispatch`, `min_interval=0` comme l'exige l'issue).

Les seuils ne sont pas inventes ici : la sonde importe ceux de l'organe
(`HOSTED_CONCURRENCY_CAP` du controleur) et en derive ses declencheurs --
declencher quand la file depasse le plafond de concurrence herbergee (variable
false), reorienter quand elle le depasse du double (variable true). La decision
reste AU CONTROLEUR : la sonde ne lit ni l'age des runs, ni la repartition
herberge/local, ni les slots libres -- c'est le prix des 2 appels, et c'est
pourquoi elle ne sature rien elle-meme.

Anti-repetition budgetaire : un passage du controleur coute ~313 appels ; la
sonde ne re-dispatche pas si le dernier passage date de moins de
`--min-dispatch-gap-minutes` (defaut : DEFAULT_SATURATION_MINUTES du
controleur, 15.0 -- la fenetre au-dela de laquelle le controleur juge lui-meme
un job en file « ancien »). Sans cette garde, un etat candidat persistant
(controleur en HOLD volet (c), cf 10:46 le 16/11) re-dispatcherait a chaque
passage sonde : 5 x 313 = 1565 appels/h, au-dessus du plafond de 1000/h --
exactement le budget que l'issue refuse de bruler. Pire cas avec la garde :
~4 dispatchs sonde/h dans un etat candidat persistant (transitoire en
pratique : les slots locaux se liberent en minutes, episode du 16/11 < 1 h) ;
regime normal : 5 passages/h x 2 appels = 10 appels/h.

Deviation nommee au critere « declenchement sous 15 min » : l'anti-repetition
peut retarder le PREMIER dispatch d'un etat neuf franchi dans la minute qui
suit un passage controleur, jusqu'a gap + cadence ~ 27 min dans l'alignement
le pire. La montee reelle de l'episode (progressive, ~38 min pour 0 -> 386)
franchit le seuil avec un age de dernier passage suffisamment vieux dans les
alignements habituels : le rejeu nominal tient les 15 min. Arbitrage
latence/budget assume et laisse a la review (l'alternative gap = 0 coute
1565 appels/h).

Sorties : exit 0 nominal (dispatch, hold ou idle) ; exit 1 = mesure impossible
(le mode degrade est visible via `::warning` dans le workflow, jamais muet).
ADVISORY par construction : schedule + workflow_dispatch seulement, aucune
PR ne peut etre bloquee par cette sonde (doctrine #12817).
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

# Seuils ancre's sur l'organe, jamais re'-invente's ici (regle organ-first) :
# le plafond de concurrence herberge'e est la barrie`re que le contro^leur
# surveille ; la sonde s'en sert comme seuil de reveil et de son double.
from ci_overflow_controller import (  # noqa: E402
    CONTROLLER_WORKFLOW_FILE,
    DEFAULT_REPO,
    DEFAULT_SATURATION_MINUTES,
    DEFAULT_VARIABLE,
    EXIT_OK,
    EXIT_UNREADABLE,
    HOSTED_CONCURRENCY_CAP,
)

PROBE_TRIGGER_QUEUE = HOSTED_CONCURRENCY_CAP
"""Seuil de reveil, variable false : file > plafond heberge (20 par defaut)."""

PROBE_REORIENT_QUEUE = 2 * HOSTED_CONCURRENCY_CAP
"""Seuil de reveil, variable true : file > 2x plafond (40 par defaut)."""

DEFAULT_MIN_DISPATCH_GAP_MINUTES = DEFAULT_SATURATION_MINUTES
"""Anti-repetition : ecart mini avec le dernier passage du controleur.

Ancre organ : c'est la fenetre au-dela de laquelle le CONTROLEUR lui-meme juge
un job « en file depuis trop longtemps » (DEFAULT_SATURATION_MINUTES = 15.0)
-- si le controleur a passe il y a moins que cette fenetre, l'instantane qu'il
a vu est plus frais que la patience qu'il applique lui-meme aux jobs."""

MAX_CADENCE_GAP_MINUTES = 15.0
"""Contrat de latence de l'issue : deux passages sonde a moins de 15 min."""


@dataclass
class ProbeDecision:
    """Verdict de la sonde : action + raison citant les valeurs mesurees."""

    action: str  # "idle" | "dispatch" | "hold"
    reason: str
    queue_total: int | None = None
    variable: str | None = None
    last_pass_age_min: float | None = None


def decide(
    queue_total: int,
    variable_value: str,
    last_pass_age_min: float | None = None,
    trigger_queue: int = PROBE_TRIGGER_QUEUE,
    reorient_queue: int = PROBE_REORIENT_QUEUE,
    min_gap_min: float = DEFAULT_MIN_DISPATCH_GAP_MINUTES,
) -> ProbeDecision:
    """Coeur PUR de la sonde : aucun appel reseau, testable tel quel.

    `last_pass_age_min=None` signifie « aucun passage du controleur connu » --
    un candidat sans age connu se dispatche (premier passage).
    """
    var_true = str(variable_value).strip().lower() == "true"
    if not var_true and queue_total > trigger_queue:
        candidate = (
            f"file {queue_total} > {trigger_queue} (plafond de concurrence "
            f"herbergee) alors que la variable est false"
        )
    elif var_true and queue_total > reorient_queue:
        candidate = (
            f"file {queue_total} > {reorient_queue} (2x plafond herberge) "
            f"alors que la variable est true (reorientation locale en cours)"
        )
    else:
        return ProbeDecision(
            action="idle",
            reason=(
                f"file {queue_total} sous les seuils "
                f"(variable {'true' if var_true else 'false'}, seuils "
                f"{trigger_queue}/{reorient_queue})"
            ),
            queue_total=queue_total,
            variable=variable_value,
            last_pass_age_min=last_pass_age_min,
        )
    if last_pass_age_min is not None and last_pass_age_min < min_gap_min:
        return ProbeDecision(
            action="hold",
            reason=(
                f"{candidate} -- ecarte : dernier passage du controleur il y a "
                f"{last_pass_age_min:.1f} min < {min_gap_min:.0f} min (anti-repetition)"
            ),
            queue_total=queue_total,
            variable=variable_value,
            last_pass_age_min=last_pass_age_min,
        )
    return ProbeDecision(
        action="dispatch",
        reason=candidate,
        queue_total=queue_total,
        variable=variable_value,
        last_pass_age_min=last_pass_age_min,
    )


def gh_api(args: list[str], token: str | None = None) -> tuple[int, str]:
    """Appelle `gh api` et rend (code retour, stdout). Forme du controleur."""
    import os

    env = dict(os.environ)
    if token:
        env["GH_TOKEN"] = token
    proc = subprocess.run(
        ["gh", "api", *args],
        capture_output=True,
        text=True,
        check=False,
        encoding="utf-8",
        errors="replace",
        env=env,
    )
    return proc.returncode, proc.stdout


def parse_cron_minutes(spec: str) -> list[int]:
    """Etend le champ MINUTES d'un cron (subset bash-cron) en liste triee.

    Supporte : "*", "*/n", "a", "a-b", "a-b/n", "a,b,c" et leurs combinaisons.
    Sert au contrat de cadence : l'ecart entre deux passages sonde doit rester
    sous MAX_CADENCE_GAP_MINUTES.
    """
    minutes: set[int] = set()
    for part in spec.split(","):
        part = part.strip()
        if part == "*":
            minutes.update(range(60))
        elif "*/" in part:
            step = int(part.split("/", 1)[1])
            minutes.update(range(0, 60, step))
        elif "-" in part:
            bounds, _, step_s = part.partition("/")
            lo, hi = (int(x) for x in bounds.split("-", 1))
            step = int(step_s) if step_s else 1
            minutes.update(range(lo, hi + 1, step))
        else:
            minutes.add(int(part))
    return sorted(minutes)


def max_cadence_gap_minutes(minutes: list[int]) -> float:
    """Ecart max entre deux minutes consecutives, wrap 59 -> 0 compris."""
    if len(minutes) < 2:
        return float("inf") if not minutes else 60.0
    gaps = [
        b - a for a, b in zip(minutes, minutes[1:])
    ] + [(minutes[0] + 60) - minutes[-1]]
    return float(max(gaps))


def _age_minutes(created_at_iso: str, now: datetime) -> float:
    """Age en minutes d'un timestamp ISO (le 'Z' final accepte partout)."""
    ts = datetime.fromisoformat(created_at_iso.replace("Z", "+00:00"))
    return (now - ts).total_seconds() / 60.0


def run(
    repo: str,
    variable: str,
    workflow_file: str,
    token: str | None,
    min_gap_min: float,
    dry_run: bool = False,
    api=gh_api,
    now: datetime | None = None,
) -> tuple[ProbeDecision, int, bool]:
    """Mesure puis decide. Rend (decision, nb d'appels gh, dispatch_effectue).

    `api` est injectable : les tests rejouent les episodes sans reseau.
    """
    now = now or datetime.now(timezone.utc)
    calls = 0

    # Appel 1 : total de la file (seul total_count est lu).
    rc, out = api([f"repos/{repo}/actions/runs?status=queued&per_page=1"], token)
    calls += 1
    if rc != 0:
        return (
            ProbeDecision("hold", f"file illisible (gh rc={rc})"),
            calls,
            False,
        )
    try:
        queue_total = int(json.loads(out)["total_count"])
    except (ValueError, KeyError, TypeError):
        return (ProbeDecision("hold", "file illisible (payload inattendu)"), calls, False)

    # Appel 2 : variable de depot.
    rc, out = api([f"repos/{repo}/actions/variables/{variable}"], token)
    calls += 1
    if rc != 0:
        return (
            ProbeDecision("hold", f"variable {variable} illisible (gh rc={rc})"),
            calls,
            False,
        )
    try:
        variable_value = str(json.loads(out)["value"])
    except (ValueError, KeyError, TypeError):
        return (ProbeDecision("hold", "variable illisible (payload inattendu)"), calls, False)

    # Pre-decision sur les 2 mesures : si idle, on s'arrete a 2 appels.
    early = decide(queue_total, variable_value, None, min_gap_min=min_gap_min)
    if early.action == "idle":
        return early, calls, False

    # Appel 3 (candidat seulement) : age du dernier passage du controleur.
    rc, out = api(
        [f"repos/{repo}/actions/workflows/{workflow_file}/runs?per_page=1"],
        token,
    )
    calls += 1
    if rc != 0:
        return (
            ProbeDecision("hold", f"age du dernier passage illisible (gh rc={rc})"),
            calls,
            False,
        )
    try:
        runs = json.loads(out).get("workflow_runs", [])
        age = _age_minutes(runs[0]["created_at"], now) if runs else None
    except (ValueError, KeyError, TypeError, IndexError):
        return (ProbeDecision("hold", "age du dernier passage illisible (payload)"), calls, False)

    decision = decide(queue_total, variable_value, age, min_gap_min=min_gap_min)
    if decision.action != "dispatch" or dry_run:
        return decision, calls, False

    # Appel 4 : dispatch du controleur complet (min_interval=0, spec #26939).
    rc, out = api(
        [
            f"repos/{repo}/actions/workflows/{workflow_file}/dispatches",
            "-X",
            "POST",
            "-f",
            "ref=main",
        ],
        token,
    )
    calls += 1
    if rc != 0:
        return (
            ProbeDecision("hold", f"dispatch refuse (gh rc={rc}, {out.strip()[:120]})"),
            calls,
            False,
        )
    return decision, calls, True


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", default=DEFAULT_REPO)
    parser.add_argument("--variable", default=DEFAULT_VARIABLE)
    parser.add_argument("--workflow-file", default=CONTROLLER_WORKFLOW_FILE)
    parser.add_argument("--token-env", default="GH_TOKEN")
    parser.add_argument(
        "--min-dispatch-gap-minutes",
        type=float,
        default=DEFAULT_MIN_DISPATCH_GAP_MINUTES,
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="mesure et decide, ne dispatche jamais (preuve de budget)",
    )
    parser.add_argument(
        "--simulate",
        metavar="QUEUE,VAR[,AGE_MIN]",
        help="rejoue un etat sans aucun appel reseau (queue, variable, age du dernier passage)",
    )
    parser.add_argument("--json", action="store_true", help="sortie machine")
    args = parser.parse_args(argv)

    if args.simulate:
        parts = args.simulate.split(",")
        queue_total = int(parts[0])
        variable_value = parts[1]
        age = float(parts[2]) if len(parts) > 2 else None
        decision = decide(
            queue_total,
            variable_value,
            age,
            min_gap_min=args.min_dispatch_gap_minutes,
        )
        calls = 0
        dispatched = False
    else:
        import os

        token = os.environ.get(args.token_env)
        decision, calls, dispatched = run(
            repo=args.repo,
            variable=args.variable,
            workflow_file=args.workflow_file,
            token=token,
            min_gap_min=args.min_dispatch_gap_minutes,
            dry_run=args.dry_run,
        )

    if args.json:
        print(
            json.dumps(
                {
                    "action": decision.action,
                    "reason": decision.reason,
                    "queue_total": decision.queue_total,
                    "variable": decision.variable,
                    "last_pass_age_min": decision.last_pass_age_min,
                    "gh_calls": calls,
                    "dispatched": dispatched,
                    "dry_run": args.dry_run,
                },
                ensure_ascii=False,
            )
        )
    else:
        prefix = {"idle": "[probe]", "hold": "[probe-hold]", "dispatch": "[probe-dispatch]"}
        tag = prefix.get(decision.action, "[probe]")
        suffix = " (dry-run, dispatch omis)" if args.dry_run and decision.action == "dispatch" else ""
        dispatched_note = " -- CONTROLEUR DISPATCH" if dispatched else ""
        print(f"{tag} {decision.reason} -- {calls} appel(s) gh{suffix}{dispatched_note}")

    # Une mesure impossible n'est pas un etat : elle sort en exit 1 pour que
    # le workflow l'affiche en warning (visible, jamais muet).
    if decision.reason.startswith(("file illisible", "variable", "age du dernier", "dispatch refuse")):
        return EXIT_UNREADABLE
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
