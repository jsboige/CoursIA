#!/usr/bin/env python3
"""Recette hebdomadaire : chaque lane fait au moins un tour de recette par semaine.

Une issue de recette (label ``recette``) a un validateur humain, hors flotte, qui
attend des allers-retours : on lui livre une iteration, il ecoute ou teste, il
repond, on reprend. Sans tirage regulier, le validateur attend des semaines
(#17586 : un validateur disponible le 24/09, aucune iteration a ecouter au 06/10).

Cet organe repond, pour UNE lane, a une seule question : son dernier tour de
recette date-t-il de plus de ``--window-days`` jours ? Si oui, il designe l'issue
de recette a servir en premier.

Un tour = un marqueur de claim attribue a la lane (``[CLAIMED]``, ``[DELIVERED]``,
``[RELEASED]``, ``[DONE]`` ...) sur une issue ``recette``, lu par le reducteur de
``check_lane_claim.py`` (meme grammaire, aucun parseur parallele).

Ordre de service quand le tour est du :
  0. une issue tenue par le claim vivant (moins de 48 h) d'une AUTRE lane passe
     en dernier : la lane qui la tient fait deja le tour du validateur ;
  1. l'issue ou le validateur a parle en dernier (la balle est chez la flotte) ;
  2. puis celle que cette lane n'a jamais servie ;
  3. puis celle dont la derniere visite de flotte est la plus ancienne.

Le validateur se declare dans le body de l'issue par une ligne
``Validateur : @login`` ; a defaut, tout auteur hors flotte compte comme validateur.

Sorties : rc 0 = rien a faire (tour fait, ou aucune issue ``recette``) ;
rc 1 = tour du, l'issue est nommee ; rc 2 = organe injoignable (fail-open : le
cycle continue, la ligne ``UNKNOWN`` le dit).

    python scripts/coordination/recette_due.py --lane myia-po-2023:CoursIA
    python scripts/coordination/recette_due.py --lane myia-po-2023:CoursIA --json
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc  # noqa: E402

REPO = "jsboige/CoursIA"
LABEL = "recette"
DEFAULT_WINDOW_DAYS = 7.0
#: Meme seuil de peremption que `check_lane_claim.py --stale-threshold` par defaut.
HOLD_STALE_HOURS = 48.0

#: Comptes de la flotte. Toutes les lanes signent ``jsboige`` ; les bots finissent par ``[bot]``.
FLEET_LOGINS = frozenset({"jsboige", "myia-ai-01", "clusterManager-Myia"})

_VALIDATOR_RE = re.compile(r"^\s*\**\s*Validateur\s*\**\s*:\s*\**\s*@([A-Za-z0-9-]+)", re.IGNORECASE | re.MULTILINE)

ListFetcher = Callable[[], list]
IssueFetcher = Callable[[int], dict]


def is_fleet(login: str | None) -> bool:
    if not login:
        return True
    return login in FLEET_LOGINS or login.endswith("[bot]")


def declared_validator(body: str) -> str | None:
    m = _VALIDATOR_RE.search(body or "")
    return m.group(1) if m else None


def _age_days(iso: str | None, now: datetime) -> float | None:
    if not iso:
        return None
    ts = datetime.fromisoformat(iso.replace("Z", "+00:00"))
    return (now - ts).total_seconds() / 86400.0


def assess_issue(payload: dict, lane: str, now: datetime) -> dict:
    """Etat d'une issue de recette vu depuis ``lane``."""
    comments = payload.get("comments") or []
    validator = declared_validator(payload.get("body") or "")

    def spoke_as_validator(c: dict) -> bool:
        login = (c.get("author") or {}).get("login")
        return login == validator if validator else not is_fleet(login)

    last_validator = max((c.get("createdAt") or "" for c in comments if spoke_as_validator(c)), default="")
    last_fleet = max(
        (c.get("createdAt") or "" for c in comments
         if is_fleet((c.get("author") or {}).get("login"))),
        default="",
    )
    events = clc._sort_events(payload)
    lane_events = [ev for ev in events if ev.lane == lane]
    last_lane = lane_events[-1].created_at if lane_events else None
    active, _ = clc.compute_active_claims(events)
    held_by = sorted(
        other for other, ev in active.items()
        if other != lane and (_age_days(ev.created_at, now) or 0.0) * 24.0 <= HOLD_STALE_HOURS
    )
    return {
        "number": payload.get("number"),
        "title": payload.get("title"),
        "validator": validator,
        "last_validator_comment": last_validator or None,
        "last_fleet_comment": last_fleet or None,
        "last_lane_visit": last_lane,
        "lane_visit_age_days": _age_days(last_lane, now),
        "ball_in_fleet_court": bool(last_validator) and last_validator > last_fleet,
        "held_by": held_by,
    }


def service_key(state: dict) -> tuple:
    """Plus petit = servi en premier."""
    return (
        1 if state["held_by"] else 0,
        0 if state["ball_in_fleet_court"] else 1,
        0 if state["last_lane_visit"] is None else 1,
        state["last_fleet_comment"] or "",
    )


def decide(states: list[dict], window_days: float) -> dict:
    if not states:
        return {"verdict": "NONE", "issue": None, "reason": f"aucune issue ouverte labellisee `{LABEL}`"}
    ages = [s["lane_visit_age_days"] for s in states if s["lane_visit_age_days"] is not None]
    last = min(ages) if ages else None
    if last is not None and last <= window_days:
        recent = min((s for s in states if s["lane_visit_age_days"] is not None),
                     key=lambda s: s["lane_visit_age_days"])
        return {"verdict": "OK", "issue": recent["number"],
                "reason": f"dernier tour de recette il y a {last:.1f} j (#{recent['number']})"}
    target = min(states, key=service_key)
    if target["held_by"]:
        why = f"toutes les issues sont tenues ; celle-ci par {', '.join(target['held_by'])}, verifier le claim avant d'editer"
    elif target["ball_in_fleet_court"]:
        why = "le validateur a repondu, la balle est chez la flotte"
    elif target["last_lane_visit"] is None:
        why = "jamais servie par cette lane"
    else:
        why = "derniere visite de flotte la plus ancienne"
    since = "jamais" if last is None else f"il y a {last:.1f} j"
    return {"verdict": "DUE", "issue": target["number"],
            "reason": f"aucun tour de recette depuis {window_days:g} j (dernier : {since}) ; {why}"}


def _gh_json(args: list[str]):
    out = subprocess.run(["gh", *args], capture_output=True, text=True, encoding="utf-8", check=True)
    return json.loads(out.stdout)


def gh_list() -> list:
    return _gh_json(["issue", "list", "--repo", REPO, "--label", LABEL, "--state", "open",
                     "--limit", "50", "--json", "number"])


def gh_issue(number: int) -> dict:
    return _gh_json(["issue", "view", str(number), "--repo", REPO,
                     "--json", "number,title,body,comments"])


def run(lane: str, window_days: float, now: datetime,
        list_issues: ListFetcher = gh_list, fetch_issue: IssueFetcher = gh_issue) -> dict:
    states = [assess_issue(fetch_issue(it["number"]), lane, now) for it in list_issues()]
    result = decide(states, window_days)
    result.update({"lane": lane, "window_days": window_days, "issues": states})
    return result


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--lane", required=True, help="lane machine:workspace, ex. myia-po-2023:CoursIA")
    ap.add_argument("--window-days", type=float, default=DEFAULT_WINDOW_DAYS)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args(argv)
    now = datetime.now(timezone.utc)
    try:
        result = run(args.lane, args.window_days, now)
    except (subprocess.CalledProcessError, FileNotFoundError, json.JSONDecodeError) as exc:
        print(f"UNKNOWN: recette_due injoignable ({type(exc).__name__}) -- le cycle continue sans tour de recette")
        return 2
    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
    else:
        for s in result["issues"]:
            age = "jamais" if s["lane_visit_age_days"] is None else f"{s['lane_visit_age_days']:.1f} j"
            who = f"@{s['validator']}" if s["validator"] else "hors flotte"
            ball = "flotte" if s["ball_in_fleet_court"] else "validateur"
            held = f" | tenue par {', '.join(s['held_by'])}" if s["held_by"] else ""
            print(f"  #{s['number']} validateur {who} | derniere visite de la lane : {age} | balle : {ball}{held}")
        tail = f" #{result['issue']}" if result["verdict"] == "DUE" else ""
        print(f"VERDICT: {result['verdict']}{tail} -- {result['reason']}")
    return 1 if result["verdict"] == "DUE" else 0


if __name__ == "__main__":
    sys.exit(main())
