#!/usr/bin/env python3
"""Compteur des ``[RELEASED]`` sur les EPICs Origami -- le rendement du parcage (#24373).

L'organe de parcage (``origami_parking.py``) sort un EPIC Origami dont le pli
suivant n'est pas déplie de la file des lanes worker : la lane ne le sert plus,
et ne pose donc plus de ``[RELEASED]`` dessus. C'est le **critere 4** de #24373,
qui demande « le decompte des ``[RELEASED]`` evites sur la semaine suivant le
merge ».

**Ce que l'organe mesure, et ce qu'il ne mesure pas.**

* Mesure : le nombre **reel** de ``[RELEASED]`` poses sur chaque EPIC Origami,
  avant et apres l'instant du parcage. Un ``[RELEASED]`` pose apres l'instant
  sur un EPIC parque = le parcage a laisse passer un service.
* Mesure : le nombre de marqueurs ``[PLI N DEPLIE]`` poses apres l'instant --
  le **controle positif** du parcage : l'EPIC redepose dans la file au moment
  ou un pli se deploie.
* N'est PAS une mesure : le nombre de ``[RELEASED]`` *evites*. Il n'existe pas
  de compteur possible d'un evenement qui n'a pas eu lieu : l'evitement
  compteurfactual est une **extrapolation**, deduite du rythme mesure avant
  l'instant. L'organe la calcule et la **signale comme telle** -- jamais comme
  un compte.

    python scripts/coordination/origami_released_counter.py
    python scripts/coordination/origami_released_counter.py --json
    python scripts/coordination/origami_released_counter.py --since 2026-11-05T16:47:04Z

L'instant du parcage par defaut est la fusion de l'organe (#24389, mergee le
2026-11-05T16:47:04Z) : au-dela, un ``[RELEASED]`` sur un EPIC Origami est un
service que le parcage aurait du empecher.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from origami_parking import is_origami_epic  # noqa: E402
import origami_parking  # noqa: E402

REPO = "jsboige/CoursIA"

#: Fusion de l'organe de parcage (#24389) : l'instant apres lequel un
#: ``[RELEASED]`` sur un EPIC Origami est un service passe.
PARKING_INSTANT = "2026-11-05T16:47:04Z"

#: Le marqueur de ``[RELEASED]`` est en TETE de commentaire (meme convention que
#: l'organe de parcage) : une citation en milieu de corps ne compte pas.
RELEASED_HEADER_RE = re.compile(r"^\s*\[RELEASED\]", re.I)

#: Un depliage declare : ``[PLI 4 DEPLIE]`` (orthographe francisee ou non).
#: Le marqueur doit etre en TETE DE LIGNE : une citation en milieu de corps
#: (un rapport qui mentionne le marqueur d'un autre EPIC) ne deploie rien.
PLI_DEPLIE_RE = re.compile(
    r"^\s*\[\s*PLI\s+\d+\s+(?:D[ÉE]PLI[ÉE]|DEPLIE)\s*\]", re.I | re.M)

LANE_RE = re.compile(r"lane\s+([A-Za-z0-9_.:-]+)", re.I)


def _gh_json(*args: str) -> object | None:
    """Lecture JSON via ``gh``. ``None`` = lecture impossible (jamais un compte
    forge : unZero would be a lie)."""
    out = subprocess.run(["gh", *args], capture_output=True, text=True,
                         encoding="utf-8", errors="replace")
    if out.returncode != 0:
        return None
    try:
        return json.loads(out.stdout)
    except json.JSONDecodeError:
        return None


def parse_instant(text: str) -> datetime:
    """Un instant ISO-8601 en UTC (``Z`` explicite)."""
    raw = (text or "").strip()
    if raw.endswith("Z"):
        raw = raw[:-1] + "+00:00"
    try:
        dt = datetime.fromisoformat(raw)
    except ValueError as exc:
        raise ValueError(f"instant illisible: {text!r}") from exc
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt.astimezone(timezone.utc)


def fetch_pool(gh=_gh_json) -> list[dict] | None:
    """Issues ouvertes du depot (``number``, ``title``, ``body``).

    ``None`` = pool illisible : l'organe ne mesure rien (jamais de zero
    forge).
    """
    payload = gh("issue", "list", "--repo", REPO, "--state", "open",
                 "--limit", "2000", "--json", "number,title,body")
    if payload is None:
        return None
    return [{"number": int(it["number"]),
             "title": it.get("title") or "",
             "body": it.get("body") or ""} for it in payload]


def origami_epics(pool: list[dict]) -> list[dict]:
    """Les EPICs Origami du pool (meme critere que l'organe de parcage)."""
    return [it for it in pool if is_origami_epic(it)]


def fetch_comments(numbers: list[int], gh=_gh_json
                   ) -> tuple[dict[int, list[dict]], list[int]]:
    """Tous les commentaires d'une liste d'issues, pagines.

    L'organe de parcage lit ``comments(first:100)`` : sur un fil de plusieurs
    centaines de commentaires, les **100 plus anciens** suffisent a son
    besoin (il cherche un marqueur de depliage) mais pas au compteur, qui doit
    voir la fin du fil. D'ou la pagination REST ici.

    Rend ``(commentaires_par_epic, epics_illisibles)``. Une page qui n'a pas
    pu etre lue rend l'EPIC **illisible**, elle ne le rend pas vide : ``gh``
    rend ``None`` aussi bien pour un reseau coupe que pour un fil sans
    commentaire, et confondre les deux ferait passer un echec de lecture pour
    une absence de ``[RELEASED]`` -- le span que l'organe doit refuser. Un
    echec en page 2 ou plus tronque la fin du fil, qui porte justement les
    evenements posterieurs a l'instant : il rend l'EPIC illisible aussi.
    """
    out: dict[int, list[dict]] = {}
    unreadable: list[int] = []
    for n in numbers:
        comments: list[dict] = []
        page = 1
        complete = True
        while True:
            payload = gh("api", f"repos/{REPO}/issues/{n}/comments"
                               f"?per_page=100&page={page}")
            if not isinstance(payload, list):
                complete = False
                break
            comments.extend(payload)
            if len(payload) < 100:
                break
            page += 1
        if complete:
            out[n] = comments
        else:
            unreadable.append(n)
    return out, unreadable


def classify_comment(body: str) -> dict:
    """Ce qu'un commentaire porte : ``[RELEASED]`` en tete, depliage, lane."""
    text = body or ""
    first = text.strip().splitlines()[0] if text.strip() else ""
    lane = LANE_RE.search(first)
    return {
        "released": bool(RELEASED_HEADER_RE.match(first)),
        "pli_deplie": bool(PLI_DEPLIE_RE.search(text)),
        "lane": lane.group(1) if lane else None,
        "headline": first[:160],
    }


def count_events(comments_by_epic: dict[int, list[dict]],
                 instant: datetime) -> dict:
    """Les evenements de chaque EPIC, separes par l'instant du parcage."""
    epics = []
    for number in sorted(comments_by_epic):
        before, after = [], []
        deplie_after = []
        for c in comments_by_epic[number]:
            created = c.get("created_at")
            if not created:
                continue
            try:
                dt = parse_instant(created)
            except ValueError:
                continue
            info = classify_comment(c.get("body") or "")
            if info["pli_deplie"] and dt >= instant:
                deplie_after.append({"at": created, "headline": info["headline"],
                                     "epic": number})
            if not info["released"]:
                continue
            entry = {"at": created, "lane": info["lane"],
                     "headline": info["headline"]}
            (before if dt < instant else after).append(entry)
        epics.append({
            "epic": number,
            "released_before": len(before),
            "released_after": len(after),
            "released_after_list": after,
            "deplie_after": deplie_after,
        })
    return {
        "epics": epics,
        "released_before": sum(e["released_before"] for e in epics),
        "released_after": sum(e["released_after"] for e in epics),
        "deplie_after": sum(len(e["deplie_after"]) for e in epics),
    }


def parked_epics(pool: list[dict]) -> set[int] | None:
    """Les EPICs que l'organe de parcage juge PARQUES.

    `None` = la mesure de parcage n'a pas pu etre faite (reseau, sonde) :
    l'appelant ne doit alors **rien conclure** sur les fuites -- jamais
    « zero fuite » par defaut.

    La reference est indispensable : un ``[RELEASED]`` pose apres l'instant
    sur un EPIC **parque** est une fuite du parcage ; le meme ``[RELEASED]``
    sur un EPIC que le parcage laisse servi (un pli est ouvert, une autre
    barriere) est un service legitime, pas une fuite.
    """
    try:
        verdicts = origami_parking.measure(pool)
    except Exception:  # pragma: no cover -- reseau
        return None
    return {int(v["epic"]) for v in verdicts if v.get("parked")}


def render(report: dict) -> None:
    print(f"Parcage Origami -- instant : {report['since']}")
    print(f"  EPICs Origami servis par le compteur : "
          f"{report.get('epics_readable', report['epics_count'])}"
          f"/{report['epics_count']}")
    print(f"  [RELEASED] avant l'instant : {report['released_before']}")
    print(f"  [RELEASED] APRES l'instant : {report['released_after']}")
    print(f"  marqueurs [PLI n DEPLIE] apres l'instant : {report['deplie_after']}")
    if report.get("parked_measured"):
        print(f"  EPICs jugets parcages a la mesure : "
              f"{report['parked_count']}")
        print(f"  CANDIDATS a qualifier ([RELEASED] apres l'instant sur un "
              f"EPIC aujourd'hui parque) : {report['released_after_on_parked']}")
        print("    NB : le verdict de parcage est un etat AUJOURD'HUI -- un "
              "pli ouvert au moment du [RELEASED] rend le service legitime. "
              "Un candidat n'est une fuite qu'apres lecture du motif.")
        for e in report.get("leaks", []):
            print(f"    #{e['epic']} {e['at']} {e['lane']} : {e['headline']}")
    else:
        print("  reference de parcage INDISPONIBLE : la distinction "
              "fuite / service legitime n'est pas etablie")
    if report.get("deplie_after_list"):
        print("  depliages declares apres l'instant (controle positif) :")
        for e in report["deplie_after_list"]:
            print(f"    #{e['epic']} {e['at']} : {e['headline']}")
    if report.get("released_after_list"):
        print("  [RELEASED] apres l'instant (par EPIC) :")
        for e in report["released_after_list"]:
            tag = "candidat" if report.get("parked_measured") and \
                e["epic"] in (report.get("parked_numbers") or []) else "serti"
            print(f"    [{tag}] #{e['epic']} {e['at']} {e['lane']} : "
                  f"{e['headline']}")
    if report.get("avoided_estimate") is not None:
        print(f"  evite (EXTRAPOLATION) : {report['avoided_estimate']} "
              f"({report['avoided_basis']})")
    print(f"  fenetre mesuree : {report['window_from']} -> {report['measured_at']}")
    print(f"  duree apres l'instant : {report['days_after']} jour(s)")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--since", default=PARKING_INSTANT,
                    help="instant du parcage (defaut : fusion de #24389)")
    ap.add_argument("--epic", type=int, action="append", default=[],
                    help="ne mesurer que cet EPIC (repete)")
    ap.add_argument("--no-parking-reference", action="store_true",
                    help="ne pas croiser avec les verdicts de parcage "
                         "(la distinction fuite / service legitime ne sera "
                         "pas etablie)")
    args = ap.parse_args(argv)

    instant = parse_instant(args.since)
    pool = fetch_pool()
    if pool is None:
        print("UNKNOWN: pool illisible -- aucune mesure")
        return 2
    epics = origami_epics(pool)
    if args.epic:
        wanted = set(args.epic)
        epics = [e for e in epics if e["number"] in wanted]
    numbers = [e["number"] for e in epics]
    if not numbers:
        print("UNKNOWN: aucun EPIC Origami trouve")
        return 2
    comments, unreadable = fetch_comments(numbers)

    counts = count_events(comments, instant)
    now = datetime.now(timezone.utc)

    # Fenetre de reference : du premier [RELEASED] observe a l'instant.
    all_stamps = []
    for number, cs in comments.items():
        for c in cs:
            info = classify_comment(c.get("body") or "")
            if info["released"] and c.get("created_at"):
                try:
                    dt = parse_instant(c["created_at"])
                except ValueError:
                    continue
                if dt < instant:
                    all_stamps.append(dt)
    window_from = min(all_stamps) if all_stamps else instant
    days_before = max((instant - window_from).total_seconds() / 86400.0, 0.0)
    days_after = max((now - instant).total_seconds() / 86400.0, 0.0)
    rate = (counts["released_before"] / days_before) if days_before > 0 else 0.0
    avoided = round(rate * days_after, 1)

    after_list = []
    for e in counts["epics"]:
        for entry in e["released_after_list"]:
            after_list.append({"epic": e["epic"], **entry})

    parked = None
    if not args.no_parking_reference:
        parked = parked_epics(pool)
    leaks = []
    if parked is not None:
        leaks = [e for e in after_list if e["epic"] in parked]
    deplie_list = [d for e in counts["epics"] for d in e["deplie_after"]]

    report = {
        "since": args.since,
        "measured_at": now.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "epics_count": len(numbers),
        "epics_readable": len(numbers) - len(unreadable),
        "unreadable_epics": sorted(unreadable),
        "released_before": counts["released_before"],
        "released_after": counts["released_after"],
        "deplie_after": counts["deplie_after"],
        "released_after_list": after_list,
        "parked_measured": parked is not None,
        "parked_count": len(parked) if parked is not None else None,
        "parked_numbers": sorted(parked) if parked is not None else None,
        "released_after_on_parked": len(leaks),
        "leaks": leaks,
        "deplie_after_list": deplie_list,
        "window_from": window_from.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "days_before": round(days_before, 2),
        "days_after": round(days_after, 2),
        "rate_before_per_day": round(rate, 2),
        "avoided_estimate": avoided,
        "avoided_basis": "rythme = [RELEASED] avant l'instant / jours ecoules "
                         "depuis le PREMIER [RELEASED] jamais observe (toute "
                         "l'histoire du fil, pas une fenetre de 7 jours) ; "
                         "x duree apres l'instant -- EXTRAPOLATION, pas un "
                         "compte",
        "rate_basis": "premier [RELEASED] observe -> instant",
        "per_epic": counts["epics"],
    }
    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=1))
    else:
        render(report)
        if unreadable:
            print(f"  LECTURE INCOMPLETE : {len(unreadable)} EPIC(s) "
                  f"illisible(s), exclus du compte -- "
                  + ", ".join(f"#{n}" for n in sorted(unreadable)))
    return 3 if unreadable else 0


if __name__ == "__main__":
    sys.exit(main())
