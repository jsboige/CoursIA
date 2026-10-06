#!/usr/bin/env python3
"""Tirage central du tapis : le coordinateur tire ~50 issues par tour et compose les files.

Le tapis (``pick_idle_grain.py --belt``) range l'ouvert par derniere visite. Quand
chaque lane le tire seule, elle le tire APRES sa file de dispatch, et une file
remplie au fil de l'actualite ne contient que du recent : la tete du tapis ne
recoit que les restes (mesure du 2026-10-06 : la nuit, 8 merges sur des issues de
plus de 30 j ; le matin, aucun).

Le coordinateur tire donc une fois par tour et compose lui-meme, issues sous les
yeux, une file par lane : un arc progressif et coherent, que la lane enchaine en
multi-grain jusqu'au tour suivant en gardant son contexte d'une tache a l'autre.
**La repartition est un jugement, pas un calcul** : cet organe ne la fait pas. Il
prepare ce que le coordinateur regarde, et il mesure apres coup.

``board``  -- le tableau de decision :
  * les issues tirees, regroupees par famille (serie de notebooks, etiquette de
    titre, label, genre), avec leurs jours sans visite et leurs contraintes
    reperees (``vision``, ``vllm-local``) ;
  * l'assiette de chaque lane depuis la repartition precedente : une issue y reste
    tant qu'elle est ouverte et que la lane n'y a pas rendu la main
    (``[DELIVERED]``, ``[RELEASED]``, ``[DONE]``) -- le ``[CLAIMED]`` pose au
    dispatch ne compte pas ;
  * le tour de recette hebdomadaire de chaque lane (``recette_due.py``).

``record`` -- enregistre la repartition decidee par le coordinateur (horodatee),
pour que le ``board`` suivant mesure les assiettes.

    python scripts/pick_idle_grain.py --belt --lane myia-ai-01:CoursIA --json --grains 50 > belt.json
    python scripts/coordination/belt_queues.py board --belt-json belt.json --previous latest \\
        --lanes myia-po-2023:CoursIA,myia-po-2027:CoursIA-2
    python scripts/coordination/belt_queues.py record --assignment files.json --belt-json belt.json

``files.json`` (ecrit par le coordinateur) :
``{"lanes": {"myia-po-2023:CoursIA": {"arc": "Search, du diagnostic au correctif",
"queue": [15639, 16034, 17315]}}}``. Les repartitions vivent hors depot, sous
``%LOCALAPPDATA%/CoursIA/belt_queues/``.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc  # noqa: E402
import recette_due as rd  # noqa: E402

_SERIES_RE = re.compile(r"MyIA\.AI\.Notebooks/([A-Za-z][\w.-]*)(?:/([A-Za-z][\w.-]*))?")
_TAG_RE = re.compile(r"^\s*\[([^\]]{1,30})\]")
_VISION_RE = re.compile(r"\b(QA visuel|rendu visuel|slides?|galerie|capture|screenshot|image[s]? g[ée]n[ée]r)", re.I)
_VLLM_RE = re.compile(r"(192\.168\.0\.47|:5002\b|vLLM local|inf[ée]rence locale)", re.I)


def store_dir() -> Path:
    base = os.environ.get("LOCALAPPDATA") or str(Path.home() / ".local" / "share")
    return Path(base) / "CoursIA" / "belt_queues"


def family_of(pick: dict) -> str:
    """Cle de regroupement : serie de notebooks > etiquette de titre > label > genre."""
    text = f"{pick.get('title') or ''}\n{pick.get('body') or ''}"
    m = _SERIES_RE.search(text)
    if m:
        return "/".join(p for p in m.groups() if p)
    t = _TAG_RE.match(pick.get("title") or "")
    if t:
        return t.group(1).strip()
    labels = [lb.get("name") if isinstance(lb, dict) else lb for lb in pick.get("labels") or []]
    if labels:
        return sorted(labels)[0]
    return pick.get("genre") or "divers"


def needs_of(pick: dict) -> list[str]:
    text = f"{pick.get('title') or ''}\n{pick.get('body') or ''}"
    out = []
    if _VISION_RE.search(text):
        out.append("vision")
    if _VLLM_RE.search(text):
        out.append("vllm-local")
    return out


def visit_age_days(pick: dict, now: datetime) -> float | None:
    """Jours depuis la derniere visite au sens du tapis : merge citant l'issue ou claim attribue.

    Le champ ``idle`` du picker mesure l'activite quelconque (``updated_at``) : un commentaire
    de bot le remet a zero sans que personne ait servi l'issue. Ce n'est pas la cle du tapis.
    """
    stamps = [s for s in (pick.get("last_delivery_stamp"), pick.get("last_claim_stamp")) if s]
    ref = max(stamps) if stamps else pick.get("created_at")
    if not ref:
        return None
    return round((now - datetime.fromisoformat(ref.replace("Z", "+00:00"))).total_seconds() / 86400.0, 1)


def group_picks(picks: list[dict], now: datetime) -> list[dict]:
    """Familles dans l'ordre du tapis (rang du premier membre)."""
    groups: dict[str, dict] = {}
    for rank, p in enumerate(picks):
        fam = family_of(p)
        g = groups.setdefault(fam, {"family": fam, "rank": rank, "items": []})
        g["items"].append({"number": p["number"], "title": p.get("title"),
                           "since_visit": visit_age_days(p, now), "needs": needs_of(p)})
    return sorted(groups.values(), key=lambda g: g["rank"])


def lane_served_since(payload: dict, lane: str, since: str) -> bool:
    """La lane a rendu la main depuis la repartition (``[DELIVERED]``, ``[RELEASED]``, ``[DONE]``).

    Un ``[CLAIMED]`` seul ne vide pas l'assiette : le coordinateur le pose lui-meme
    au dispatch, et une issue prise mais pas rendue reste a servir.
    """
    return any(ev.lane == lane and ev.get("action") == "close" and (ev.created_at or "") >= since
               for ev in clc._sort_events(payload))


def measure_plates(previous: dict, fetch_issue) -> dict[str, dict]:
    """Ce qui reste dans l'assiette de chaque lane depuis la repartition precedente."""
    since = previous["assigned_at"]
    plates = {}
    for lane, info in previous["lanes"].items():
        remaining = []
        for it in info["queue"]:
            payload = fetch_issue(it["number"])
            if payload.get("state", "OPEN").upper() != "OPEN" or lane_served_since(payload, lane, since):
                continue
            remaining.append(it)
        plates[lane] = {"assigned": len(info["queue"]), "remaining": remaining, "arc": info.get("arc")}
    return plates


def gh_issue_state(number: int) -> dict:
    out = subprocess.run(["gh", "issue", "view", str(number), "--repo", rd.REPO,
                          "--json", "number,state,comments"],
                         capture_output=True, text=True, encoding="utf-8", check=True)
    return json.loads(out.stdout)


def board(belt: dict, lanes: list[str], previous: dict | None, now: datetime,
          fetch_issue=gh_issue_state, recette=None) -> dict:
    plates = measure_plates(previous, fetch_issue) if previous else {}
    on_plate = {it["number"] for p in plates.values() for it in p["remaining"]}
    picks = [p for p in belt.get("picks", []) if p["number"] not in on_plate]
    out_lanes = {}
    for lane in list(dict.fromkeys(lanes + list(plates))):
        plate = plates.get(lane)
        out_lanes[lane] = {
            "assigned": plate["assigned"] if plate else 0,
            "remaining": plate["remaining"] if plate else [],
            "arc": plate["arc"] if plate else None,
            "recette": recette(lane) if recette else None,
        }
    return {"drawn": len(belt.get("picks", [])), "families": group_picks(picks, now), "lanes": out_lanes,
            "previous_at": previous["assigned_at"] if previous else None}


def render_board(b: dict) -> str:
    lines = [f"{b['drawn']} issues tirees ; repartition precedente : {b['previous_at'] or 'aucune'}", "",
             "# Familles (ordre du tapis ; jours depuis la derniere visite)"]
    for g in b["families"]:
        lines.append(f"\n## {g['family']} ({len(g['items'])})")
        for it in g["items"]:
            needs = f" [{', '.join(it['needs'])}]" if it["needs"] else ""
            age = "" if it.get("since_visit") is None else f"{it['since_visit']} j"
            lines.append(f"  #{it['number']} {age}{needs} {it.get('title') or ''}")
    lines += ["", "# Lanes"]
    for lane, info in b["lanes"].items():
        rest = [it["number"] for it in info["remaining"]]
        served = info["assigned"] - len(rest)
        rec = info["recette"] or {}
        rec_txt = f" | recette {rec.get('verdict')}" + (f" #{rec['issue']}" if rec.get("verdict") == "DUE" else "")
        lines.append(f"  {lane} : {served}/{info['assigned']} rendues, assiette {rest}{rec_txt if rec else ''}")
    return "\n".join(lines)


def record(assignment: dict, belt: dict | None, now: datetime) -> dict:
    """Valide et horodate la repartition decidee par le coordinateur."""
    titles = {p["number"]: p for p in (belt or {}).get("picks", [])}
    seen: dict[int, str] = {}
    lanes = {}
    for lane, info in assignment["lanes"].items():
        queue = []
        for n in info["queue"]:
            n = int(n)
            if n in seen:
                raise ValueError(f"#{n} attribuee deux fois ({seen[n]} et {lane})")
            seen[n] = lane
            p = titles.get(n, {})
            queue.append({"number": n, "title": p.get("title"), "family": family_of(p) if p else None})
        lanes[lane] = {"arc": info.get("arc"), "queue": queue}
    return {"assigned_at": now.strftime("%Y-%m-%dT%H:%M:%SZ"), "lanes": lanes}


def _load_previous(arg: str | None) -> dict | None:
    if not arg:
        return None
    if arg == "latest":
        files = sorted(store_dir().glob("draw-*.json"))
        return json.loads(files[-1].read_text(encoding="utf-8")) if files else None
    return json.loads(Path(arg).read_text(encoding="utf-8"))


def _read_json(path: str | None):
    return json.loads(Path(path).read_text(encoding="utf-8")) if path else None


def main(argv: list[str] | None = None) -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    b = sub.add_parser("board")
    b.add_argument("--belt-json", required=True)
    b.add_argument("--previous", help="fichier d'une repartition precedente, ou 'latest'")
    b.add_argument("--lanes", default="", help="lanes a afficher, separees par des virgules")
    b.add_argument("--no-recette", action="store_true")
    b.add_argument("--json", action="store_true")
    r = sub.add_parser("record")
    r.add_argument("--assignment", required=True)
    r.add_argument("--belt-json")
    args = ap.parse_args(argv)
    now = datetime.now(timezone.utc)

    if args.cmd == "record":
        try:
            result = record(_read_json(args.assignment), _read_json(args.belt_json), now)
        except (ValueError, KeyError) as exc:
            print(f"REFUS: {exc}")
            return 1
        store_dir().mkdir(parents=True, exist_ok=True)
        out = store_dir() / f"draw-{result['assigned_at'].replace(':', '')}.json"
        out.write_text(json.dumps(result, ensure_ascii=False, indent=1), encoding="utf-8")
        print(f"repartition enregistree : {out} ({sum(len(v['queue']) for v in result['lanes'].values())} issues)")
        return 0

    lanes = [x.strip() for x in args.lanes.split(",") if x.strip()]
    recette = None
    try:
        if not args.no_recette and lanes:
            cache: dict[int, dict] = {}

            def fetch(n: int) -> dict:
                if n not in cache:
                    cache[n] = rd.gh_issue(n)
                return cache[n]
            listed = rd.gh_list()

            def recette(lane: str) -> dict:
                return rd.run(lane, rd.DEFAULT_WINDOW_DAYS, now, list_issues=lambda: listed, fetch_issue=fetch)
        result = board(_read_json(args.belt_json), lanes, _load_previous(args.previous), now, recette=recette)
    except (subprocess.CalledProcessError, FileNotFoundError, json.JSONDecodeError) as exc:
        print(f"UNKNOWN: belt_queues injoignable ({type(exc).__name__})")
        return 2
    print(json.dumps(result, ensure_ascii=False, indent=1) if args.json else render_board(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
