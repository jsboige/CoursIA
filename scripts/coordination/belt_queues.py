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
import grain_tag as gt  # noqa: E402
import recette_due as rd  # noqa: E402
import tirage_journal as tj  # noqa: E402

_SERIES_RE = re.compile(r"MyIA\.AI\.Notebooks/([A-Za-z][\w.-]*)(?:/([A-Za-z][\w.-]*))?")
_TAG_RE = re.compile(r"^\s*\[([^\]]{1,30})\]")
_VISION_RE = re.compile(r"\b(QA visuel|rendu visuel|slides?|galerie|capture|screenshot|image[s]? g[ée]n[ée]r)", re.I)
_VLLM_RE = re.compile(r"(192\.168\.0\.47|:5002\b|vLLM local|inf[ée]rence locale)", re.I)
#: Reference a une issue dans le TITRE d'une PR : la convention des lanes
#: est `Type(scope,#N): ...` ou `Type(#N): ...`. Le numero est le sujet
#: traite, pas un renvoi de PR (celles-ci sont citees en toutes lettres).
_TITLE_ISSUE_RE = re.compile(r"#(\d+)")


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


def lane_served_since(payload: dict, lane: str, since: str,
                      pr_states: dict[int, str] | None = None) -> bool:
    """La lane a rendu la main depuis la repartition (``[DELIVERED]``, ``[RELEASED]``, ``[DONE]``).

    Un ``[CLAIMED]`` seul ne vide pas l'assiette : le coordinateur le pose lui-meme
    au dispatch, et une issue prise mais pas rendue reste a servir.

    La main rendue se lit par le reducteur v2 (#12386), le meme que
    ``recette_due.held_by`` : un ``[DELIVERED]`` dont la PR est encore OUVERTE
    garde l'issue dans l'assiette, car la substance est en vol et la lane la tient.
    Une PR MERGED (claim verrouille) ou fermee, un ``[DELIVERED]`` sans PR, un
    ``[RELEASED]`` ou un ``[DONE]`` la rendent. ``pr_states`` injecte l'etat des
    PRs (tests) ; absent, le reducteur le lit par ``gh``.
    """
    events = clc._sort_events(payload)
    if not any(ev.lane == lane and ev.get("action") == "close" and (ev.created_at or "") >= since
               for ev in events):
        return False
    active, _ = clc.compute_active_claims(events, pr_states=pr_states)
    held = active.get(lane)
    return held is None or bool(held.get("locked"))


def measure_plates(previous: dict, fetch_issue, pr_states: dict[int, str] | None = None) -> dict[str, dict]:
    """Ce qui reste dans l'assiette de chaque lane depuis la repartition precedente.

    Une issue **illisible** n'interrompt pas la mesure (#23115) : l'echec est
    consigne et nomme, l'issue **reste en assiette** (fail-closed — une issue
    qu'on n'a pas pu lire ne peut pas etre declaree servie), et les autres
    items sont mesures normalement. Seul le binaire ``gh`` absent remonte
    (c'est un incident global, pas un incident de lecture).
    """
    since = previous["assigned_at"]
    plates = {}
    for lane, info in previous["lanes"].items():
        remaining = []
        unreadable = []
        for it in info["queue"]:
            try:
                payload = fetch_issue(it["number"])
            except (subprocess.CalledProcessError, json.JSONDecodeError) as exc:
                unreadable.append({"number": it["number"], "error": error_label(exc)})
                remaining.append(it)
                continue
            if payload.get("state", "OPEN").upper() != "OPEN" or lane_served_since(payload, lane, since, pr_states):
                continue
            remaining.append(it)
        plates[lane] = {"assigned": len(info["queue"]), "remaining": remaining,
                        "arc": info.get("arc"), "unreadable": unreadable}
    return plates


def error_label(exc: BaseException) -> str:
    """Cause courte et nommable d'un echec de lecture (#23115).

    Le message doit permettre de reconnaitre l'incident sans ouvrir les
    journaux : numero de l'issue cote appelant, cause ici.
    """
    if isinstance(exc, subprocess.CalledProcessError):
        stderr = (exc.stderr or "").strip().splitlines()
        tail = stderr[-1][:160] if stderr else ""
        return f"gh rc={exc.returncode}" + (f" : {tail}" if tail else "")
    if isinstance(exc, json.JSONDecodeError):
        return f"json illisible ({exc.msg})"
    if isinstance(exc, FileNotFoundError):
        return "binaire gh introuvable"
    return type(exc).__name__


# --- adherence au tapis (issue #25082, point D) ------------------------------
#
# Mesure du 2026-11-07 (issue #25082, mesure 1) : sur 67 PRs ouvertes
# depuis le 06/11 16:00Z, **16** traitaient une issue de la file de leur
# lane. Le chiffre ne distinguait pas trois provenances que le coordinateur
# a ensuite precises (commentaire du 07/11 16:30Z) :
#
#   1. issue de la file ASSIGNEE (tirage enregistre par `belt_queues.py
#      record`) ;
#   2. issue TIREE par la lane elle-meme au tapis (son propre tirage) ;
#   3. HORS tapis (dispatch nominatif, reparation de PR, initiative).
#
# La provenance 2 n'innocente pas le tirage : c'est le tapis lui-meme qui
# ne met pas la consolidation en tete (mesures 3 a 6). Elle se distingue de
# 1 pour savoir si une lane travaille SA file ou le tapis, et de 3 pour
# voir le travail hors tapis.

ADHERENCE_ASSIGNED = "file"
ADHERENCE_SELF_DRAWN = "tapis"
ADHERENCE_OFF_BELT = "hors_tapis"
# 4e provenance (#25082, revue du 07/11) : le journal de tirage est PAR
# MACHINE ; pour une lane d'une autre machine, la part tapis/hors d'une PR
# hors file est NON MESURABLE localement. Ces PRs tombent dans ce seau --
# jamais dans hors_tapis, qui se lirait « la lane n'a rien fait du tapis »
# alors que c'est la lecture qui est impossible.
ADHERENCE_NON_MEASURED = "non_mesure"
ADHERENCE_PROVENANCES = (ADHERENCE_ASSIGNED, ADHERENCE_SELF_DRAWN,
                          ADHERENCE_OFF_BELT, ADHERENCE_NON_MEASURED)


def _local_machine() -> str:
    """La machine locale, au format du segment machine d'une lane.

    Reutilise la normalisation de ``gh_identity.machine_hostname``
    (``COMPUTERNAME`` prime sur Windows, cf #17418) -- une fonction locale
    substituable en test plutot qu'un appel direct a l'import.
    """
    import gh_identity as ghi
    return ghi.machine_hostname()


def gh_open_prs() -> list[dict]:
    """Les PRs OUVERTES du depot, avec leur corps et leur date de creation.

    Le corps porte le tag `Grain:` (l'attribution de lane -- le login
    GitHub est partage) et les references d'issues ; la date de creation
    borne la fenetre « depuis le tirage precedent ».
    """
    out = subprocess.run(
        ["gh", "pr", "list", "--repo", rd.REPO, "--state", "open",
         "--limit", "500", "--json",
         "number,title,body,createdAt,closingIssuesReferences"],
        capture_output=True, text=True, encoding="utf-8", check=True)
    return json.loads(out.stdout)


def pr_issue_refs(pr: dict) -> set[int]:
    """Les issues qu'une PR traite.

    Trois sources, par ordre de fidelite :

    - `closingIssuesReferences` : la parse de GitHub lui-meme ;
    - les references NON fermantes du body (`See #N`, `Part of #N`) : la
      livraison d'une lane passe majoritairement par elles -- elles ne
      ferment pas, et le commit les ecrit ;
    - le numero du titre : la convention des lanes est `Type(scope,#N): ...`.

    On ne lit PAS les references fermantes en prose : leur detecteur scanne
    le texte entier, et une citation (`voir #12345` dans une explication)
    se lirait comme une issue traitee.
    """
    refs: set[int] = set()
    for ref in pr.get("closingIssuesReferences") or []:
        n = ref.get("number")
        if n:
            refs.add(int(n))
    for hit in gt.find_non_closing_refs(pr.get("body") or ""):
        refs.add(int(hit["number"]))
    for m in _TITLE_ISSUE_RE.finditer(pr.get("title") or ""):
        refs.add(int(m.group(1)))
    return refs


def pr_lane(pr: dict) -> str | None:
    """La lane qui porte la PR, lue dans son tag `Grain:`.

    Le login GitHub est partage (`jsboige`) : le tag est la seule source
    d'attribution par lane (spec #18832, reprise par
    `belt_service_balance.attribute_service`). Une PR sans tag n'est pas
    attribuee : elle est comptee a part, jamais repartie au hasard.
    """
    tag = gt.parse_grain_tag(pr.get("body") or "")
    if not tag:
        return None
    return tag.get("lane") or None


def belt_draw_numbers(lane: str) -> set[int] | None:
    """Les issues que la lane a RETENUES d'un tirage au tapis (journal local).

    La provenance « tiree par la lane » est l'issue RETENUE du tirage
    (``retained``), pas les candidates montrees : le tapis montre jusqu'a 50
    issues par tour, la lane n'en prend qu'une. Compter les candidates
    gonflerait l'adherence -- toute PR traitant une issue simplement MONTREE
    par un tirage passerait pour du tapis (#25082, revue du 07/11).

    Le journal est PAR MACHINE (`%LOCALAPPDATA%/CoursIA/tirage_journal`) :
    une mesure prise sur ai-01 ne voit que les tirages d'ai-01. Pour une
    lane dont la machine n'est pas la machine locale, on retourne donc
    ``None`` (non mesure) -- jamais un ensemble vide, qui se lirait « la
    lane n'a rien tire » alors que c'est la lecture qui est impossible.
    """
    if lane.split(":", 1)[0] != _local_machine():
        return None
    try:
        records = tj.read_journal()
    except (OSError, json.JSONDecodeError):
        return set()
    out: set[int] = set()
    for rec in records:
        if rec.lane != lane or rec.mode != "belt":
            continue
        if rec.retained is not None:
            out.add(int(rec.retained))
    return out


def measure_adherence(previous: dict | None, lanes: list[str], *,
                       open_prs: list[dict] | None = None,
                       belt_draws: dict[str, set[int] | None] | None = None,
                       measured: bool = True) -> dict:
    """La part des PRs d'une lane qui traite une issue de SON tapis.

    La fenetre est celle du tour : les PRs creees depuis la repartition
    precedente (`previous["assigned_at"]`). Une PR sans date de creation
    n'entre pas dans la mesure : elle est comptee a part, jamais imputee.

    Trois provenances disjointes, chacune Named (cf. les constantes) :
    `file`, `tapis`, `hors_tapis` -- plus `non_mesure` : le journal de
    tirage est PAR MACHINE ; quand ``belt_draws[lane]`` vaut ``None``, la
    part tapis/hors des PRs hors file de cette lane est inconnue ICI.
    Elles tombent dans ce seau (jamais dans `hors_tapis`, qui se lirait
    « la lane n'a rien fait du tapis »), `self_drawn` rend ``None`` et
    l'adherence n'est pas calculee. Le taux d'adherence est
    `(file + tapis) / total` : il dit si une lane travaille le tapis ou
    autre chose, sans pretendre que le tapis lui-meme est bien oriente.
    """
    out: dict[str, dict] = {}
    if not previous:
        return {"measured": False, "reason": "aucune repartition precedente",
                "lanes": out, "sans_lane": 0}
    since = previous.get("assigned_at") or ""
    queue_by_lane = {
        lane: {int(it["number"]) for it in (info.get("queue") or [])}
        for lane, info in (previous.get("lanes") or {}).items()
    }
    draws = belt_draws or {}
    # None (cle absente comprise) = le journal local ne couvre pas la
    # machine de la lane : echec-clos sur la non-mesure, jamais un zero
    # qui se lirait « la lane n'a rien tire au tapis ».
    journal_covers = {lane: draws.get(lane) is not None for lane in lanes}
    buckets: dict[str, dict[str, list[int]]] = {}
    sans_lane: list[int] = []
    for pr in open_prs or []:
        created = pr.get("createdAt") or ""
        if since and created and created < since:
            continue
        lane = pr_lane(pr)
        if not lane:
            sans_lane.append(int(pr.get("number") or 0))
            continue
        if lane not in lanes:
            continue
        refs = pr_issue_refs(pr)
        queue = queue_by_lane.get(lane, set())
        drawn = draws.get(lane) or set()
        if refs & queue:
            kind = ADHERENCE_ASSIGNED
        elif not journal_covers.get(lane, False):
            kind = ADHERENCE_NON_MEASURED
        elif refs & drawn:
            kind = ADHERENCE_SELF_DRAWN
        else:
            kind = ADHERENCE_OFF_BELT
        buckets.setdefault(lane, {k: [] for k in ADHERENCE_PROVENANCES})
        buckets[lane][kind].append(int(pr.get("number") or 0))
    for lane in lanes:
        b = buckets.get(lane) or {k: [] for k in ADHERENCE_PROVENANCES}
        total = sum(len(v) for v in b.values())
        covers = journal_covers.get(lane, False)
        adhere = (len(b[ADHERENCE_ASSIGNED]) + len(b[ADHERENCE_SELF_DRAWN]))
        out[lane] = {
            "measured": measured,
            "assigned": len(b[ADHERENCE_ASSIGNED]),
            "self_drawn": len(b[ADHERENCE_SELF_DRAWN]) if covers else None,
            "off_belt": len(b[ADHERENCE_OFF_BELT]),
            "non_mesure": len(b[ADHERENCE_NON_MEASURED]),
            "total": total,
            "adherence": round(adhere / total, 3) if (total and covers) else None,
            "prs": b,
        }
    return {"measured": measured, "since": since, "lanes": out,
            "sans_lane": len(sans_lane),
            "draw_journal_scope": "machine locale"}


def gh_issue_state(number: int) -> dict:
    out = subprocess.run(["gh", "issue", "view", str(number), "--repo", rd.REPO,
                          "--json", "number,state,comments"],
                         capture_output=True, text=True, encoding="utf-8", check=True)
    return json.loads(out.stdout)


def board(belt: dict, lanes: list[str], previous: dict | None, now: datetime,
          fetch_issue=None, recette=None, open_prs=None, belt_draws=None,
          adherence_measured: bool = True) -> dict:
    # `fetch_issue` est resolu a l'appel (et non a la definition) pour que le
    # defaut reste le vrai lecteur `gh` tout en restant substituable en test.
    fetch_issue = fetch_issue or gh_issue_state
    plates = measure_plates(previous, fetch_issue) if previous else {}
    on_plate = {it["number"] for p in plates.values() for it in p["remaining"]}
    picks = [p for p in belt.get("picks", []) if p["number"] not in on_plate]
    incidents: list[dict] = []
    out_lanes = {}
    all_lanes = list(dict.fromkeys(lanes + list(plates)))
    # #25082 point D -- l'adherence au tapis, mesuree par lane.
    adherence = measure_adherence(previous, all_lanes, open_prs=open_prs,
                                   belt_draws=belt_draws,
                                   measured=adherence_measured)
    for lane in all_lanes:
        plate = plates.get(lane)
        for inc in (plate["unreadable"] if plate else []):
            incidents.append({"kind": "issue", "lane": lane, **inc})
        rec = None
        if recette:
            try:
                rec = recette(lane)
            except (subprocess.CalledProcessError, json.JSONDecodeError) as exc:
                # La recette d'une lane ne doit pas tuer le tableau des autres
                # (#23115) : elle est declaree illisible, elle est nommee.
                rec = {"verdict": "UNKNOWN", "reason": error_label(exc)}
                incidents.append({"kind": "recette", "lane": lane, "number": None,
                                  "error": error_label(exc)})
        out_lanes[lane] = {
            "assigned": plate["assigned"] if plate else 0,
            "remaining": plate["remaining"] if plate else [],
            "arc": plate["arc"] if plate else None,
            "recette": rec,
            "adherence": adherence["lanes"].get(lane),
        }
    # #24373 : les EPICs Origami dont le pli suivant n'est pas deplie ne sont
    # pas servis aux lanes. Le tableau les montre : c'est la que le
    # coordinateur voit ce qui attend SON geste.
    origami = belt.get("origami_parking") or {}
    parked = []
    for item in origami.get("details") or []:
        if item.get("parked"):
            parked.append({"number": item.get("epic"),
                           "title": item.get("title"),
                           "next_pli": item.get("next_pli"),
                           "reason": item.get("reason")})
    return {"drawn": len(belt.get("picks", [])), "families": group_picks(picks, now), "lanes": out_lanes,
            "previous_at": previous["assigned_at"] if previous else None,
            "adherence": adherence,
            "origami_parked": parked,
            "origami_parking": {"measured": bool(origami.get("measured")),
                                "reason": origami.get("reason"),
                                "count": len(parked)},
            "unreadable": incidents}


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
        # #25082 point D -- l'adherence au tapis, dans la meme ligne : le
        # coordinateur voit la file ET ce que la lane a reellement travaille.
        adh = info.get("adherence") or {}
        if adh and adh.get("total"):
            pct = adh.get("adherence")
            pct_txt = "n/a" if pct is None else f"{round(pct * 100)} %"
            if adh.get("self_drawn") is None:
                # Journal de tirage local : pour une lane d'une autre
                # machine, la part tapis de ses PRs hors file n'est pas
                # mesurable ici. Rendu n/m avec la reserve nommee -- jamais
                # un zero nu qui se lirait « la lane n'a rien fait du
                # tapis » (#25082, revue du 07/11).
                tapis_txt = (f"tapis 0/{adh.get('non_mesure', 0)} "
                             f"(journal local)")
            else:
                tapis_txt = f"tapis {adh.get('self_drawn', 0)}"
            lines.append(
                f"      adherence : file {adh.get('assigned', 0)} / "
                f"{tapis_txt} / "
                f"hors {adh.get('off_belt', 0)} "
                f"(= {pct_txt} sur {adh.get('total')} PR(s))")
        elif adh and not adh.get("measured"):
            lines.append("      adherence : NON MESUREE")
    # #24373 : ce qui attend le geste du coordinateur (depliage d'un pli).
    parked = b.get("origami_parked") or []
    origami = b.get("origami_parking") or {}
    lines += ["", "# Origami en attente de depliage"]
    if not origami.get("measured"):
        lines.append(f"  (non mesure : {origami.get('reason') or 'inconnu'})")
    elif not parked:
        lines.append("  (aucun)")
    else:
        for item in parked:
            next_pli = f" -- pli {item['next_pli']}" if item.get("next_pli") else ""
            lines.append(f"  #{item['number']}{next_pli} {item.get('title') or ''}")
    unreadable = b.get("unreadable") or []
    if unreadable:
        lines += ["", "# Lectures impossibles (la mesure a echoue pour ces la)"]
        for inc in unreadable:
            what = f"#{inc['number']}" if inc.get("number") else "tour de recette"
            lines.append(f"  {inc['lane']} : {what} — {inc['error']}")
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
        # #25082 point D -- les PRs ouvertes de la flotte (attribution par le
        # tag `Grain:`) et les tirages que chaque lane a faits au tapis.
        # Une lecture impossible est une ABSENCE DE MESURE : elle est
        # nommee, jamais convertie en un zero qui se lirait « la lane n'a
        # rien fait du tapis ».
        open_prs = None
        adherence_measured = True
        try:
            open_prs = gh_open_prs()
        except (subprocess.CalledProcessError, FileNotFoundError,
                json.JSONDecodeError) as exc:
            adherence_measured = False
            print(f"(adherence NON MESUREE : lecture des PRs ouvertes "
                  f"impossible -- {error_label(exc)})", file=sys.stderr)
        belt_draws = {lane: belt_draw_numbers(lane) for lane in lanes}
        result = board(_read_json(args.belt_json), lanes, _load_previous(args.previous), now, recette=recette,
                       open_prs=open_prs, belt_draws=belt_draws,
                       adherence_measured=adherence_measured)
    except (subprocess.CalledProcessError, FileNotFoundError, json.JSONDecodeError) as exc:
        print(f"UNKNOWN: belt_queues injoignable ({type(exc).__name__}) — {error_label(exc)}")
        return 2
    unreadable_issues = [i for i in result.get("unreadable") or [] if i["kind"] == "issue"]
    assigned = sum(info.get("assigned", 0) for info in result["lanes"].values())
    if assigned and len(unreadable_issues) >= assigned:
        # Toutes les assiettes sont illisibles : le tableau ne mesurerait rien.
        # UNKNOWN honnete, nomme — plutot qu'un tableau vide qui se lit comme
        # « aucune issue servie » (#23115).
        first = unreadable_issues[0]
        print(f"UNKNOWN: belt_queues illisible ({len(unreadable_issues)}/{assigned} issues de "
              f"l'assiette non lisibles) — premiere : #{first['number']} ({first['error']})")
        return 2
    print(json.dumps(result, ensure_ascii=False, indent=1) if args.json else render_board(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
