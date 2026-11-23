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
  3. puis celle dont la derniere communication de flotte est la plus ancienne.

Un marqueur d'ouverture de claim (``[CLAIMED]``, ``[CLAIMED-AMEND]``) n'est pas
une communication adressee au validateur : un commentaire de flotte qui ne porte
QUE de tels marqueurs ne compte pas dans la derniere communication de flotte
(#21988, voie b). Une lane qui pose un ``[CLAIMED]`` puis l'abandonne ne rend
donc pas la balle au validateur -- l'issue reste servable, la balle reste chez
la flotte tant qu'aucune livraison (``[DELIVERED]``, reponse en prose) ou
cloture (``[DONE]``) n'est postee. Relacher proprement reste le geste recommande
(``[RELEASED]``), mais l'organe ne deserte plus l'issue en son absence.

BALLE CHEZ LE VALIDATEUR (#21279) : quand le dernier message de TOUTES les issues
``recette`` vient de la flotte, le validateur est muet et la balle est chez lui --
un tour de lane ne produirait qu'une notification de plus pour une personne hors
flotte. L'organe rend alors rc 0 avec une ligne explicite
``WAITING-VALIDATOR #N depuis <ts>`` (ts = dernier message de flotte sur l'issue
dont l'attente est la plus longue) au lieu de nommer une issue a servir.

Le validateur se declare dans le body de l'issue par une ligne
``Validateur : @login`` ; a defaut, tout auteur hors flotte compte comme validateur.

LIMITE CLOSE (#21279, revue Hermes du 2026-10-22) : l'etat « balle chez le
validateur » se lisait sur l'ORDRE DES MESSAGES, pas sur l'etat du claim, donc un
``[CLAIMED]`` de flotte pose puis abandonne restait le dernier message de flotte
et la balle demeurait chez le validateur alors que personne n'attendait. #22105 a
livre le correctif durable : les marqueurs d'ouverture de claim sont exclus du
calcul « la flotte a parle en dernier ». La resolution de ce merge a retire le
paragraphe de limite et le test qui l'encodait.

REGISTRE DES DESTINATAIRES (``--board``, demande user 2026-11-16) : releve d'un
geste de TOUTES les issues ``recette``, sans lane. Chaque body declare a qui
l'issue s'adresse et si son lien est parti :
    Destinataires : Frederic (MOA externe) ; Odile (MOA externe)
    Transmission : 2026-11-16      (toute valeur non datee = non transmis)
Le registre est l'ensemble de ces lignes, jamais une liste parallele. Alertes :
``A TRANSMETTRE`` (geste du mainteneur), ``REPONSE DUE PAR LA FLOTTE``,
``DESTINATAIRE MUET`` (lien transmis, balle chez lui depuis plus de
``--silence-days``, defaut 14 : la relance passe par le canal du mainteneur).
rc du board : 0 = rien du cote flotte, 1 = une reponse de flotte est due,
2 = injoignable.

Sorties : rc 0 = rien a faire (tour fait, aucune issue ``recette``, ou balle chez
le validateur sur toutes les issues) ;
rc 1 = tour du, l'issue est nommee ; rc 2 = organe injoignable (fail-open : le
cycle continue, la ligne ``UNKNOWN`` le dit).

    python scripts/coordination/recette_due.py --lane myia-po-2023:CoursIA
    python scripts/coordination/recette_due.py --lane myia-po-2023:CoursIA --json
    python scripts/coordination/recette_due.py --board
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

# Registre des destinataires (demande user 2026-11-16) : chaque issue de recette
# declare dans son body a qui elle s'adresse et si son lien a ete transmis. Le
# registre EST l'ensemble de ces lignes : aucune liste parallele qui deriverait.
#   Destinataires : Frederic (MOA externe) ; Odile (MOA externe)
#   Transmission : 2026-11-16            (ou : a faire par le mainteneur)
_RECIPIENTS_RE = re.compile(r"^\s*\**\s*Destinataires\s*\**\s*:\s*\**\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE)
_TRANSMISSION_RE = re.compile(r"^\s*\**\s*Transmission\s*\**\s*:\s*\**\s*(.+?)\s*$", re.IGNORECASE | re.MULTILINE)
_DATE_RE = re.compile(r"^(\d{4}-\d{2}-\d{2})\b")

#: Au-dela, un destinataire qui a recu le lien et n'a rien dit est signale : la
#: relance passe par le canal du mainteneur, pas par une notification de plus.
DEFAULT_SILENCE_DAYS = 14.0

ListFetcher = Callable[[], list]
IssueFetcher = Callable[[int], dict]


def is_fleet(login: str | None) -> bool:
    if not login:
        return True
    return login in FLEET_LOGINS or login.endswith("[bot]")


def declared_validator(body: str) -> str | None:
    m = _VALIDATOR_RE.search(body or "")
    return m.group(1) if m else None


def declared_recipients(body: str) -> list[str]:
    """Destinataires declares par la ligne ``Destinataires :`` (separateur ``;``)."""
    m = _RECIPIENTS_RE.search(body or "")
    if not m:
        return []
    return [part.strip() for part in m.group(1).split(";") if part.strip()]


def declared_transmission(body: str) -> str | None:
    """Valeur brute de la ligne ``Transmission :``, ou None si absente."""
    m = _TRANSMISSION_RE.search(body or "")
    return m.group(1) if m else None


def transmitted_on(value: str | None) -> str | None:
    """Date de transmission si la valeur commence par AAAA-MM-JJ, sinon None.

    Tout autre texte (« a faire », « a confirmer ») compte comme NON transmis :
    l'organe ne devine pas une transmission qui n'est pas datee.
    """
    m = _DATE_RE.match((value or "").strip())
    return m.group(1) if m else None


def is_claim_only_fleet_comment(comment: dict) -> bool:
    """Vrai si le commentaire ne porte QUE des marqueurs d'ouverture de claim.

    Un ``[CLAIMED]`` / ``[CLAIMED-AMEND]`` s'adresse au plan de coordination de
    la flotte, pas au validateur : il ne lui donne rien a ecouter. Le commentaire
    de flotte qui n'en porte que de tels marqueurs n'est donc pas une
    communication (#21988, voie b). Grammaire reutilisee de
    ``check_lane_claim`` (ancrage ligne, blocs fences masques, payload depiege) :
    aucun parseur parallele.
    """
    events = clc._parse_claim_events(comment)
    return bool(events) and all(ev.get("action") == "open" for ev in events)


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
    # #21988 voie b : un claim n'est pas une communication adressee au
    # validateur -- il ne compte pas dans last_fleet, la balle ne lui revient
    # que sur une livraison, une reponse ou une cloture.
    last_fleet = max(
        (c.get("createdAt") or "" for c in comments
         if is_fleet((c.get("author") or {}).get("login"))
         and not is_claim_only_fleet_comment(c)),
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
        # La flotte a parle en dernier : le validateur doit repondre (#21279).
        # Ni la flotte ni le validateur n'ont parle : la balle est libre, l'issue
        # n'a jamais ete servie et la lane peut la prendre.
        "ball_with_validator": bool(last_fleet) and not (bool(last_validator) and last_validator > last_fleet),
        # Depuis quand le validateur attend : son dernier message de flotte, ou la
        # creation de l'issue si la flotte n'y a jamais parle (#21279).
        "waiting_since": last_fleet or payload.get("createdAt") or None,
        "held_by": held_by,
        "recipients": declared_recipients(payload.get("body") or ""),
        "transmission": declared_transmission(payload.get("body") or ""),
        "transmitted_on": transmitted_on(declared_transmission(payload.get("body") or "")),
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
    if all(s["ball_with_validator"] for s in states):
        # Le validateur est muet sur TOUTES les issues : la balle est chez lui.
        # Servir une issue ici ne produirait qu'une notification de plus pour une
        # personne hors flotte (#21279) -- l'organe rend rc 0 et nomme l'attente.
        waiter = min(states, key=lambda s: (s.get("waiting_since") or ""))
        since = "jamais" if last is None else f"il y a {last:.1f} j"
        return {"verdict": "WAITING-VALIDATOR", "issue": waiter["number"],
                "reason": f"aucun tour de recette depuis {window_days:g} j (dernier : {since}) ; "
                          f"la balle est chez le validateur sur les {len(states)} issue(s) de recette "
                          f"-- un tour de lane n'y change rien"}
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


def board_alerts(state: dict, now: datetime, silence_days: float = DEFAULT_SILENCE_DAYS) -> list[str]:
    """Ce qui demande un geste sur une issue de recette, nomme par qui le doit."""
    alerts: list[str] = []
    if not state.get("recipients"):
        alerts.append("DESTINATAIRES NON DECLARES (ligne Destinataires absente du body)")
    if not state.get("transmitted_on"):
        alerts.append("A TRANSMETTRE (mainteneur)")
    if state.get("ball_in_fleet_court"):
        age = _age_days(state.get("last_validator_comment"), now)
        alerts.append(f"REPONSE DUE PAR LA FLOTTE depuis {age:.1f} j" if age is not None
                      else "REPONSE DUE PAR LA FLOTTE")
    elif state.get("transmitted_on") and state.get("ball_with_validator"):
        age = _age_days(state.get("waiting_since"), now)
        if age is not None and age > silence_days:
            alerts.append(f"DESTINATAIRE MUET depuis {age:.1f} j (relance par le canal du mainteneur)")
    return alerts


def run_board(now: datetime, silence_days: float = DEFAULT_SILENCE_DAYS,
              list_issues: ListFetcher | None = None, fetch_issue: IssueFetcher | None = None) -> dict:
    """Le registre des issues de recette, releve d'un geste (demande user 2026-11-16)."""
    list_issues = list_issues or gh_list
    fetch_issue = fetch_issue or gh_issue
    states = sorted((assess_issue(fetch_issue(it["number"]), "", now) for it in list_issues()),
                    key=lambda st: st["number"] or 0)
    for st in states:
        st["alerts"] = board_alerts(st, now, silence_days)
    fleet_due = [st["number"] for st in states if st["ball_in_fleet_court"]]
    return {
        "verdict": "FLEET-REPLY-DUE" if fleet_due else "OK",
        "fleet_reply_due": fleet_due,
        "to_transmit": [st["number"] for st in states if not st["transmitted_on"]],
        "silent": [st["number"] for st in states
                   if any(a.startswith("DESTINATAIRE MUET") for a in st["alerts"])],
        "silence_days": silence_days,
        "issues": states,
    }


def _short_date(iso: str | None, now: datetime) -> str:
    if not iso:
        return "jamais"
    return f"{iso[:10]} ({_age_days(iso, now):.1f} j)"


def print_board(board: dict, now: datetime) -> None:
    for st in board["issues"]:
        title = (st.get("title") or "")[:100]
        print(f"#{st['number']} {title}")
        recipients = " ; ".join(st["recipients"]) if st["recipients"] else "NON DECLARES"
        print(f"   destinataires : {recipients}")
        print(f"   transmission  : {st['transmission'] or 'NON DECLAREE'}")
        print(f"   dernier message destinataire : {_short_date(st['last_validator_comment'], now)}"
              f" | dernier message flotte : {_short_date(st['last_fleet_comment'], now)}")
        if st["ball_in_fleet_court"]:
            ball = "flotte"
        elif st["ball_with_validator"]:
            ball = f"destinataire depuis {_short_date(st['waiting_since'], now)}"
        else:
            ball = "libre (personne n'a encore parle)"
        held = f" | tenue par {', '.join(st['held_by'])}" if st["held_by"] else ""
        print(f"   balle : {ball}{held}")
        print(f"   alertes : {' ; '.join(st['alerts']) if st['alerts'] else 'aucune'}")
    print(f"BOARD: {len(board['issues'])} issue(s) de recette ; "
          f"{len(board['to_transmit'])} a transmettre ; "
          f"{len(board['fleet_reply_due'])} reponse(s) due(s) par la flotte ; "
          f"{len(board['silent'])} destinataire(s) muet(s) > {board['silence_days']:g} j")


def _gh_json(args: list[str]):
    out = subprocess.run(["gh", *args], capture_output=True, text=True, encoding="utf-8", check=True)
    return json.loads(out.stdout)


def gh_list() -> list:
    return _gh_json(["issue", "list", "--repo", REPO, "--label", LABEL, "--state", "open",
                     "--limit", "50", "--json", "number"])


def gh_issue(number: int) -> dict:
    return _gh_json(["issue", "view", str(number), "--repo", REPO,
                     "--json", "number,title,body,comments,createdAt"])


def run(lane: str, window_days: float, now: datetime,
        list_issues: ListFetcher = gh_list, fetch_issue: IssueFetcher = gh_issue) -> dict:
    states = [assess_issue(fetch_issue(it["number"]), lane, now) for it in list_issues()]
    result = decide(states, window_days)
    result.update({"lane": lane, "window_days": window_days, "issues": states})
    return result


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--lane", help="lane machine:workspace, ex. myia-po-2023:CoursIA (requis hors --board)")
    ap.add_argument("--window-days", type=float, default=DEFAULT_WINDOW_DAYS)
    ap.add_argument("--board", action="store_true",
                    help="registre de toutes les issues de recette : destinataires, transmission, balle, alertes")
    ap.add_argument("--silence-days", type=float, default=DEFAULT_SILENCE_DAYS)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args(argv)
    now = datetime.now(timezone.utc)
    if args.board:
        try:
            board = run_board(now, args.silence_days)
        except (subprocess.CalledProcessError, FileNotFoundError, json.JSONDecodeError) as exc:
            print(f"UNKNOWN: registre de recette injoignable ({type(exc).__name__})")
            return 2
        if args.json:
            print(json.dumps(board, ensure_ascii=False, indent=2))
        else:
            print_board(board, now)
        return 1 if board["fleet_reply_due"] else 0
    if not args.lane:
        ap.error("--lane est requis hors --board")
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
        if result["verdict"] == "WAITING-VALIDATOR":
            waiter = next((s for s in result.get("issues") or []
                           if s.get("number") == result.get("issue")), {})
            since = waiter.get("waiting_since") or "inconnue"
            print(f"WAITING-VALIDATOR #{result.get('issue')} depuis {since}")
    return 1 if result["verdict"] == "DUE" else 0


if __name__ == "__main__":
    sys.exit(main())
