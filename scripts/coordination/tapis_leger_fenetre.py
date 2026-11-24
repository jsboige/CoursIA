#!/usr/bin/env python3
"""La fenetre SERVIE de la voie leger : cap de livraisons, qualification, rapport.

Ce module est **extrait** de `coordination.tapis_leger` pour tenir le plafond de
lignes de ce module (meme geste que l'extraction de `tapis_leger_texte`) : la fin
du tirage -- le cap de livraisons, la **qualification de la fenetre** et le
rapport -- y vit desormais.

**La qualification precede le service** (dispatch `c0030` du coordinateur,
24/11) : la lane ne recoit que des grains **CONFIRMES** sur leur FIL COMPLET.
Mesure du 24/11 sur la fenetre reelle d'une lane (24 candidats) : la
qualification ecarte **16 des 24** (RELACHE, RECLAMEE, GEL, LIVREE, PLAFOND,
EPAISSE) et n'en confirme que **8** -- la file rendue sans elle etait servie a
deux tiers de grains que la qualification refusait ensuite. Un refus porte son
code et son motif ; un grain **non qualifie** n'est PAS servi (fail-CLOSED :
une decision qui n'a pas pu etre prise refuse le grain).

**Une file confirmee VIDE n'est pas un service** (revue du 24/11) : quand la
qualification ne confirme aucun grain — le mur atteint avant tout verdict, ou
une fenetre entierement refusee — le **repli chronologique** prend le relais,
comme le fait le cap de livraisons. Les grains **non qualifies** restent
DECLARES dans le rapport ; aucun n'est servi en silence.
"""
from __future__ import annotations

import sys
import time
from datetime import datetime
from pathlib import Path

from coordination import tapis_cap_livraisons, tapis_labels, tapis_repli
from coordination import tapis_qualification as tq
from coordination import tapis_universel
from coordination.tapis_marqueurs import _age, _iso, lane_de_pr

#: La qualification a son PROPRE mur : le mur global borne la LECTURE du
#: pool, celui-ci borne la LECTURE DES FILS. Les deux sont sequentiels, jamais
#: simultanes -- le total du tirage reste borne (2 x 60 s).
MUR_QUALIFICATION_S = 60


def qualifier(file: list, lane: str, maintenant: datetime, jours: int,
              prs: list[dict], run) -> tuple[list, dict, Exception | None]:
    """Qualifie la fenetre servie sur le FIL COMPLET de chaque grain.

    Rend `(file_confirmee, qualif, erreur)`. L'erreur n'est pas un verdict :
    elle rend la main au repli chronologique -- une qualification en panne ne
    sert **jamais** une file non qualifiee.
    """
    debut = time.monotonic()
    nums = [e.numero for e in file]
    try:
        servis, ecartees, illisibles, arrete, appels, chrono = tq.qualifier(
            nums, lane, maintenant, jours, prs, run,
            debut + MUR_QUALIFICATION_S, debut=debut)
    except Exception as exc:  # noqa: BLE001 - une qualification en panne ne sert rien
        return file, {}, exc
    confirmes = {e.numero for e in servis}
    qualif = {
        "candidats": len(nums), "servis": len(confirmes),
        "ecartees": [{"numero": n, "code": v.get("code"), "motif": v.get("motif")}
                     for n, v in sorted(ecartees.items())],
        "illisibles": list(illisibles),
        "non_qualifies": [n for n in nums
                          if n not in confirmes and n not in ecartees],
        "appels": appels, "secondes": chrono.get("secondes"),
        "premier_servable_s": chrono.get("premier_servable_s"),
        "budget_epuise": bool(arrete),
    }
    return [e for e in file if e.numero in confirmes], qualif, None


def rapport(lane: str, graine: str, maintenant: datetime, metas: list[dict],
            duree: float, secondes: float, budget_s: float, etats_: list,
            file: list, prs: list[dict], origami: dict,
            phases: dict | None = None, fenetre: dict | None = None,
            qualif: dict | None = None) -> dict:
    """Le rapport du tirage leger : l'etat de chaque grain et l'action a faire."""
    vos = sorted((pr for pr in prs if lane_de_pr(pr) == lane),
                 key=lambda pr: pr.get("created_at") or "")
    r = tapis_universel.rapport(etats_=etats_, file=file, lane=lane,
                                 maintenant=maintenant, lecture={},
                                 ecartees=tapis_labels.ecartees(metas))
    r.update({
        "graine": graine, "voie": "leger", "pool": len(metas),
        "fenetre": fenetre or {},
        "lecture": {"issues": len(metas), "secondes": round(secondes, 1),
                    "selection_s": duree, "budget_s": budget_s,
                    "phases": phases or {}, "budget_epuise": False},
        "vos_prs": [{"numero": pr["number"], "titre": pr.get("title") or "",
                     "age_j": _age(maintenant, pr.get("created_at"), 86400)}
                    for pr in vos],
        "qualification": {
            "organe": "scripts/coordination/tapis_prise_en_charge.py",
            "vagues": "scripts/coordination/tapis_vagues.py : la file se remplit",
            "quand": "avant le service, sur la fenetre servie",
            "ecarts": "les neuf regles se decident sur le fil complet",
            **(qualif or {}),
        },
        "origami_parking": origami,
    })
    return r


def servir(classe: dict, file: list, fenetre: dict, origami: dict, lane: str,
           grains: int, maintenant: datetime, jours: int, graine: str,
           depot: Path, run, phases: dict, secondes: float,
           budget_s: float) -> tuple[dict, int]:
    """Le cap de livraisons, la qualification, puis le rapport de la fenetre.

    Trois temps dans l'ordre : le CAP ecarte les livraisons d'EPIC trop
    recentes (fail-OPEN), la QUALIFICATION confirme chaque grain sur son fil
    complet, et le RAPPORT publie les refus -- une exclusion n'est jamais
    silencieuse.
    """
    file, temoins_cap, cap_mesure, rendu = tapis_cap_livraisons.passer_et_replir(
        file, classe["grains"] + classe["conteneurs"], lane, maintenant,
        classe["prs"], run=run, pool_ouvert=bool(classe["grains"]),
        repli=lambda: tapis_repli.replir(lane, grains, maintenant, jours, graine, depot))
    if rendu is not None:
        return rendu
    file, qualif, erreur = qualifier(file, lane, maintenant, jours,
                                     classe["prs"], run)
    if erreur is not None:
        print(f"Qualification en echec ({erreur}) : repli chronologique.",
              file=sys.stderr)
        return tapis_repli.replir(lane, grains, maintenant, jours, graine, depot)
    if not file:
        # Une file CONFIRMEE VIDE n'est pas un service : la lane s'eteint
        # (mandat #28114, « file sans fin par lane »). Deux causes, un meme
        # geste : le mur atteint avant tout verdict, ou une fenetre
        # entierement refusee (mesure du 24/11 : 16 des 24 candidats refuses,
        # pour une marge de 3 -- elle est mince). Le repli chronologique prend
        # le relais, comme le fait le cap de livraisons ; les grains NON
        # QUALIFIES restent DECLARES dans le rapport, jamais servis en
        # silence (fail-CLOSED).
        r, code = tapis_repli.replir(lane, grains, maintenant, jours, graine,
                                     depot)
        q = dict(r.get("qualification") or {})
        q.update(qualif or {})
        q["repli"] = ("file confirmee vide : repli chronologique")
        r["qualification"] = q
        return r, code
    r = rapport(lane, graine, maintenant, classe["metas"],
                phases["selection_s"], secondes, budget_s, classe["etats"],
                file, classe["prs"], origami, phases, fenetre, qualif)
    r["cap_livraisons"] = {"mesure": cap_mesure, "ecartes": temoins_cap,
                           "fenetre_j": tapis_cap_livraisons.FENETRE_J}
    return r, 0


def texte_fenetre(fen: dict) -> list[str]:
    """Les lignes de la fenetre : selection par age, blocs, non-visites."""
    lignes = []
    if fen.get("ordre") == "age":
        seuil = (fen.get("age") or {}).get("seuil_h", 72)
        lignes.append(f"Selection par AGE (mandat du 22/11) : les issues "
                      f"anciennes d'abord ; une issue de moins de {seuil} h "
                      f"va en fin de file ; "
                      f"{(fen.get('age') or {}).get('exclus', 0)} issue(s) "
                      f"deja servie(s) en attente de verdict, laisses de cote.")
    if fen.get("blocs", 1) > 1:
        lignes.append(f"Fenetre : bloc {fen['bloc']}/{fen['blocs']} du pool classe "
                      f"(taille {fen['taille']}) -- la fenetre avance d'un bloc par "
                      f"tranche de 4 h : le pool entier est couvert en "
                      f"{fen['blocs']} tranches.")
    non_visites = fen.get("non_visites") or []
    if non_visites:
        apercu = ", ".join(f"#{n}" for n in non_visites[:12])
        suite = " ..." if len(non_visites) > 12 else ""
        lignes.append(f"Fenetre : {len(non_visites)} numero(s) du pool non visite(s) "
                      f"a cette tranche -- delai max de requalification "
                      f"{fen.get('delai_max_h')} h : {apercu}{suite}.")
    elif fen.get("delai_max_h"):
        lignes.append(f"Fenetre : pool entier visite -- delai max de "
                      f"requalification {fen.get('delai_max_h')} h.")
    return lignes


def texte_qualification(q: dict) -> list[str]:
    """Les lignes de la qualification : mesure, refus (code + motif), non qualifies."""
    lignes = [f"\nQualification : {q['organe']} -- {q['quand']} ; {q['ecarts']}."]
    if q.get("candidats") is not None:
        lignes.append(f"Qualification de la fenetre servie : {q['candidats']} candidat(s) "
                      f"-> {q['servis']} confirme(s) sur le fil complet "
                      f"({q.get('appels')} appel(s), {q.get('secondes')} s"
                      + (", budget epuise" if q.get("budget_epuise") else "") + ").")
    for e in q.get("ecartees") or []:
        lignes.append(f"  #{e['numero']}  ecarte -- {e['code']} : {e['motif']}")
    if q.get("non_qualifies"):
        apercu = ", ".join(f"#{n}" for n in q["non_qualifies"][:12])
        suite = " ..." if len(q["non_qualifies"]) > 12 else ""
        lignes.append(f"  {len(q['non_qualifies'])} grain(s) non qualifies (mur) : "
                      f"{apercu}{suite} -- ils reviendront au tour suivant.")
    if q.get("repli"):
        lignes.append(f"  {q['repli']} -- la file confirmee etait vide ; "
                      f"la file servie vient du repli chronologique.")
    return lignes
