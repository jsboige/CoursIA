#!/usr/bin/env python3
"""Couverture des visites des issues ouvertes (#27590).

Mandat du 2026-11-16 (repris de `tapis_equilibre.py`) : « Toute issue doit etre
visitee au moins une fois avant qu'une autre le soit deux fois, a l'exception de
quelques issues anciennes de consolidation qui peuvent recevoir plusieurs
visites, et des marathon csharp et Rust qui recevront le fruit du travail du
nouveau harnais. Les issues recentes en particulier ne devraient pas recevoir
plus de visites que les anciennes. »

Mandat du 2026-11-20 : « Assure-toi bien que toutes les issues sont visitees et
avancees maintenant, ca doit faire partie des tests unitaires et de tes organes
de verification. » (verbatim : « Assure-toi bien que toutes les issues sont
visitées et avancées maintenant, ça doit faire partie des tests unitaires et de
tes organes de vérification. »)

Le tapis rapide n'equilibre que les issues SERVABLES par les workers (32 sur
443 a la mesure du 20/11) : une issue ecartee par un code (LIVREE, MERGEE,
COUVERTE, LABEL, GEL, RELACHEE...) depend d'un autre role, et aucun organe ne
mesurait si ce role la visite. Cet organe attribue a chaque issue ouverte le
role responsable de son prochain pas, mesure par role les issues sans visite du
tour et les visitees non avancees, et verifie l'invariant du 16/11 sur le pool
servable. Lecture seule : il relit la lecture du tapis (`gh_bulk`) sans nouvel
appel reseau, SAUF la mesure Origami -- celle du tirage (cache machine de
30 min, sinon mesure fraiche), sans quoi la classe « worker » compterait des
EPIC que le tirage ne sert jamais (mesure du 21/11 : cinq sur vingt et un).
Doc : docs/reference/tapis-rapide.md.

Usage : visit_coverage.py [--json] [--dashboard-line] [--lecture <dossier>]
    [--cache-s 3600] [--jours 45] [--lane myia-ai-01:CoursIA]
    (sorties : 0 tout est couvert ; 1 invariant viole ou issue d'urne / de
     revue sans visite au-dela du tour ; 2 lecture incomplete sans secours,
     jamais un faux 0)
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import replace
from datetime import UTC, datetime, timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import (
    gh_bulk,
    tapis_equilibre,
    tapis_origami,
    tapis_rapide,
    tapis_service,
)
from coordination.tapis_equilibre import FENETRE_J
from coordination.tapis_marqueurs import _dt, _iso, evenements
from coordination.tapis_rapide import LABEL_LIVRE, Etat

# Tous les roles, dans l'ordre du rapport ; `harnais` est exclu des agregats
# « hors marathon » (l'issue est servie par le harnais sk-agent, pas par le pool).
ROLES = ("worker", "urne", "revue", "harnais", "mainteneur", "attente",
         "hors-flotte", "autre")
ROLE_PAR_ECART = {
    "RECLAMEE": "worker", "LIVREE": "urne", "MERGEE": "urne", "COUVERTE": "revue",
    "GEL": "mainteneur", "RELACHEE": "attente", "PLAFOND": "attente",
    "ORIGAMI": "attente", "HORSFLOTTE": "hors-flotte",
}
LIMITE_LISTE = 20  # numeros cites par role ; les comptes, eux, restent entiers
_PR_RE = re.compile(r"#(\d+)")
_URGENCE = frozenset({"urne", "revue"})  # roles que le cycle doit servir lui-meme


def role(etat: Etat) -> str:
    """Le role responsable du prochain pas d'une issue ouverte.

    Un marathon est au harnais sk-agent QUEL QUE SOIT son ecart : la mesure du
    20/11 (443 issues hors marathons, 87 a zero visite dont 59 d'urne et 12 de
    revue) sort les 16 marathons des roles du pool, y compris ceux qui portent
    un ecart de livraison. Sinon, le role est deduit du code d'ecart ; un LABEL
    qui ne nomme pas `candidate-delivered` n'est pas l'urne : `autre`, avec son
    motif.
    """
    if tapis_equilibre.est_marathon(etat):
        return "harnais"
    if etat.ecart in (None, "RECLAMEE"):
        return "worker"
    if etat.ecart == "LABEL":
        return "urne" if LABEL_LIVRE in (etat.motif or "").lower() else "autre"
    return ROLE_PAR_ECART.get(etat.ecart, "autre")


def pr_de_revue(etat: Etat) -> int | None:
    """Le numero de la PR ouverte qui cite une issue COUVERTE, lu dans le motif."""
    m = _PR_RE.search(etat.motif or "")
    return int(m.group(1)) if m else None


def parer_origami(etats_: list[Etat], lecture: gh_bulk.Lecture, *,
                  reseau: bool = True) -> dict:
    """Le parcage Origami (#24373), comme dans `tapis_rapide.main()`.

    Mesure du 21/11 : sans cette ligne, l'organe comptait en role « worker »
    cinq EPIC Origami que le tirage ne sert jamais (le depliage d'un pli est
    reserve au coordinateur) -- la classe « worker » surestimait donc de cinq
    issues le travail que le tapis pouvait reellement servir. La mesure est
    celle du tirage : cache machine de 30 min, sinon mesure fraiche (fail-OPEN
    comme lui : une mesure en panne ne parque rien). Un rejeu hors ligne
    (`reseau=False`) ne mesure rien et ne parque rien.
    """
    parcs, etat = tapis_origami.mesurer(lecture, reseau=reseau)
    if parcs:
        tapis_rapide._parquer(etats_, parcs)
    return etat


def avancee(etat: Etat, lecture: gh_bulk.Lecture, maintenant: datetime,
            jours: int = FENETRE_J) -> str | None:
    """La preuve que l'issue a AVANCE dans la fenetre, ou None.

    Deux preuves seulement, celles que la lecture porte : un marqueur
    `[DELIVERED]` du fil date de la fenetre, ou un commit de
    `lecture.citations` qui la cite dans la fenetre.

    Ce que la mesure ne voit pas : une FERMETURE (la lecture ne contient que
    les issues ouvertes) ; une PR fusionnee sans commit cite (le squash cite sa
    PR, pas forcement l'issue) ; un `[DELIVERED]` plus ancien que les 12
    derniers commentaires lus (fil tronque, deja note « fil partiel » par le
    tapis) ; `[INFO] candidate-delivered`, que `_livree` reconnait comme
    livraison mais qui n'est pas retenu ici comme preuve d'avancee.
    """
    limite = maintenant - timedelta(days=jours)
    it = next((x for x in lecture.issues if x.get("number") == etat.numero), None)
    livres = [ev for ev in evenements((it or {}).get("comments") or [])
              if ev.marque == "DELIVERED" and ev.quand >= limite]
    if livres:
        ev = max(livres, key=lambda e: e.quand)
        return f"[DELIVERED] de {ev.lane or '?'} le {_iso(ev.quand)[:10]}"
    dates = [(d, c.get("sha") or "") for c in lecture.citations.get(etat.numero, [])
             if (d := _dt(c.get("date"))) and d >= limite]
    if dates:
        quand, sha = max(dates)
        return f"commit {sha[:7]} du {_iso(quand)[:10]}"
    return None


def _cle_creation(e: Etat) -> tuple[datetime, int]:
    """La plus ancienne d'abord, le numero pour departager."""
    return (_dt(e.cree_le) or datetime.min.replace(tzinfo=UTC), e.numero)


def _bornes(etats_: list[Etat]) -> list[int]:
    """Les numeros bornes a LIMITE_LISTE, tries par anciennete de creation."""
    return [e.numero for e in sorted(etats_, key=_cle_creation)[:LIMITE_LISTE]]


def invariant(etats_: list[Etat], maintenant: datetime) -> dict:
    """L'invariant du 16/11 sur le pool servable.

    Pool = servable (`ecart` None), hors claim propre et hors marathon : il
    existe une issue a zero visite pendant qu'une AUTRE en recoit deux ou plus.
    """
    pool = [e for e in etats_ if e.ecart is None and not e.mon_claim
            and not tapis_equilibre.est_marathon(e)]
    a_zero = [e.numero for e in sorted(pool, key=_cle_creation) if e.visites == 0]
    a_deux = [e.numero for e in sorted(pool, key=_cle_creation) if e.visites >= 2]
    return {"viole": bool(a_zero) and bool(a_deux), "maintenant": _iso(maintenant),
            "a_zero": a_zero, "a_deux": a_deux}


def atteignable(etats_: list[Etat], lane: str, maintenant: datetime,
                grains: int = 8) -> dict:
    """L'atteignabilite des issues jamais visitees par le tapis (#27590).

    Deux mesures, sur la MEME lecture que le bilan :

    - `tours` : combien de tours du tapis (de `grains` issues) il faut pour
      servir toutes les issues servables jamais visitees. Un nombre, pas une
      impression : la simulation sert la tete du tour et incremente ses
      visites, comme le ferait une lane.
    - `equite` : une issue deja visitée servie pendant qu'une issue jamais
      visitée attend encore -- la violation du mandat du 16/11 (« toute issue
      doit etre visitée au moins une fois avant qu'une autre le soit deux
      fois »). Doit etre vide.

    Les etats sont copies -- l'etat mesure n'est pas modifie par la
    simulation.
    """
    pool = [e for e in etats_ if e.ecart is None and not e.mon_claim
            and not tapis_equilibre.est_marathon(e)]
    a_zero = {e.numero for e in pool if e.visites == 0}
    etats_ = [replace(e) for e in etats_]
    servis: set[int] = set()
    equite: list[int] = []
    tours = 0
    while a_zero - servis and tours < 50:
        tours += 1
        avant = {e.numero: e.visites for e in etats_}
        tour = tapis_rapide.ordonner(etats_, lane, maintenant, grains)
        for e in tour:
            # Une issue deja visitée servie pendant qu'une issue jamais visitée
            # attend encore : la violation du mandat du 16/11.
            #
            # Les **claims de la lane** sont exclus, comme dans le pool : une
            # lane sert d'abord ses propres claims, et une issue qu'elle tient
            # en claim n'est pas une issue que le tapis « republie ». Sans
            # cette exclusion, l'organe rend rc 1 sur le fonctionnement
            # normal du tirage (le coordinateur tient des claims) et masque
            # les vraies violations.
            if avant[e.numero] > 0 and not e.mon_claim and (a_zero - servis):
                equite.append(e.numero)
            if e.numero in a_zero:
                servis.add(e.numero)
            e.visites += 1
    return {"tours": tours, "equite": sorted(set(equite)),
            "jamais_visitees": len(a_zero), "servies": len(servis),
            "restantes": sorted(a_zero - servis)}


def bilan(etats_: list[Etat], lecture: gh_bulk.Lecture, maintenant: datetime) -> dict:
    """Le bilan par role, l'invariant et les urgences.

    Par role : nombre d'issues, sans visite du tour, visitees non avancees, et
    les numeros bornes (anciennete de creation). `hors_marathon`,
    `sans_visite` et `visitees_non_avancees` suivent la mesure du 20/11 (443
    issues et 87 a zero visite hors marathons, dont 59 d'urne et 12 de revue) :
    tous les marathons sont hors agregats. `urgences` : issues d'urne ou de
    revue a zero visite, creees il y a plus de FENETRE_J jours -- c'est la
    sortie 1 du cycle.
    """
    par_role = {r: {"issues": 0, "sans_visite": 0, "visitees_non_avancees": 0,
                    "numeros_sans_visite": [], "numeros_non_avancees": []}
                for r in ROLES}
    groupes = {r: {"zero": [], "non_avancees": []} for r in ROLES}
    jamais, urgences, autres, revues = [], [], [], []
    redecider: list[Etat] = []
    hors_n = hors_zero = hors_non = 0
    limite_age = maintenant - timedelta(days=FENETRE_J)
    for e in etats_:
        r = role(e)
        par_role[r]["issues"] += 1
        if r == "autre":
            autres.append(e)
        if r == "revue":
            revues.append(e)
        non_avancee = e.visites > 0 and avancee(e, lecture, maintenant) is None
        if e.visites == 0:
            par_role[r]["sans_visite"] += 1
            groupes[r]["zero"].append(e)
            cree = _dt(e.cree_le)
            if r in _URGENCE and cree is not None and cree < limite_age:
                urgences.append(e)
            # Une lecture groupee ne voit que les 12 derniers commentaires :
            # l'ecart peut donc changer au service, sur le fil complet (le
            # tirage re-decide, `tapis_reverif`). Ces issues sont comptees
            # « worker » ici, mais le tirage peut les ecarter ensuite.
            if r == "worker" and any("fil partiel" in n for n in e.notes):
                redecider.append(e)
        if non_avancee:
            par_role[r]["visitees_non_avancees"] += 1
            groupes[r]["non_avancees"].append(e)
        if e.visites_total == 0:
            jamais.append(e)
        if not tapis_equilibre.est_marathon(e):
            # Perimetre explicite de la mesure du 20/11 : tous les marathons
            # sont harnais, et le compte ne depend pas du role.
            hors_n += 1
            hors_zero += e.visites == 0
            hors_non += non_avancee
    for r in ROLES:
        par_role[r]["numeros_sans_visite"] = _bornes(groupes[r]["zero"])
        par_role[r]["numeros_non_avancees"] = _bornes(groupes[r]["non_avancees"])
    revue_prs = []
    for e in sorted(revues, key=_cle_creation)[:LIMITE_LISTE]:
        pr = pr_de_revue(e)
        if pr is not None:
            revue_prs.append({"numero": e.numero, "pr": pr})
    return {
        "maintenant": _iso(maintenant),
        "issues": len(etats_),
        "hors_marathon": hors_n,
        "sans_visite": hors_zero,
        "visitees_non_avancees": hors_non,
        "roles": par_role,
        "invariant": invariant(etats_, maintenant),
        "jamais_visitees": _bornes(jamais),
        "jamais_visitees_nombre": len(jamais),
        "urgences": {"nombre": len(urgences), "numeros": _bornes(urgences)},
        "redecider_au_service": {"nombre": len(redecider), "numeros": _bornes(redecider)},
        "revue_prs": revue_prs,
        "autres": [{"numero": e.numero, "motif": e.motif}
                   for e in sorted(autres, key=_cle_creation)[:LIMITE_LISTE]],
    }


def ligne_dashboard(r: dict, code: int) -> str:
    """Une ligne de tableau de bord, bornee a 200 caracteres.

    La ligne est assemblee par morceaux, du plus important au moins important :
    si elle deborde, on retire le detail par role AVANT de retirer un verdict,
    et le code de sortie reste toujours visible.
    """
    inv = r["invariant"]
    zero = ", ".join(f"{nom} {r['roles'][nom]['sans_visite']}" for nom in ROLES
                     if nom != "harnais" and r["roles"][nom]["sans_visite"])
    inv_txt = (f"invariant VIOLE ({len(inv['a_zero'])} a 0 / {len(inv['a_deux'])} "
               f"a 2 ou plus)" if inv["viole"] else "invariant respecte")
    urg = f"urgences {r['urgences']['nombre']}" if r["urgences"]["nombre"] else ""
    att = r.get("atteignable") or {}
    eq = att.get("equite") or []
    eq_txt = (f"equite VIOLEE ({len(eq)})" if eq else
              (f"equite ok ({att.get('tours', '?')} tours)" if att else ""))
    tete = f"Couverture #27590 : {r['hors_marathon']} issues hors marathon ; " \
           f"{r['sans_visite']} a 0 visite ; {inv_txt}"
    queue = " ; ".join(x for x in (eq_txt, urg, f"rc {code}") if x)
    ligne = f"{tete} ({zero}) ; {queue}" if zero else f"{tete} ; {queue}"
    if len(ligne) > 200:  # le detail par role part en premier, jamais un verdict
        worker = r["roles"]["worker"]["sans_visite"]
        ligne = f"{tete} (worker {worker}) ; {queue}"
    return ligne if len(ligne) <= 200 else ligne[:197] + "..."


def _texte(r: dict, source: str) -> str:
    """Le bilan en texte court, derive du rapport."""
    inv = r["invariant"]
    lignes = [f"Couverture des visites (#27590) -- {r['maintenant']} -- source : {source}",
              (f"{r['hors_marathon']} issues hors marathon ({r['issues']} au total), "
               f"{r['sans_visite']} a 0 visite dans le tour, "
               f"{r['visitees_non_avancees']} visitees non avancees, "
               f"{r['jamais_visitees_nombre']} jamais visitees"),
              "Par role :"]
    for nom in ROLES:
        d = r["roles"][nom]
        if not d["issues"]:
            continue
        zero = ", ".join(f"#{n}" for n in d["numeros_sans_visite"]) or "aucune"
        non = ", ".join(f"#{n}" for n in d["numeros_non_avancees"]) or "aucune"
        lignes.append(f"  {nom:10s} {d['issues']:4d} issues, {d['sans_visite']:3d} "
                      f"a 0 visite, {d['visitees_non_avancees']:3d} non avancees "
                      f"-- a 0 : {zero} ; non avancees : {non}")
    lignes.append("Invariant du 16/11 (pool servable, hors claim propre et "
                  f"marathon) : {'VIOLE' if inv['viole'] else 'respecte'}")
    if inv["viole"]:
        lignes.append("  a 0 visite : "
                      + (", ".join(f"#{n}" for n in inv["a_zero"][:LIMITE_LISTE]) or "aucune"))
        lignes.append("  a 2 visites ou plus : "
                      + (", ".join(f"#{n}" for n in inv["a_deux"][:LIMITE_LISTE]) or "aucune"))
    u = r["urgences"]
    suite = f" -- {', '.join(f'#{n}' for n in u['numeros'])}" if u["nombre"] else ""
    lignes.append(f"Urgences (urne / revue sans visite, creee il y a plus de "
                  f"{FENETRE_J} j) : {u['nombre']}{suite}")
    red = r.get("redecider_au_service") or {"nombre": 0, "numeros": []}
    if red["nombre"]:
        lignes.append(f"A re-decider au service (fil tronque, l'ecart peut changer "
                      f"sur le fil complet) : {red['nombre']} -- "
                      + ", ".join(f"#{n}" for n in red["numeros"]))
    att = r.get("atteignable")
    if att:
        eq = ", ".join(f"#{n}" for n in att["equite"]) or "aucune"
        lignes.append(f"Atteignabilite du tapis : {att['tours']} tour(s) pour servir "
                      f"les {att['jamais_visitees']} issues jamais visitees "
                      f"({att['servies']} servies, {len(att['restantes'])} restantes) ; "
                      f"equite (une issue deja visitee servie pendant qu'une autre "
                      f"attend) : {eq}")
    for a in r["autres"]:
        lignes.append(f"Autre role (motif non mappe) : #{a['numero']} -- {a['motif']}")
    return "\n".join(lignes)


def _parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Couverture des visites des issues ouvertes (#27590).")
    p.add_argument("--json", action="store_true")
    p.add_argument("--dashboard-line", action="store_true",
                   help="une seule ligne (200 caracteres au plus) pour le dashboard")
    p.add_argument("--lecture", default=None, help="rejouer un dossier deja lu")
    p.add_argument("--cache-s", type=int, default=3600, help="0 desactive le cache")
    p.add_argument("--jours", type=int, default=45, help="fenetre des commits cites")
    p.add_argument("--lane", default="myia-ai-01:CoursIA", help="machine:workspace")
    return p


def main(argv: list[str] | None = None, run: gh_bulk.Run = gh_bulk.run_defaut,
         maintenant: datetime | None = None) -> int:
    args = _parser().parse_args(argv)
    depot = Path(__file__).resolve().parents[2]
    try:
        if args.lecture:
            lecture = gh_bulk.charger_depuis(args.lecture, depot, args.jours, run)
        else:
            lecture = gh_bulk.lire_tout(depot, args.cache_s, run, args.jours)
    except gh_bulk.LectureIncomplete as exc:
        # Meme secours que le tapis (#26926) : la derniere lecture COMPLETE du
        # cache (< 12 h). Un rejeu n'en a pas. Jamais un faux 0.
        secours = None if args.lecture or args.cache_s <= 0 else \
            tapis_service.lecture_de_secours(args.jours, exc)
        print(f"Lecture incomplete ({exc.lecture}, page {exc.page}) : {exc.cause}",
              file=sys.stderr)
        if secours is None:
            print("Couverture NON MESUREE -- jamais un faux 0.", file=sys.stderr)
            return 2
        lecture = secours
        print(f"Bilan sur la lecture de secours du {lecture.lu_a}.", file=sys.stderr)
    # Un rejeu se mesure a l'instant de sa lecture : memes ages, meme fenetre.
    maintenant = maintenant or (args.lecture and _dt(lecture.lu_a)) or datetime.now(UTC)
    etats_ = tapis_rapide.etats(lecture, args.lane, maintenant, args.jours)
    # Le parcage Origami, comme dans le tirage : un EPIC parque n'est pas un
    # travail de worker, son depliage est reserve au coordinateur.
    origami = parer_origami(etats_, lecture, reseau=not args.lecture)
    r = bilan(etats_, lecture, maintenant)
    r["atteignable"] = atteignable(etats_, args.lane, maintenant)
    r["origami"] = {"measured": origami.get("measured"), "parked": origami.get("parked"),
                    "reason": origami.get("reason")}
    r["lecture"] = {"lu_a": lecture.lu_a, "issues": len(lecture.issues),
                    "prs": len(lecture.prs), "depuis_cache": lecture.depuis_cache,
                    "fetch_note": lecture.fetch_note}
    # L'equite du tapis (une issue deja visitée servie pendant qu'une issue
    # jamais visitée attend) est un ROUGE de code : c'est la garantie que le
    # tirage ne repete pas les issues deja servies pendant qu'une autre attend.
    code = 1 if (r["invariant"]["viole"] or r["urgences"]["nombre"]
                 or r.get("atteignable", {}).get("equite")) else 0
    if args.json:
        out = json.dumps(r, ensure_ascii=False, indent=1)
    elif args.dashboard_line:
        out = ligne_dashboard(r, code)
    else:
        source = f"dossier {args.lecture}" if args.lecture else "cache et reseau du tapis"
        out = _texte(r, source)
    sys.stdout.buffer.write((out + "\n").encode("utf-8"))
    return code


if __name__ == "__main__":
    sys.exit(main())