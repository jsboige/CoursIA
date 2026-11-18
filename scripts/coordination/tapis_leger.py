#!/usr/bin/env python3
"""La voie LEGERE du tirage : classement sur metadonnees, qualification sur fil complet.

Ce module est la **bascule** du tirage par defaut (#27225, suite de #27223).

Le classement ne lit plus le corps ni les commentaires du pool : il classe
toutes les issues ouvertes sur leurs metadonnees seules (`coordination.gh_selection`)
et tourne la tete de niveau (`coordination.tapis_universel`). Ce qui exige le
corps et le fil -- gel, livre, claim vivant, marquage de visite -- se decide a la
**prise en charge**, sur le grain servi, et sur le **fil complet**.

Le fil complet est la condition de cette bascule : la lecture groupee ne voit
que les 12 derniers commentaires (`gh_bulk.QUERY`, `comments(last:12)`), et le
marqueur qui ecarte un grain peut etre plus vieux que la fenetre -- constat de
#27179, qui a produit l'organe `tapis_reverif`. La qualification lit donc tous
les commentaires par l'organe deja livre (`gh_snapshot`, pagination REST), et
**jamais** la fenetre.

Les regles de decision ne sont pas dupliquees : la qualification rejoue
`tapis_rapide.etats`, donc les neuf regles d'ecart et le compte des visites
sont exactement les memes qu'en voie lourde.

La qualification elle-meme (corps, fil, vagues) vit dans
`coordination.tapis_qualification.py` : c'est une reponsabilite distincte, et
elle a son propre plafond de lignes.
"""
from __future__ import annotations

import time
from datetime import UTC, datetime

from coordination import gh_bulk, gh_selection, tapis_equilibre
from coordination import tapis_origami, tapis_rapide, tapis_service, tapis_universel
from coordination import tapis_qualification as qual
from coordination.tapis_marqueurs import _age, _iso, lane_de_pr

#: Candidats qualifies au minimum pour un tirage (appels REST, un par candidat).
#: Le plafond REEL suit le nombre de grains demandes : la ceinture du
#: coordinateur (`--grains 60`) doit rendre 60 grains, pas 12.
QUAL_MAX = 12
#: Nombre maximum de VAGUES de qualification. Une vague = une lecture REST par
#: candidat ; au-dela, le tirage rend ce qu'il a -- le pool ne se vide pas.
MAX_VAGUES = 4
#: Le classement propose ce multiple de grains : la qualification en ecarte
#: quelques-uns (claim, gel, contenu livre), et la liste doit rester pleine.
CANDIDATS_MULT = 3


def _rapport(lane: str, graine: str, maintenant: datetime, metas: list[dict],
             duree: float, lec, qualifies: list, servables: list, ecartees: dict,
             numbers: list[int], issues: list[dict], echecs: list[int],
             prs: list[dict], origami: dict) -> dict:
    """Le rapport du tirage leger, meme forme que la voie lourde."""
    conso = tapis_equilibre.familles_consolidation(qualifies)
    prs_par = tapis_rapide._prs_par_issue(prs)
    vos = sorted((pr for pr in prs if lane_de_pr(pr) == lane),
                 key=lambda pr: pr.get("created_at") or "")
    return {
        "lane": lane, "graine": graine, "maintenant": _iso(maintenant),
        "voie": "leger",
        "lecture": {"issues": len(metas), "servables": len(servables),
                    "familles": len({e.famille for e in servables}),
                    "lu_a": lec.lu_a, "appels": lec.appels, "secondes": lec.secondes,
                    "depuis_cache": False, "fetch_note": None,
                    "origin_main_le": lec.origin_main_le,
                    "origin_main_age_h": _age(maintenant, lec.origin_main_le, 3600),
                    "selection_s": duree},
        "vos_prs": [{"numero": pr["number"], "titre": pr.get("title") or "",
                     "age_j": _age(maintenant, pr.get("created_at"), 86400)} for pr in vos],
        "grains": [tapis_service.grain_servi(
            i, e, lane, tapis_equilibre.raisons(e, conso, maintenant), prs_par)
            for i, e in enumerate(servables, 1)],
        "ecartees": ecartees,
        "qualification": {"proposes": len(numbers),
                          "candidats": len(issues) + len(echecs),
                          "qualifies": len(issues),
                          "rejets": len(qualifies) - len(servables),
                          "fils_illisibles": echecs, "fil": "complet"},
        "origami_parking": origami,
    }


def tirage(lane: str, grains: int, maintenant: datetime, jours: int, graine: str,
           depot, run=gh_bulk.run_defaut, budget_s: float = gh_selection.MUR_GLOBAL_S,
           qual_max: int | None = None) -> tuple[dict, int]:
    """Le tirage leger complet : le rapport et le code de sortie.

    Sortie 3 : la lecture de selection est incomplete (rien n'est servi) --
    jamais une liste a moitie. Une lecture incomplete du POOL n'est pas
    equivalente : la selection paginee est complete ou elle echoue.
    """
    debut = time.monotonic()
    # Le plafond de qualification suit le nombre de grains demandes : la
    # ceinture du coordinateur (`--grains 60`) doit rendre 60 grains.
    qual_max = max(QUAL_MAX, grains) if qual_max is None else qual_max
    metas, duree = gh_selection.lire_metadonnees_issues(run, budget_s=budget_s)
    citations = gh_bulk.lire_citations_mergees(depot, jours, run)
    prs = gh_bulk.lire_prs_ouvertes(run)
    etats_ = tapis_universel.etats_leger(metas, citations, maintenant)
    # Le classement propose assez de candidats pour remplir la file malgre les
    # ecarts : la qualification ecarte, la vague suivante prend le relais.
    nb_candidats = max(grains * CANDIDATS_MULT, qual_max * MAX_VAGUES)
    candidats = tapis_universel.rotation_universelle(
        etats_, lane, maintenant, nb_candidats, graine)
    numbers = [e.numero for e in candidats]
    qualifies, issues, echecs, lec, servables = qual.qualifier_par_vagues(
        numbers, qual_max, grains, lane, maintenant, jours, prs, citations, run,
        MAX_VAGUES)
    lec.secondes = round(time.monotonic() - debut, 1)
    # Parcage Origami : mesure sur les grains QUALIFIES (leur corps est la).
    # Le pool n'est pas lu en entier -- un EPIC non deplie qui n'a pas ete
    # qualifie ne pouvait pas etre servi de toute facon.
    try:
        parcs, origami = tapis_origami.mesurer(lec, reseau=True)
    except Exception:  # noqa: BLE001 - un garde ne doit pas casser le tirage
        parcs, origami = {}, {"measured": False, "reason": "mesure Origami en echec"}
    tapis_rapide._parquer(qualifies, parcs)
    # L'ordre propose est celui de la rotation ; la qualification le conserve.
    rang = {e.numero: i for i, e in enumerate(candidats)}
    qualifies.sort(key=lambda e: rang.get(e.numero, 10**6))
    servables = [e for e in qualifies if e.ecart is None][:grains]
    ecartees: dict[str, list[dict]] = {}
    for e in qualifies:
        if e.ecart:
            ecartees.setdefault(e.ecart, []).append({"numero": e.numero, "motif": e.motif})
    rapport = _rapport(lane, graine, maintenant, metas, duree, lec, qualifies,
                       servables, ecartees, numbers, issues, echecs, prs, origami)
    return rapport, 0


def main(argv: list[str] | None = None, run=gh_bulk.run_defaut,
         maintenant: datetime | None = None) -> int:
    """Point d'entree du tirage leger (`tapis_leger.py --lane ...`)."""
    import argparse
    import json
    import sys
    from pathlib import Path

    p = argparse.ArgumentParser(
        description="Tapis leger : classement sur metadonnees, qualification sur fil complet.")
    p.add_argument("--lane", required=True, help="machine:workspace")
    p.add_argument("--grains", type=int, default=8)
    p.add_argument("--json", action="store_true")
    p.add_argument("--jours", type=int, default=45)
    p.add_argument("--graine", default=None)
    p.add_argument("--budget-s", type=float, default=gh_selection.MUR_GLOBAL_S)
    args = p.parse_args(argv)
    depot = Path(__file__).resolve().parents[2]
    maintenant = maintenant or datetime.now(UTC)
    graine = args.graine or tapis_rapide.graine_defaut(args.lane, maintenant)
    try:
        r, code = tirage(args.lane, args.grains, maintenant, args.jours, graine,
                         depot, run, args.budget_s)
    except gh_bulk.LectureIncomplete as exc:
        print(f"Lecture incomplete ({exc.lecture}, page {exc.page}) : {exc.cause}",
              file=sys.stderr)
        return 3
    out = json.dumps(r, ensure_ascii=False, indent=1) if args.json else \
        "\n".join(f"#{g['numero']} {g['titre'][:70]}" for g in r["grains"])
    sys.stdout.buffer.write((out + "\n").encode("utf-8"))
    return code


if __name__ == "__main__":
    import sys

    sys.exit(main())
