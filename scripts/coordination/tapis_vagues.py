#!/usr/bin/env python3
"""Les VAGUES de la prise en charge : la file se remplit, ou le pool est vide.

Mesure du 18/11 : les 9 premiers candidats sont **tous** ecartes (les neuf
ecarts, lus sur le fil complet). Servir 0 grain alors que le pool en contient
serait un echec de methode, pas un pool vide : la qualification ouvre donc la
**vague** suivante tant que la file n'est pas pleine, dans la limite de
`max_vagues`.

Une vague est un bloc **contigu** de l'ordre classe, dans la fenetre de la
lane : la vague 0 est le bloc de la tranche, la vague 1 le bloc suivant, et
ainsi de suite. La vague s'arrete des que la file est pleine -- ou quand le
budget d'action est epuise : le mur reste un **refus** (jamais un demi-resultat).

Ce module ne fait que vaguer : il qualifie (organe `tapis_qualification`) et
publie, vague par vague, ce que chaque vague a decide.

Usage :

    python scripts/coordination/tapis_vagues.py --lane machine:workspace
    python scripts/coordination/tapis_vagues.py --lane machine:workspace --grains 8 --vagues 4
"""
from __future__ import annotations

import sys
import time
from datetime import UTC, datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import gh_bulk, gh_selection, tapis_rotation
from coordination import tapis_qualification as tq
from coordination import tapis_rapide
from coordination.tapis_marqueurs import _iso

#: Vagues maximum : au dela, la file reste courte et le rapport le dit.
VAGUES_MAX = 4


def vagues(grains_ordre: list, conteneurs: list, lane: str, maintenant: datetime,
           jours: int, prs: list[dict], run, grains: int,
           max_vagues: int = VAGUES_MAX, taille: int | None = None,
           echeance: float | None = None, debut: float | None = None,
           horloge=time.monotonic) -> tuple[list, dict, dict]:
    """Qualifie par VAGUES, jusqu'a remplir la file.

    Rend `(servis, ecartees, rapport)` : les exclusions portent leur code et
    leur motif, et le rapport dit, vague par vague, ce que la vague a decide.

    Les **citations** ne sont pas passees : la requalification decide sur le
    fil (revue du 19/11, #27242).
    """
    taille = taille or max(grains * 3, grains)
    servis: list = []
    ecartees: dict[int, dict] = {}
    detail: list[dict] = []
    for k in range(max_vagnes := max_vagues):
        bloc, fen = tapis_rotation.bloc(grains_ordre, conteneurs, grains, taille,
                                         lane, maintenant, bloc_suivant=k)
        nums = [e.numero for e in bloc]
        if not nums:
            break
        s, ec, echecs, arrete, appels, chrono = tq.qualifier(
            nums, lane, maintenant, jours, prs, run, echeance,
            debut=debut)
        for e in s:
            if e.numero not in {x.numero for x in servis}:
                servis.append(e)
        for n, v in ec.items():
            ecartees.setdefault(n, v)
        detail.append({"vague": k, "candidats": len(nums), "servis": len(s),
                       "ecartees": len(ec), "illisibles": len(echecs),
                       "appels": appels, "bloc": fen.get("bloc"),
                       "blocs": fen.get("blocs"), "chrono": chrono})
        if len(servis) >= grains or arrete:
            break
    rapport = {"vagues": detail, "vagues_max": max_vagnes,
               "vagues_jouees": len(detail)}
    return servis, ecartees, rapport


def main(argv: list[str] | None = None, run=gh_bulk.run_defaut,
         maintenant: datetime | None = None) -> int:
    """Les vagues : la file de la lane, servie par vagues jusqu'a la remplir."""
    import argparse
    import json

    p = argparse.ArgumentParser(
        description="Prise en charge par VAGUES : la file se remplit, ou le pool est vide.")
    p.add_argument("--lane", required=True, help="machine:workspace")
    p.add_argument("--grains", type=int, default=8, help="taille de la file a remplir")
    p.add_argument("--vagues", type=int, default=VAGUES_MAX, help="vagues maximum")
    p.add_argument("--jours", type=int, default=45)
    p.add_argument("--graine", default=None)
    p.add_argument("--budget-s", type=float, default=gh_selection.MUR_GLOBAL_S)
    p.add_argument("--json", action="store_true")
    args = p.parse_args(argv)
    depot = Path(__file__).resolve().parents[2]
    maintenant = maintenant or datetime.now(UTC)
    graine = args.graine or tapis_rapide.graine_defaut(args.lane, maintenant)
    debut = time.monotonic()
    from coordination import tapis_leger
    try:
        classe = tapis_leger.classer(args.lane, maintenant, args.jours, graine,
                                      depot, run, args.budget_s)
    except gh_bulk.LectureIncomplete as exc:
        print(f"Lecture incomplete ({exc.lecture}, page {exc.page}) : {exc.cause}",
              file=sys.stderr)
        return 3
    servis, ecartees, rapport_vagues = vagues(
        classe["grains"], classe["conteneurs"], args.lane, maintenant,
        args.jours, classe["prs"], run, args.grains,
        args.vagues, echeance=debut + args.budget_s, debut=debut)
    rapport = {
        "lane": args.lane, "maintenant": _iso(maintenant), "voie": "vagues",
        "pool": len(classe["metas"]), "grains": args.grains,
        "servis": len(servis), "rejets": len(ecartees),
        "secondes": round(time.monotonic() - debut, 1),
        "chrono": {"secondes": round(time.monotonic() - debut, 1),
                   "premier_servable_s": next(
                       (v["chrono"]["premier_servable_s"] for v in rapport_vagues["vagues"]
                        if v["chrono"].get("premier_servable_s") is not None), None)},
        "classement": {"organe": "scripts/coordination/tapis_leger.py",
                       "latence": "classement sur metadonnees seules (la fenetre "
                                  "qui avance est servie par vagues)"},
        "vagues": rapport_vagues,
        "grains_servis": [{"numero": e.numero, "titre": e.titre,
                           "visites": e.visites, "conteneur": e.conteneur,
                           "notes": e.notes} for e in servis],
        "ecartees": list(ecartees.values()),
    }
    out = json.dumps(rapport, ensure_ascii=False, indent=1)
    sys.stdout.buffer.write((out + "\n").encode("utf-8"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
