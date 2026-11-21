#!/usr/bin/env python3
"""Le CONTROLE ISOLE d'une citation : que deplace-t-elle, exactement ?

Mandat du coordinateur (20/11/2026, DM `coord1911-27338-isolate`) :
« si le diff de #27393 ne livre pas #27338, ajouter ou retirer cette citation
seule doit laisser exactement inchangee la date de service de #27338. Rends le
couple de dates avant/apres sur ce controle isole ; le changement global de
rang 362->350 n'y repond pas. Je garde la decision de revue. »

Cet organe ne rejoue PAS le tirage : il isole UNE citation et mesure ce qu'elle
deplace. Il rend le **couple de dates** (avec la citation, sans la citation),
la cle et son origine, les visites, le rang, et la livraison confirmee (store).

Il ne DECIDE rien : le coordinateur garde la decision de revue.
"""
from __future__ import annotations

import json
import sys
from datetime import UTC, datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import (gh_bulk, tapis_leger, tapis_rapide, tapis_releve,
                         tapis_universel)


def resume(etats_: list, numero: int) -> dict:
    """L'etat d'un grain : cle, origine, visites, date de creation."""
    for e in etats_:
        if int(e.numero) == int(numero):
            return {"numero": e.numero, "cle_service": e.cle_service,
                    "cle_origine": e.cle_origine,
                    "derniere_visite": e.derniere_visite,
                    "visites_total": e.visites_total,
                    "creation": e.cree_le}
    return {}


def rang(etats_: list, numero: int, lane: str, maintenant: datetime,
         graine: str | None) -> int | None:
    """La place du grain dans l'ordre FAIR (rotation=False, comme la voie leger)."""
    ordre = tapis_universel.rotation_universelle(
        etats_, lane, maintenant, len(etats_), graine, rotation=False)
    for i, e in enumerate(ordre):
        if int(e.numero) == int(numero):
            return i + 1
    return None


def controler(numero: int, pr: int, etats_avec: list, etats_sans: list,
              lane: str = "", maintenant: datetime | None = None,
              graine: str | None = None) -> dict:
    """Le couple de dates avant/apres, isole sur UNE citation.

    `etats_avec` est l'etat du pool ou la citation est presente ;
    `etats_sans` le meme pool, la PR citee retranchee. Rien d'autre ne change.
    """
    maintenant = maintenant or datetime.now(UTC)
    return {
        "numero": int(numero), "pr": int(pr),
        "avant": resume(etats_avec, numero),
        "apres": resume(etats_sans, numero),
        "rang_avant": rang(etats_avec, numero, lane, maintenant, graine),
        "rang_apres": rang(etats_sans, numero, lane, maintenant, graine),
        "livraison_confirmee": tapis_releve.service(numero),
        "store": tapis_releve.service_connue().get(int(numero)),
    }


def isoler(lane: str, numero: int, pr: int, depot, run=gh_bulk.run_defaut,
           grains: int = 8, graine: str | None = None,
           maintenant: datetime | None = None) -> dict:
    """Le controle sur le POOL REEL : une lecture, puis la meme lecture sans la PR.

    La PR citee est la seule entree retiree : le reste du pool, ses citations
    et ses livraisons restent identiques.
    """
    maintenant = maintenant or datetime.now(UTC)
    classe = tapis_leger.classer(lane, maintenant, 45, graine, depot, run)
    etats_avec = classe["etats"]
    prs_sans = [p for p in classe["prs"]
                if int(p.get("number") or 0) != int(pr)]
    etats_sans = tapis_universel.etats_leger(
        classe["metas"], classe["citations"], maintenant, prs_sans)
    return controler(numero, pr, etats_avec, etats_sans, lane, maintenant, graine)


def main(argv: list[str] | None = None) -> int:
    """Point d'entree : `tapis_controle.py --lane ... --issue N --pr M`."""
    import argparse

    p = argparse.ArgumentParser(
        description="Controle isole d'une citation : le couple de dates.")
    p.add_argument("--lane", required=True, help="machine:workspace")
    p.add_argument("--issue", type=int, required=True, help="issue isolee")
    p.add_argument("--pr", type=int, required=True, help="PR citee a retrancher")
    p.add_argument("--graine", default=None)
    args = p.parse_args(argv)
    depot = Path(__file__).resolve().parents[2]
    maintenant = datetime.now(UTC)
    graine = args.graine or tapis_rapide.graine_defaut(args.lane, maintenant)
    r = isoler(args.lane, args.issue, args.pr, depot, graine=graine,
               maintenant=maintenant)
    sys.stdout.buffer.write(
        (json.dumps(r, ensure_ascii=False, indent=1) + "\n").encode("utf-8"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
