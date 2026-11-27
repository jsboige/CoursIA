#!/usr/bin/env python3
"""La VOIE LEGERE du tirage : le service du classement sur metadonnees.

Extraits de `tapis_rapide.py` pour tenir le plafond de lignes de ce module.

Le classement ne lit que les metadonnees du pool ; ce qui exige le corps et
le fil se decide sur le grain servi, sur son **fil complet** (organe REST
`gh_snapshot`), jamais sur la fenetre des 12 derniers commentaires.
"""
import json
import sys
from datetime import UTC, datetime

from coordination import gh_bulk


def servir(args, depot, run, maintenant, graine: str, fraicheur: dict | None,
           echeance: float | None = None) -> int:
    """La voie LEGERE : classement sur metadonnees, qualification sur fil complet.

    Sortie 3 : la lecture de selection est incomplete -- rien n'est servi,
    jamais une liste a moitie.
    """
    from coordination import tapis_leger
    try:
        r, code = tapis_leger.tirage(args.lane, args.grains, maintenant,
                                     args.jours, graine, depot, run,
                                     echeance=echeance)
    except gh_bulk.LectureIncomplete as exc:
        print(f"Lecture incomplete ({exc.lecture}, page {exc.page}) : {exc.cause}",
              file=sys.stderr)
        return 3
    r["fraicheur"] = fraicheur
    out = json.dumps(r, ensure_ascii=False, indent=1) if args.json else \
        tapis_leger.texte(r)
    sys.stdout.buffer.write((out + "\n").encode("utf-8"))
    return code
