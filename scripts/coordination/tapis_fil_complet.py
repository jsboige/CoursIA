#!/usr/bin/env python3
"""Le FIL COMPLET des candidats retenus : lever le doute de la fenetre.

La lecture groupee ne voit que les 12 derniers commentaires : le marqueur qui
ecarte un grain peut etre plus ancien que la fenetre (constat de #27179, qui
a produit l'organe `tapis_reverif`). Le fil complet est donc relu -- par
l'organe REST `gh_snapshot` -- pour les **seuls** candidats que la fenetre
RETIENT, et la decision est rejouee (`tapis_rapide._decider`, comme
`tapis_reverif`).

C'est la separation demandee : la rotation universelle est legere (metadonnees
seules), la lecture complete n'intervient qu'**avant l'action**, sur le grain
que la lane engage a prendre.

Mesure du 2026-11-18 (pool de 440 issues) : relire le fil complet de TOUS les
candidats coute 1 appel REST par candidat (48 appels, 59 s) ; relire d'abord
la fenetre en un lot GraphQL (1 appel pour 50 candidats) et ne relire le fil
complet que des candidats **retenus** coute 1 appel REST par candidat retenu.

**fail-CLOSED.** Un candidat dont la decision n'a pas pu etre prise n'est PAS
servi : le fil illisible (FIL_ILLISIBLE), le mur de lectures atteint
(MUR_EPUISE) et l'echeance depassee (ECHEANCE) REFUSENT la prise en charge,
chacun avec son code et son motif. Le temps d'action engage un grain dont le
fil a ete lu et la decision prise -- le tapis propose, il ne fait pas
autorite, et un grain non qualifie ne s'engage pas.
"""
from __future__ import annotations

import time
from datetime import datetime
from pathlib import Path

import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import gh_bulk, tapis_diff, tapis_fenetre, tapis_rapide, tapis_reverif

#: Borne des lectures REST du fil complet (les candidats retenus).
APPELS_MAX = 16

#: Les refus de LECTURE : le grain n'est pas servi, il est refuse.
#: distincts des ecarts de REGLE (les neuf), qui sont une decision.
CODES_REFUS = ("FIL_ILLISIBLE", "MUR_EPUISE", "ECHEANCE")


def confirmer(retenus: list, lecture, lane: str, maintenant: datetime, jours: int,
              echeance: float | None = None, horloge=time.monotonic,
              appels_max: int = APPELS_MAX, preuve=None) -> tuple[list, list, list[int], int]:
    """Re-decide sur le fil complet les candidats RETENUS par la fenetre.

    Rend `(confirmes, rejetes, echecs, appels)`. Un candidat dont la fenetre
    EST le fil complet (moins de 12 commentaires) est confirme sans appel :
    il n'y a rien a lever.

    **fail-CLOSED** : un candidat dont le fil n'a pas pu etre lu -- illisible,
    hors budget de lectures, ou hors echeance -- n'est PAS confirme : il est
    refuse, avec son code et son motif, et le refus est affiche. Un grain
    dont la decision n'a pas etre prise ne s'engage pas.
    """
    ouvertes, parents, _, ctx = tapis_rapide._contexte(lecture, lane,
                                                       maintenant, jours)
    confirmes, rejetes, echecs, appels = [], [], [], 0
    for e in retenus:
        it = ouvertes.get(e.numero) or {}
        # La fenetre EST-elle le fil complet ? C'est l'organe canonique qui
        # repond (`tapis_fenetre.suffit`) : un `comments_total` INCONNU ne
        # vaut pas 0 (19/11, DM du coordinateur) -- il vaut « la fenetre
        # n'est pas prouvee complete », donc le fil complet se lit.
        if tapis_fenetre.suffit(it):
            confirmes.append(e)
            continue
        if appels >= appels_max:
            rejetes.append({"numero": e.numero, "code": "MUR_EPUISE",
                            "motif": (f"mur de lectures atteint ({appels_max} "
                                      "fil(s) complet(s) lus) : le fil de ce "
                                      "grain n'a pas ete lu")})
            continue
        if echeance is not None and horloge() > echeance:
            rejetes.append({"numero": e.numero, "code": "ECHEANCE",
                            "motif": "echeance de la qualification depassee : "
                                     "le fil de ce grain n'a pas ete lu"})
            continue
        try:
            fil = tapis_fenetre.fil_complet(e.numero)
        except Exception:  # noqa: BLE001 - un fil illisible REFUSE le grain
            echecs.append(e.numero)
            rejetes.append({"numero": e.numero, "code": "FIL_ILLISIBLE",
                            "motif": "fil complet illisible : la decision n'a "
                                     "pas pu etre prise"})
            continue
        appels += 1
        code = tapis_reverif._redecrire(e, ouvertes, parents, ctx, fil,
                                         tapis_rapide)
        if preuve is not None:
            code = tapis_diff.decider(e, fil, code, preuve)
        if code is None:
            confirmes.append(e)
        else:
            rejetes.append({"numero": e.numero, "code": code, "motif": e.motif})
    return confirmes, rejetes, echecs, appels
