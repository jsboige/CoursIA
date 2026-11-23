#!/usr/bin/env python3
"""La lecture d'un LOT de candidats : un VERDICT par numero demande.

Le lot se lit d'un coup (une requete GraphQL pour 50 issues). Ce que la
lecture rend est incomplet par nature : un numero peut etre illisible, ou
absent de la reponse (l'issue n'existe pas). **Aucun numero demande ne
disparait** : chacun sort avec son verdict -- lu, illisible, ou absent.

Ce module est extrait de `tapis_qualification.py` (revue du 19/11) : le
plafond de lignes se paie en **extrait**, pas en relevant le plafond.
"""
from __future__ import annotations

import sys
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import gh_bulk, gh_selection
from coordination.tapis_marqueurs import _iso

#: Le verdict d'un numero absent de la reponse (l'issue n'existe pas, ou
#: n'est pas visible). C'est un **refus**, pas une decision de contenu.
ABSENT = "ABSENT"


def lec(issues: list[dict], maintenant: datetime,
        appels: int = 0) -> gh_bulk.Lecture:
    """La lecture des seuls candidats qualifies : c'est elle qui est rejouee
    par `tapis_rapide.etats` (les neuf regles d'ecart).

    **Ni PRs ni citations** n'y figurent : la requalification decide sur le
    FIL (un grain prouve une prise en charge), et une citation ou une PR
    ouverte ne prouve aucune livraison (revue du 19/11, #27242). Elles sont
    rendues a la lane en NOTES (`coordination.tapis_preuves`).
    """
    return gh_bulk.Lecture(issues=issues, prs=[], citations={},
                           lu_a=_iso(maintenant), secondes=0.0, appels=appels)


def fenetre(candidats: list[int], run, issues: dict[int, dict],
            echecs: list[int], ecartees: dict[int, dict]) -> int:
    """Lit le corps et la fenetre des candidats (un lot GraphQL), et les ajoute
    au contexte. Rend le nombre de lots lus.

    **Un verdict par numero demande** :

    - lu -> `issues` ;
    - lot illisible -> `echecs` (tous les numeros du lot) ;
    - issue absente de la reponse -> `ecartees`, code `ABSENT`.

    Un numero qui sortait sans verdict etait un trou du classement : il
    disparaissait du tirage sans que personne sache pourquoi (revue du 19/11).
    """
    if not candidats:
        return 0
    try:
        lus = gh_selection.qualifier(run, gh_bulk.DEPOT_GH, candidats)
    except gh_bulk.LectureIncomplete:
        echecs.extend(candidats)
        return 0
    for n, v in lus.items():
        if v is None:
            ecartees.setdefault(n, {"numero": n, "code": ABSENT,
                                    "motif": "absente de la reponse de la lecture",
                                    "fenetre_suffit": False})
        else:
            issues[n] = v
    return 1
