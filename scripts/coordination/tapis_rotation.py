#!/usr/bin/env python3
"""La ROTATION du pool : le bloc servi, et la rotation par NUMERO.

Le classement change a chaque tour : une rotation qui suit la POSITION fait
passer des issues a travers le bloc, et le tour ne se ferme pas -- mesure du
19/11 : **380 issues sur 440** atteintes en un tour. La rotation suit donc le
**NUMERO** : l'ordre des numeros ne bouge pas, le tour se ferme.

Le bloc est CONTIGU de cet ordre, decale par lane : deux lanes ne balayent pas
le meme bloc. Une tranche de 4 h fait avancer le bloc d'un cran (delai max publie).

**Chaque numero du pool sort avec un verdict** (#27242) : le bloc publie les
numeros qu'il **visite** et ceux qu'il ne visite pas (`non_visites`). L'ANCRE
(dernier numero qualifie) choisit QUOI servir, la **PRIORITE** l'ordre.

La composition du bloc (tranche primaire + reprise des illisibles) est dans
`coordination.tapis_composition` : deux choses distinctes, et le melange des
deux figeait la rotation (19/11). La place du bloc dans le pool est dans
`coordination.tapis_position`.
"""
from __future__ import annotations

from datetime import datetime

from coordination import tapis_ancre, tapis_composition, tapis_position
from coordination.tapis_rapide import PART_CONTENEURS

#: La fenetre avance d'un bloc par tranche de 4 h.
TRANCHES_JOUR = tapis_position.TRANCHES_JOUR
HEURES_TRANCHE = tapis_position.HEURES_TRANCHE


def bloc(grains: list, conteneurs: list, n_grains: int, taille: int, lane: str,
         maintenant: datetime, bloc_suivant: int = 0,
         ancres: dict | None = None) -> tuple[list, dict]:
    """Le bloc servi : la rotation par numero, dans la fenetre de la lane.

    Les GRAINS et les CONTENEURS ont chacun leur tranche et leur bloc : un
    conteneur ne passe jamais devant un grain (#26926).

    `bloc_suivant` decale le bloc de N blocs : c'est la VAGUE suivante de la
    prise en charge. `ancres` porte l'ancre PERSISTENTE (`tapis_ancre`) : le
    bloc commence au premier numero superieur a l'ancre de chaque classe.
    """
    quota = max(1, int(n_grains * PART_CONTENEURS)) if conteneurs else 0
    part = max(taille - quota, 1)
    n_g, n_c = len(grains), len(conteneurs)
    compteur = tapis_position.compteur(maintenant) + bloc_suivant
    ancres = ancres or {}
    ancre_g = tapis_ancre.ancre_de(ancres, "grains")
    ancre_c = tapis_ancre.ancre_de(ancres, "conteneurs")
    b_g, b_c, primaires, reprises = tapis_composition.compose(
        grains, conteneurs, part, quota, ancre_g, ancre_c,
        tapis_ancre.inconnus_de(ancres, "grains"),
        tapis_ancre.inconnus_de(ancres, "conteneurs"),
        tapis_position.decalage(lane, "grains", n_g) + compteur * part,
        tapis_position.decalage(lane, "conteneurs", n_c) + compteur * quota,
        bloc_suivant)
    pool = {g.numero for g in grains} | {g.numero for g in conteneurs}
    visites = {g.numero for g in b_g} | {g.numero for g in b_c}
    blocs = max((n_g + part - 1) // part if n_g else 1,
                (n_c + quota - 1) // quota if n_c else 1)
    return b_g + b_c, {
        "taille": taille, "grains": len(b_g), "conteneurs": len(b_c),
        "bloc": (tapis_position.decalage(lane, "grains", n_g) // part) + 1
        if n_g else 0,
        "blocs": blocs, "pool": n_g, "tranche": compteur,
        "ordre": "numero", "delai_max_h": HEURES_TRANCHE * blocs,
        "ancres": {"grains": ancre_g, "conteneurs": ancre_c},
        "ancres_proposees": {
            "grains": tapis_composition.dernier(primaires["grains"]),
            "conteneurs": tapis_composition.dernier(primaires["conteneurs"])},
        "primaires": primaires, "reprises": reprises,
        "visites": sorted(visites), "non_visites": sorted(pool - visites)}
