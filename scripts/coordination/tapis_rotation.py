#!/usr/bin/env python3
"""La ROTATION du pool : le bloc servi, et la rotation par NUMERO.

La rotation suit le **NUMERO** : une rotation qui suit la POSITION fait passer
des issues a travers le bloc et le tour ne se ferme pas (mesure du 19/11 :
**380 issues sur 440** atteintes en un tour).

Le bloc est CONTIGU de cet ordre, decale par lane. Une tranche de 4 h fait
avancer le bloc d'un cran.

**Chaque numero du pool sort avec un verdict** (#27242) : le bloc publie les
numeros qu'il **visite** et ceux qu'il ne visite pas (`non_visites`). L'ANCRE
(dernier numero qualifie) choisit QUOI servir ; la TETE est le numero suivant
l'ancre, la **PRIORITE** l'ordre du reste. La composition du bloc est dans
`coordination.tapis_composition`, la place du bloc dans `tapis_position`.
"""
from __future__ import annotations

from datetime import datetime

from coordination import (tapis_age, tapis_ancre, tapis_blocs, tapis_composition, tapis_entrelace, tapis_position)

#: La fenetre avance d'un bloc par tranche de 4 h.
TRANCHES_JOUR = tapis_position.TRANCHES_JOUR
HEURES_TRANCHE = tapis_position.HEURES_TRANCHE


def bloc(grains: list, conteneurs: list, n_grains: int, taille: int, lane: str,
         maintenant: datetime, bloc_suivant: int = 0,
         ancres: dict | None = None, ages_g: list | None = None,
         exclus_g: set | None = None) -> tuple[list, dict]:
    """Le bloc servi : la rotation par numero, dans la fenetre de la lane.

    Les GRAINS et les CONTENEURS ont chacun leur tranche et leur bloc ; les
    classes se partagent le lot, un creneau chacune (19/11).

    `bloc_suivant` decale le bloc de N blocs : c'est la VAGUE suivante. `ancres`
    porte l'ancre PERSISTENTE : le bloc commence au premier numero superieur a
    l'ancre de chaque classe.

    `ages_g` / `exclus_g` : la SELECTION par AGE des grains (mandat du 22/11)
    -- l'ordre d'age, et les numeros deja servis.
    """
    quota, part = tapis_blocs.quotas(n_grains, taille, len(conteneurs))
    n_g, n_c = len(grains), len(conteneurs)
    compteur = tapis_position.compteur(maintenant) + bloc_suivant
    ancres = ancres or {}
    ancre_g = tapis_ancre.ancre_de(ancres, "grains")
    ancre_c = tapis_ancre.ancre_de(ancres, "conteneurs")
    b_g, b_c, primaires, reprises = tapis_composition.compose(
        grains, conteneurs, part, quota, ancre_g, ancre_c,
        tapis_ancre.inconnus_de(ancres, "grains"), tapis_ancre.inconnus_de(ancres, "conteneurs"),
        tapis_position.decalage(lane, "grains", n_g) + compteur * part,
        tapis_position.decalage(lane, "conteneurs", n_c) + compteur * quota,
        bloc_suivant,
        # La PHASE alterne le sens de l'entrelacement (un tour sur deux).
        reprise_d_abord=tapis_ancre.phase_de(ancres, "grains") % 2 == 1,
        ages_g=ages_g, exclus_g=exclus_g)

    pool = {g.numero for g in grains} | {g.numero for g in conteneurs}
    visites = {g.numero for g in b_g} | {g.numero for g in b_c}
    blocs = tapis_blocs.nombre_blocs(n_g, n_c, part, quota)
    # Le lot PUBLIC entrelace les CLASSES : chacune a un creneau de lecture.
    return tapis_entrelace.intercale(
        b_g, b_c, tapis_ancre.phase_de(ancres, "grains") % 2 == 1), {
        "taille": taille, "grains": len(b_g), "conteneurs": len(b_c),
        "bloc": (tapis_position.decalage(lane, "grains", n_g) // part) + 1 if n_g else 0,
        "blocs": blocs, "pool": n_g, "tranche": compteur,
        "ordre": "age" if ages_g is not None else "numero",
        "age": {"exclus": len(exclus_g or ())} if ages_g is not None else {},
        "delai_max_h": HEURES_TRANCHE * blocs,
        "ancres": {"grains": ancre_g, "conteneurs": ancre_c},
        "ancres_proposees": {"grains": tapis_composition.dernier(primaires["grains"]),
                             "conteneurs": tapis_composition.dernier(primaires["conteneurs"])},
        "primaires": primaires, "reprises": reprises,
        "visites": sorted(visites), "non_visites": sorted(pool - visites)}
