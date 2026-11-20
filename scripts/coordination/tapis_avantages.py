#!/usr/bin/env python3
"""Les deux priorites LEGERES du tapis (mandat user du 2026-11-18).

> « je veux que toutes les issues soient servies regulierement par le tapis,
> avec une legere priorite pour les vieilles issues, et une autre legere
> priorite pour les issues de consolidation »

Deux contributions PETITES et DISTINCTES :

- **l'age** : un quart de bande, `BANDS_AGE_J` -- 0,1 visite par tranche de
  30 jours franchie, **plafonne a 0,5 visite** (au-dela de 180 jours) ;
- **la consolidation** : **0,4 visite, a tout age** (label `consolidation`, ou
  famille dont la racine l'est).

Les deux sont comptees en **dixiemes de visite** : le niveau reste un multiple
de 0,1, donc les issues se regroupent par niveau (c'est ce qui permet a la
tete de niveau de tourner d'une lane a l'autre) et le bonus n'est jamais une
visite entiere.

La division par 3 des consolidations anciennes disparait : elle etait plus
forte qu'une priorite legere. La borne `BONUS_TOTAL_MAX` (0,9 visite)
preserve l'equite du mandat du 16/11 : une issue a 0 visite passe devant une
issue a 1 visite, et le « tour » (une visite chacun) reste la regle.

Fonctions pures, sans reseau.
"""
from __future__ import annotations

from datetime import datetime

from coordination.tapis_marqueurs import _dt

# (age minimal en jours, bonus en dixiemes de visite) ; la premiere tranche
# franchie gagne. 180 j et plus : le bonus d'age est plein (0,5 visite).
BANDS_AGE_J = ((180, 5), (120, 4), (60, 3), (30, 2), (10, 1))
BONUS_CONSOLIDATION = 4  # dixiemes de visite, a tout age
BONUS_TOTAL_MAX = 9  # dixiemes : 0 visite reste devant 1 visite


def age_jours(cree_le: str | None, maintenant: datetime) -> float:
    """L'age de l'issue en JOURS PLEINS (0 si la date est illisible).

    Le jour plein, et non l'heure : une bande d'age franchie a cheval sur une
    tranche de quatre heures changerait la liste d'une lane a l'autre. Les
    tranches de quatre heures ne franchissent pas minuit, donc la liste reste
    stable dans sa tranche."""
    cree = _dt(cree_le)
    if cree is None:
        return 0.0
    return float(max(0, (maintenant.date() - cree.date()).days))


def est_consolidation(consolidation: bool, famille: int, racines: set[int]) -> bool:
    """Une issue de consolidation : label, ou famille dont la racine l'est."""
    return bool(consolidation) or famille in racines


def bonus_dixiemes(age_j: float, consolidation: bool) -> tuple[int, list[str]]:
    """Le bonus total en dixiemes de visite, et les motifs que le rapport nomme."""
    band = next((dix for seuil, dix in BANDS_AGE_J if age_j >= seuil), 0)
    b_conso = BONUS_CONSOLIDATION if consolidation else 0
    motifs = []
    if band:
        motifs.append(f"priorite d age : -{band / 10:.1f} visite")
    if b_conso:
        motifs.append(f"priorite de consolidation : -{b_conso / 10:.1f} visite")
    return min(BONUS_TOTAL_MAX, band + b_conso), motifs
