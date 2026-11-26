#!/usr/bin/env python3
"""Les deux priorites LEGERES du tapis (mandat user du 2026-11-18).

> « je veux que toutes les issues soient servies regulierement par le tapis,
> avec une legere priorite pour les vieilles issues, et une autre legere
> priorite pour les issues de consolidation »

Deux contributions PETITES et DISTINCTES :

- **l'age** : un quart de bande, `BANDS_AGE_J` -- 0,1 visite par tranche de
  30 jours franchie, **plafonne a 0,5 visite** (au-dela de 180 jours) ;
- **la consolidation** : **0,6 visite, a tout age** (label `consolidation`, ou
  famille dont la racine l'est).

**La consolidation passe DEVANT l'anciennete** (invariant I7 du contrat du
picker, #28114, 22/11) : les bonus ne s'additionnent plus, ils se composent
par priorite -- la consolidation prend 0,6 visite, l'age ne garde que
`BONUS_AGE_MAX_CONSO` (0,3) sur une consolidation. Avant, l'age plein
l'emportait (mesure : `scripts/tests/test_tapis_equilibre.py`).

Les deux sont comptees en **dixiemes de visite** : le niveau reste un multiple
de 0,1, donc les issues se regroupent par niveau (c'est ce qui permet a la
tete de niveau de tourner d'une lane a l'autre) et le bonus n'est jamais une
visite entiere. La division par 3 des consolidations anciennes disparait
(elle etait plus forte qu'une priorite legere) ; la borne `BONUS_TOTAL_MAX`
(0,9 visite) preserve l'equite du 16/11 : 0 visite passe devant 1 visite.

Fonctions pures, sans reseau.
"""
from __future__ import annotations

from datetime import datetime

from coordination.tapis_marqueurs import _dt

# (age minimal en jours, bonus en dixiemes de visite) ; la premiere tranche
# franchie gagne. 180 j et plus : le bonus d'age est plein (0,5 visite).
BANDS_AGE_J = ((180, 5), (120, 4), (60, 3), (30, 2), (10, 1))
BONUS_CONSOLIDATION = 6  # dixiemes de visite, a tout age : pose EN PREMIER
BONUS_AGE_MAX_CONSO = 3  # dixiemes : part de l'age qui reste sur une consolidation
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
    """Le bonus total en dixiemes de visite, et les motifs que le rapport nomme.

    **La consolidation passe devant l'anciennete** (I7) : son bonus est pose
    EN PREMIER (0,6 visite), l'age ne garde que `BONUS_AGE_MAX_CONSO` (0,3
    visite) sur une consolidation. Les motifs somment au bonus effectif."""
    band = next((dix for seuil, dix in BANDS_AGE_J if age_j >= seuil), 0)
    if not consolidation:
        motifs = []
        if band:
            motifs.append(f"priorite d age : -{band / 10:.1f} visite")
        return band, motifs
    age = min(band, BONUS_AGE_MAX_CONSO)
    motifs = []
    if band:
        plafonne = " (plafonnee : la consolidation passe devant)" if age != band else ""
        motifs.append(f"priorite d age : -{age / 10:.1f} visite{plafonne}")
    motifs.append(f"priorite de consolidation : -{BONUS_CONSOLIDATION / 10:.1f} visite")
    return min(BONUS_TOTAL_MAX, BONUS_CONSOLIDATION + age), motifs
