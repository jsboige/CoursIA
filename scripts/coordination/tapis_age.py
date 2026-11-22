#!/usr/bin/env python3
"""L'ORDRE D'AGE du tapis : les issues anciennes d'abord.

Mandat du mainteneur (22/11) : « le tapis devrait pouvoir piocher les issues
anciennes prioritairement sur les plus recentes, meme si celles qui n'ont
jamais ete visitees peuvent etre traitees parmi la tete du tapis. Si ca ne
fonctionne pas, alors on mettra les nouvelles issues en fin de tapis. »

Ce module tient la **cle** de tri ET la **selection** (ce qui est servi) :
`membres` pour le bloc servi, `tour` pour l'etat du tour. L'exclusion des deja
servis vient de `coordination.tapis_ancre` (la file d'attente de la lane).

## La cle : la DATE DE CREATION, pas la derniere visite

La derniere visite change a chaque tour : une visite en ouvre une autre, et
un ordre construit sur une cle qui bouge ne se ferme pas -- c'est exactement
l'echec mesure le 19/11 (une rotation qui suit la POSITION ouvrait 380 issues
sur 440 en un tour, sans jamais fermer le tour). La **creation** est
immuable : l'ordre d'age est le meme a tous les tours, donc la couverture du
pool se mesure, et un bloc servi ne revient pas au hasard.

La cle, dans l'ordre :

1. la **bande** : une issue plus recente que `SEUIL_FRAICHES_H` part en FIN
   de file (le « si ca ne fonctionne pas » du mandat) ;
2. la **jamais visitée** passe devant (le mandat du 16/11 : 0 visite avant
   1 visite) ;
3. puis la **creation** : la plus ancienne d'abord.

Fonctions pures, sans reseau ni etat.
"""
from __future__ import annotations

from datetime import datetime, timezone

#: Une issue plus recente que ce seuil va en FIN de file (72 h = 3 jours).
SEUIL_FRAICHES_H = 72


def _cree(g) -> str:
    """La date de creation ISO d'un grain (vide si l'etat ne la porte pas)."""
    return getattr(g, "cree_le", "") or ""


def _dt(brut: str) -> datetime | None:
    if not brut:
        return None
    try:
        d = datetime.fromisoformat(brut.replace("Z", "+00:00"))
    except ValueError:
        return None
    return d if d.tzinfo else d.replace(tzinfo=timezone.utc)


def age_h(g, maintenant: datetime) -> float:
    """L'age de l'issue en heures, depuis sa creation."""
    d = _dt(_cree(g))
    if d is None:
        return 0.0
    return (maintenant - d).total_seconds() / 3600.0


def frais(g, maintenant: datetime, seuil_h: float = SEUIL_FRAICHES_H) -> bool:
    """L'issue est trop recente pour la tete de file."""
    return age_h(g, maintenant) < seuil_h


def jamais_visite(g) -> bool:
    """L'issue n'a jamais ete servie (aucune visite, sur toute la lecture)."""
    return int(getattr(g, "visites_total", 0) or 0) == 0


def cle(g, maintenant: datetime, seuil_h: float = SEUIL_FRAICHES_H) -> tuple:
    """La cle de l'ordre d'age : (bande, jamais_visitee, creation, numero).

    La bande passe devant tout : une issue de moins de `seuil_h` heures va
    en fin de file, meme si elle n'a jamais ete visitée.
    """
    return (1 if frais(g, maintenant, seuil_h) else 0,
            0 if jamais_visite(g) else 1,
            _cree(g),
            int(g.numero))


def trier(grains: list, maintenant: datetime,
          seuil_h: float = SEUIL_FRAICHES_H) -> list:
    """Les grains dans l'ordre d'age."""
    return sorted(grains, key=lambda g: cle(g, maintenant, seuil_h))


def bandes(grains: list, maintenant: datetime,
           seuil_h: float = SEUIL_FRAICHES_H) -> dict:
    """Le decompte des bandes d'age d'un ensemble de grains (rapport)."""
    total = len(grains)
    frais_ = sum(1 for g in grains if frais(g, maintenant, seuil_h))
    jamais = sum(1 for g in grains if jamais_visite(g))
    return {"total": total, "frais": frais_, "admis": total - frais_,
            "jamais_visitees": jamais, "seuil_h": seuil_h}


def membres(ages: list, part: int, avance: int = 0,
             exclus: set | None = None) -> tuple[list, list[int]]:
    """La SELECTION par age : les `part` premiers grains de l'ordre d'age.

    Les grains deja servis (`exclus`) sont laisses de cote, et l'ordre rendu
    est l'ordre d'age : le plus ancien d'abord. `avance` decale dans cet
    ordre (la VAGUE suivante de la prise en charge).

    Le second rendu est la **tranche primaire** : les numeros servis, dans
    l'ordre d'age. C'est elle qui porte le curseur du tour.
    """
    eligibles = [g for g in ages if g.numero not in (exclus or ())]
    depart = max(0, int(avance)) * max(part, 0)
    tranche_ = [g.numero for g in eligibles[depart:depart + max(part, 0)]]
    choisis = set(tranche_)
    return ([g for g in ages if g.numero in choisis], tranche_)


def tour(grains: list, ancres: dict | None, maintenant: datetime
         ) -> tuple[list, set, bool]:
    """L'etat de selection du tour : (ordre d'age, exclus, nouveau_tour).

    L'exclusion porte les numeros **servis et non decides** (ils attendent
    leur verdict) : une issue servie n'est pas re-servie au tirage suivant.
    Elle vient de la file d'attente de la lane (`tapis_ancre`).

    `nouveau_tour` : plus rien de servable -- la file est rendue et le tour
    recommence (le mandat du 22/11 veut que les issues anciennes
    reviennent, pas qu'elles disparaissent).
    """
    attente = ((ancres or {}).get("grains") or {}).get("attente") or {}
    exclus = {n for n, ok in attente.items() if not ok}
    ages = trier(grains, maintenant)
    if not [g for g in ages if g.numero not in exclus]:
        return ages, set(), True
    return ages, exclus, False
