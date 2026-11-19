#!/usr/bin/env python3
"""L'ANCRE de la rotation : le dernier numero qualifie, persistant.

Une rotation qui avance d'un cran **par position** saute des numeros quand le
pool change : une cloture decale l'index, et la tranche suivante recommence
ailleurs. Temoin mesure le 19/11 (peer ai-01:CoursIA) : pool 1..8, blocs de
2, offset 0 -> bloc {1,2} ; on cloture #1 -> blocs {4,5}, {6,7}, {8,2} : **#3
est encore ouverte et n'a jamais ete visitee** apres les quatre tranches
annoncees.

L'ancre porte le **numero** du dernier grain qualifie, pas sa position : le
prochain bloc commence au premier numero strictement superieur. Une cloture
(ou une arrivee) ne deplace plus le curseur, et le tour se ferme sur le pool
reel. L'ancre est **persistee** par lane (et par classe : grains,
conteneurs) : sans elle, chaque tranche repart de zero et le tour ne se ferme
jamais.

Le module tient aussi l'**ordre de service** : la rotation choisit QUELS
numeros sont servis, l'ordre de PRIORITE decide de l'ordre dans le bloc.
"""
from __future__ import annotations

import json
import os
from pathlib import Path

ENV_ETAT = "COURSIA_TAPIS_ANCRE_DIR"


def chemin_etat(lane: str) -> Path:
    """Le fichier d'ancre de la lane (LOCALAPPDATA par defaut)."""
    base = os.environ.get(ENV_ETAT) or os.environ.get("LOCALAPPDATA")
    racine = Path(base) if base else Path.home() / ".coursia"
    return racine / "CoursIA" / "tapis_ancre" / f"{lane.replace(':', '-')}.json"


def lire(lane: str) -> dict:
    """Les ancres de la lane : `{"grains": numero|None, "conteneurs": ...}`.

    Un fichier absent ou illisible ne vaut PAS zero : il vaut inconnu, et un
    inconnu ne s'acquitte pas (fail-CLOSED).
    """
    vide = {"grains": None, "conteneurs": None}
    try:
        brut = json.loads(chemin_etat(lane).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return vide
    if not isinstance(brut, dict):
        return vide
    return {c: (brut.get(c) if isinstance(brut.get(c), int) else None)
            for c in ("grains", "conteneurs")}


def ecrire(lane: str, ancres: dict) -> Path:
    """Persiste les ancres de la lane (une ecriture atomique)."""
    chemin = chemin_etat(lane)
    chemin.parent.mkdir(parents=True, exist_ok=True)
    corps = json.dumps({c: ancres.get(c) for c in ("grains", "conteneurs")},
                       ensure_ascii=False, indent=1) + "\n"
    tmp = chemin.with_suffix(".tmp")
    tmp.write_text(corps, encoding="utf-8")
    tmp.replace(chemin)
    return chemin


def position(nums: list[int], ancre: int | None) -> int:
    """L'index du premier numero strictement superieur a l'ancre (cyclique).

    Ancre absente -> 0 (le tour commence par le plus petit numero). Ancre
    superieure a tous les numeros -> 0 : le tour a boucle, on recommence.
    """
    if not nums or ancre is None:
        return 0
    for i, n in enumerate(nums):
        if n > ancre:
            return i
    return 0


def tranche(nums: list[int], ancre: int | None, part: int,
            avance: int = 0) -> list[int]:
    """La tranche d'apres l'ancre : `part` numeros, cyclique.

    `avance` decale de N tranches (la VAGUE suivante). La liste `nums` est
    supposee TRIEE par numero : c'est l'ordre de couverture du tour.
    """
    if not nums or part <= 0:
        return []
    n = len(nums)
    depart = (position(nums, ancre) + avance * part) % n
    return [nums[(depart + i) % n] for i in range(min(part, n))]


def membres(ordre: list, ancre: int | None, part: int, avance: int = 0,
             depart_alea: int = 0) -> tuple[list, int | None]:
    """Les membres du bloc, ORDONNES par priorite (l'ordre d'entree).

    La SELECTION est la tranche d'apres l'ancre ; l'ORDRE rendu est celui de
    l'entree : la rotation choisit QUOI servir, la priorite decide de
    l'ordre. Sans ancre, le depart vient de `depart_alea` (le decalage de la
    lane) et l'ancre qui en sort devient l'ancre du tour suivant.
    """
    nums = sorted(g.numero for g in ordre)
    if not nums:
        return [], None
    if ancre is None:
        depart = depart_alea % len(nums)
        tranche_ = [nums[(depart + i) % len(nums)]
                    for i in range(min(part, len(nums)))]
    else:
        tranche_ = tranche(nums, ancre, part, avance)
    choisis = set(tranche_)
    return ([g for g in ordre if g.numero in choisis],
            tranche_[-1] if tranche_ else None)
