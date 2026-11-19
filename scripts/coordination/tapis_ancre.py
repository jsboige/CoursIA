#!/usr/bin/env python3
"""L'ANCRE de la rotation : l'etat PERSISTANT du dernier numero qualifie.

Une rotation qui avance par POSITION saute des numeros des que le pool
change (une cloture, une arrivee) -- temoin mesure le 19/11 (peer
ai-01:CoursIA) : #3 ouverte, jamais visitee apres quatre tranches. L'ancre
porte le **numero** du dernier grain qualifie.

**L'ancre n'avance que sur un verdict TERMINAL** (peer, 19/11) : le tirage
PROPOSE (`proposer`), la qualification DECIDE (`avancer`). Un tirage sans
action, ou un lot dont une lecture a echoue, ne la deplace pas.

L'arithmetique de la selection vit dans `coordination.tapis_tranche`.
"""
from __future__ import annotations

import json
import os
from pathlib import Path

from coordination.tapis_tranche import membres, position, tranche  # noqa: F401

ENV_ETAT = "COURSIA_TAPIS_ANCRE_DIR"
CLASSES = ("grains", "conteneurs")


def chemin_etat(lane: str) -> Path:
    """Le fichier d'ancre de la lane (LOCALAPPDATA par defaut)."""
    base = os.environ.get(ENV_ETAT) or os.environ.get("LOCALAPPDATA")
    racine = Path(base) if base else Path.home() / ".coursia"
    return racine / "CoursIA" / "tapis_ancre" / f"{lane.replace(':', '-')}.json"


def _vide() -> dict:
    return {c: {"ancre": None, "attente": {}} for c in CLASSES}


def ancre_de(etat: dict | None, classe: str) -> int | None:
    """Le numero d'ancre d'une classe dans l'etat lu (None si inconnue)."""
    if not isinstance(etat, dict):
        return None
    bloc = etat.get(classe)
    if isinstance(bloc, int):
        return bloc
    if isinstance(bloc, dict):
        ancre = bloc.get("ancre")
        return ancre if isinstance(ancre, int) else None
    return None


def lire(lane: str) -> dict:
    """L'etat de l'ancre ; absent ou illisible = inconnu (fail-CLOSED)."""
    vide = _vide()
    try:
        brut = json.loads(chemin_etat(lane).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return vide
    if not isinstance(brut, dict):
        return vide
    for c in CLASSES:
        bloc = brut.get(c)
        if not isinstance(bloc, dict):
            continue
        ancre = bloc.get("ancre")
        vide[c]["ancre"] = ancre if isinstance(ancre, int) else None
        att = bloc.get("attente")
        if isinstance(att, dict):
            vide[c]["attente"] = {int(k): bool(v) for k, v in att.items()
                                  if str(k).lstrip("-").isdigit()}
    return vide


def ecrire(lane: str, etat: dict) -> Path:
    """Persiste l'etat de l'ancre (une ecriture atomique)."""
    chemin = chemin_etat(lane)
    chemin.parent.mkdir(parents=True, exist_ok=True)
    corps = {c: {"ancre": etat.get(c, {}).get("ancre"),
                  "attente": {str(n): b for n, b in
                              etat.get(c, {}).get("attente", {}).items()}}
             for c in CLASSES}
    tmp = chemin.with_suffix(".tmp")
    tmp.write_text(json.dumps(corps, ensure_ascii=False, indent=1) + "\n",
                   encoding="utf-8")
    tmp.replace(chemin)
    return chemin


def proposer(lane: str, classe: str, numeros: list[int]) -> dict:
    """Enregistre les numeros PROPOSES par le tirage, sans bouger l'ancre.

    Le tirage **selectionne** ; il ne qualifie pas. Un tirage sans action
    laisse donc l'ancre en place -- sinon un numero pourrait etre declare
    visite sans avoir jamais ete qualifie.
    """
    etat = lire(lane)
    att = etat[classe]["attente"]
    for n in numeros:
        att.setdefault(n, False)
    etat[classe]["attente"] = att
    ecrire(lane, etat)
    return etat


def avancer(lane: str, terminaux: set[int]) -> dict:
    """Fait avancer l'ancre sur les verdicts TERMINAUX connus.

    L'ancre ne passe jamais un numero dont le verdict n'est pas connu : elle
    s'arrete au premier numero en attente. Un lot partiel (une lecture en
    echec) la laisse donc en place.
    """
    etat = lire(lane)
    for c in CLASSES:
        att = etat[c]["attente"]
        for n in terminaux:
            if n in att:
                att[n] = True
        ancre = etat[c]["ancre"]
        for n in sorted(att):
            if ancre is not None and n <= ancre:
                continue
            if not att[n]:
                break
            ancre = n
        etat[c]["ancre"] = ancre
        etat[c]["attente"] = {n: b for n, b in att.items()
                              if ancre is None or n > ancre}
    ecrire(lane, etat)
    return etat
