#!/usr/bin/env python3
"""L'ECRITURE de l'etat d'ancre : le fichier, et rien d'autre.

L'etat est un etat de LANE : il vit dans le repertoire local de la machine
(`LOCALAPPDATA`), jamais dans le depot. Un fichier absent ou illisible
vaut INCONNU (fail-CLOSED) : il ne vaut pas zero.

Ce module tient la PERSISTANCE ; la machine a etat elle vit dans
`coordination.tapis_ancre`, l'arithmetique de selection dans
`coordination.tapis_tranche`.
"""
from __future__ import annotations

import json
import os
from pathlib import Path

ENV_ETAT = "COURSIA_TAPIS_ANCRE_DIR"
CLASSES = ("grains", "conteneurs")


def chemin_etat(lane: str) -> Path:
    """Le fichier d'ancre de la lane (LOCALAPPDATA par defaut)."""
    base = os.environ.get(ENV_ETAT) or os.environ.get("LOCALAPPDATA")
    racine = Path(base) if base else Path.home() / ".coursia"
    return racine / "CoursIA" / "tapis_ancre" / f"{lane.replace(':', '-')}.json"


def vide() -> dict:
    """Un etat neuf : aucun curseur, aucun tour, rien en attente."""
    return {c: {"ancre": None, "tour": 0, "attente": {}, "inconnus": {},
                "primaire": []}
            for c in CLASSES}


def _entiers(brut, cle: str) -> dict:
    """Un dictionnaire de numeros (les cles non numeriques sont ignorees)."""
    if not isinstance(brut, dict):
        return {}
    return {int(k): v for k, v in brut.items()
            if str(k).lstrip("-").isdigit()}


def lire(lane: str) -> dict:
    """L'etat normalise ; absent ou illisible = inconnu (fail-CLOSED)."""
    etat = vide()
    try:
        brut = json.loads(chemin_etat(lane).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return etat
    if not isinstance(brut, dict):
        return etat
    for c in CLASSES:
        bloc = brut.get(c)
        if not isinstance(bloc, dict):
            continue
        ancre = bloc.get("ancre")
        etat[c]["ancre"] = ancre if isinstance(ancre, int) else None
        tour = bloc.get("tour")
        etat[c]["tour"] = tour if isinstance(tour, int) else 0
        etat[c]["attente"] = {n: bool(b) for n, b
                              in _entiers(bloc.get("attente"), "attente").items()}
        etat[c]["inconnus"] = _entiers(bloc.get("inconnus"), "inconnus")
        primaire = bloc.get("primaire")
        etat[c]["primaire"] = sorted(
            n for n in primaire if isinstance(n, int)) if isinstance(
                primaire, list) else []
    return etat


def ancre_de(etat: dict | None, classe: str) -> int | None:
    """Le numero de curseur d'une classe dans l'etat lu (None si inconnue)."""
    if not isinstance(etat, dict):
        return None
    bloc = etat.get(classe)
    if isinstance(bloc, int):
        return bloc
    if isinstance(bloc, dict):
        ancre = bloc.get("ancre")
        return ancre if isinstance(ancre, int) else None
    return None


def tour_de(etat: dict | None, classe: str) -> int:
    """Le numero de tour d'une classe (0 si inconnu)."""
    bloc = (etat or {}).get(classe)
    if isinstance(bloc, dict) and isinstance(bloc.get("tour"), int):
        return bloc["tour"]
    return 0


def inconnus_de(etat: dict | None, classe: str) -> dict:
    """Les numeros PARKES d'une classe (lecture impossible, non decides)."""
    bloc = (etat or {}).get(classe)
    if isinstance(bloc, dict) and isinstance(bloc.get("inconnus"), dict):
        return bloc["inconnus"]
    return {}


def ecrire(lane: str, etat: dict) -> Path:
    """Persiste l'etat (une ecriture atomique)."""
    chemin = chemin_etat(lane)
    chemin.parent.mkdir(parents=True, exist_ok=True)
    corps = {c: {"ancre": etat.get(c, {}).get("ancre"),
                  "tour": etat.get(c, {}).get("tour", 0),
                  "attente": {str(n): b for n, b in
                              etat.get(c, {}).get("attente", {}).items()},
                  "inconnus": etat.get(c, {}).get("inconnus", {}),
                  "primaire": list(etat.get(c, {}).get("primaire") or [])}
             for c in CLASSES}
    tmp = chemin.with_suffix(".tmp")
    tmp.write_text(json.dumps(corps, ensure_ascii=False, indent=1) + "\n",
                   encoding="utf-8")
    tmp.replace(chemin)
    return chemin
