#!/usr/bin/env python3
"""Le SCHEMA de l'etat d'ancre : les classes, un etat neuf, les accesseurs.

L'etat est un etat de LANE : un fichier par lane, dans le repertoire local
de la machine. Son SCHEMA vit ici -- les classes, la forme d'un etat neuf,
la normalisation des numeros, les accesseurs -- et sa PERSISTANCE dans
`coordination.tapis_etat`.

Il porte aussi la **PHASE** du lot : le compteur des propositions de la
lane. Elle sert a alterner le sens de l'entrelacement (primaire/reprise) :
sans elle, une reprise en queue du lot n'est jamais lue quand la lane ne
qualifie qu'un seul candidat par tour (mesure du 19/11).

Ce module est extrait de `tapis_etat.py` (revue du 19/11) : le plafond de
lignes se paie en **extrait**, pas en relevant le plafond.
"""
from __future__ import annotations

#: Les classes de l'etat : les GRAINS et les CONTENEURS ont chacune leur
#: ancre, leur tour, leur file de reprise.
CLASSES = ("grains", "conteneurs")


def vide() -> dict:
    """Un etat neuf : aucun curseur, aucun tour, rien en attente."""
    return {c: {"ancre": None, "tour": 0, "attente": {}, "inconnus": {},
                "primaire": [], "phase": 0, "commit": None}
            for c in CLASSES}


def entiers(brut, cle: str) -> dict:
    """Un dictionnaire de numeros (les cles non numeriques sont ignorees)."""
    if not isinstance(brut, dict):
        return {}
    return {int(k): v for k, v in brut.items()
            if str(k).lstrip("-").isdigit()}


def _bloc(etat: dict | None, classe: str) -> dict:
    """Le bloc d'une classe dans l'etat lu (vide si elle est inconnue)."""
    bloc = (etat or {}).get(classe)
    return bloc if isinstance(bloc, dict) else {}


def ancre_de(etat: dict | None, classe: str) -> int | None:
    """Le numero de curseur d'une classe dans l'etat lu (None si inconnue).

    Un etat peut porter l'ancre DIRECTEMENT (le numero, sans le reste du
    bloc) : c'est la forme courte acceptee par les appels qui n'ont qu'un
    curseur a passer.
    """
    bloc = (etat or {}).get(classe)
    if isinstance(bloc, int):
        return bloc
    ancre = _bloc(etat, classe).get("ancre")
    return ancre if isinstance(ancre, int) else None


def tour_de(etat: dict | None, classe: str) -> int:
    """Le numero de tour d'une classe dans l'etat lu (0 si inconnu)."""
    tour = _bloc(etat, classe).get("tour")
    return tour if isinstance(tour, int) else 0


def phase_de(etat: dict | None, classe: str) -> int:
    """Le nombre de propositions de la classe (l'alternance du lot)."""
    phase = _bloc(etat, classe).get("phase")
    return phase if isinstance(phase, int) else 0


def inconnus_de(etat: dict | None, classe: str) -> dict:
    """Les numeros PARKES d'une classe (lecture impossible, non decides)."""
    inconnus = _bloc(etat, classe).get("inconnus")
    return inconnus if isinstance(inconnus, dict) else {}
