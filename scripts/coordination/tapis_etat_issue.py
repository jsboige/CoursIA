#!/usr/bin/env python3
"""L'ETAT d'une issue ouverte pour une lane -- le dataclass du tirage.

Seam d'extraction de `tapis_rapide.py` (plafond de lignes, 19/11) : le
dataclass **vivait** dans le module du tirage, qui ne pouvait plus porter la
CLE DE SERVICE (deux champs de plus) sans depasser son plafond.

`coordination.tapis_rapide` le reintroduit (`from coordination.tapis_etat_issue
import Etat`), donc tous les consommateurs (`tapis_rapide.Etat`,
`visit_coverage.Etat`, les tests) continuent de fonctionner : une seule
adresse.

Ne pas confondre avec `coordination.tapis_etat` (l'etat d'ANCRE de la lane,
sur disque) ni avec `tapis_dernier_grain.EtatGrain` (l'etat de grain
c3274, mesure par le fil complet).
"""
from __future__ import annotations

from dataclasses import dataclass, field


@dataclass
class Etat:
    """L'etat d'une issue ouverte pour une lane : servable si `ecart` est None."""

    numero: int
    titre: str
    labels: list[str]
    cree_le: str
    parent: int | None
    famille: int
    conteneur: bool
    consolidation: bool
    derniere_visite: str | None = None
    visites: int = 0  # seances du tour (FENETRE_J jours), l'unite de l'equilibrage
    visites_total: int = 0  # seances sur toute la lecture
    ecart: str | None = None
    motif: str = ""
    notes: list[str] = field(default_factory=list)
    mon_claim: bool = False
    occupes: list[tuple[str, str]] = field(default_factory=list)  # (lane, paths) bornes
    #: L'etat de grain (c3274) : `grain`, `passage_seul`, `jamais_servie` ou
    #: `non_measurable`. `None` = inconnu (la voie legere ne lit pas le fil).
    etat_grain: str | None = None
    #: La CLE DE SERVICE (19/11) : la date de la derniere PR qui **couvre**
    #: le grain, vide si aucune PR ne le couvre (l'anciennete tombe alors
    #: sur la creation). `cle_origine` nomme la source de cette date.
    cle_service: str = ""
    cle_origine: str = ""
