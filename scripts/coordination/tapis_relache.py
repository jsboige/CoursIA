#!/usr/bin/env python3
"""La portee d'une remise de main : un echec d'outillage ne gele que sa lane.

Avant (#28114, dispatch `c0035b` du coordinateur, 24/11) : une remise de main
de moins de trois jours ecartait le grain pour **TOUTE** la flotte. Un echec
d'outillage d'une seule lane perdait alors le grain pour tout le monde -- et
les 5 grains degeles par cette regle sont les productions Rust rendues par
`myia-po-2028:claudish` (#27720, #27721, #28064, #28085, #28097).

La regle :

- un **echec d'OUTIL** (vocabulaire ferme, `tapis_relache_motif`) ne gele que
  la lane qui l'a subi -- les autres n'ont pas le meme outillage ;
- une **barriere reelle** (GPU, siege, arbitrage, proprietaire nomme) gele
  toute la flotte : le comportement d'avant, intact ;
- un motif **inconnu** ou **ambigu** gele toute la flotte (fail-CLOSED).

Ce module est extrait de `tapis_attente` pour que celui-ci tienne son plafond.
"""
from __future__ import annotations

from coordination import tapis_attente, tapis_relache_motif

#: La fenetre de remise de main, en jours (celle de `tapis_attente`).
RELACHE_J = tapis_attente.RELACHE_J

#: Les marques qui ouvrent une prise en charge (le rendu sans lane nommee).
_OUVERTURE = ("CLAIMED", "CLAIMED-AMEND")


def _lane_du_rendu(evts: list) -> str | None:
    """La lane qui a rendu le grain : celle que nomme le marqueur, sinon celle
    du **dernier claim qui precede** la remise de main -- c'est la lane qui
    produisait."""
    if evts[-1].lane:
        return evts[-1].lane
    for e in reversed(evts[:-1]):
        if e.marque in _OUVERTURE and e.lane:
            return e.lane
    return None


def _motif_globale(ev, age: float) -> str:
    """Le motif d'avant : le gel vaut pour toute la flotte."""
    return f"rendue par {ev.lane or '?'} il y a {age} j (< {RELACHE_J} j) : lire son motif"


def relachee(evts: list, ctx: dict) -> str | None:
    """Le motif d'ecart d'un grain rendu, ou None (servable pour la lane
    courante).

    Un echec d'outillage rendu par **une autre** lane ne gèle pas la lane
    courante : le grain redevient servable ici, et reste gelé chez celle qui
    l'a subi.
    """
    if not evts or evts[-1].marque != "RELEASED" or evts[-1].attend:
        return None  # un [RELEASED] qui porte une condition est une PAUSE
    ev = evts[-1]
    age = round((ctx["maintenant"] - ev.quand).total_seconds() / 86400, 1)
    if age >= RELACHE_J:
        return None
    codes = tapis_relache_motif.codes_outil(ev.corps)
    if not codes:
        return _motif_globale(ev, age)  # barriere reelle, motif inconnu, ambigu
    lane = _lane_du_rendu(evts)
    if lane is None:
        return _motif_globale(ev, age)  # fail-CLOSED : personne n'a nomme la lane
    if lane != ctx["lane"]:
        return None  # echec d'outillage d'une autre lane : servable ici
    codes_txt = ", ".join(sorted(codes))
    return (f"echec d'outillage ({codes_txt}) sur {lane} il y a {age} j : "
            f"cette lane est gelee, pas les autres")
