#!/usr/bin/env python3
"""La PREUVE d'une livraison : le diff de la PR **et l'etat de la PR`.

`/files` ne dit pas si la PR a ete **integree** : une PR **fermee sans
fusion** porte un diff, mais le travail n'est jamais arrive sur `main`. La
preuve porte donc les deux choses -- les fichiers modifies, et l'etat de la
PR (revue du 19/11, DM `night-27242-unknown-scope-stays-in-rotation`).

Un etat **inconnu** rend la preuve **incomplete** : fail-CLOSED, elle
n'atteste pas une livraison complete.

Ce module est extrait de `coordination.tapis_diff` (le verdict) pour tenir
le plafond de lignes de la serie.
"""
from __future__ import annotations

import json
import sys
from dataclasses import dataclass
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from coordination import gh_bulk

#: Les etats de PR que GitHub rend (`state`).
ETATS = ("OPEN", "CLOSED", "MERGED")


@dataclass(frozen=True)
class Preuve:
    """Les fichiers modifies par la PR, et l'etat de la PR.

    `etat` vide = **inconnu** : la preuve est incomplete, et fail-CLOSED
    elle vaut le maintien dans la rotation, jamais l'exclusion.
    """

    fichiers: tuple[str, ...]
    etat: str = ""
    fusionne: bool = False

    @property
    def etat_known(self) -> bool:
        return self.etat in ETATS

    @property
    def integree(self) -> bool:
        """La PR est-elle integree (fusionnee) ou en cours (ouverte) ?

        Une PR **fermee sans fusion** n'est integree par rien : le travail
        qu'elle porte n'est jamais arrive sur `main`.
        """
        return self.fusionne or self.etat == "OPEN"


def comme_preuve(preuve) -> Preuve:
    """Normalise une preuve : une liste de fichiers seule n'en est pas une.

    Sans l'etat de la PR, la preuve est **incomplete** -- fail-CLOSED, elle
    ne peut pas attester une livraison complete.
    """
    if isinstance(preuve, Preuve):
        return preuve
    return Preuve(tuple(preuve or ()))


def diff_pr(depot: str, numero: int, run) -> list[str] | None:
    """Les fichiers modifies par la PR ; None si la lecture echoue (fail-CLOSED)."""
    argv = ["gh", "api", f"repos/{depot}/pulls/{numero}/files?per_page=100"]
    try:
        texte = gh_bulk._appel(run, argv, "diff_pr", numero)
        donnees = json.loads(texte or "[]")
        return [f.get("filename") for f in donnees if f.get("filename")]
    except Exception:  # noqa: BLE001 - une preuve absente ne vaut jamais exclusion
        return None


def etat_pr(depot: str, numero: int, run) -> tuple[str, bool] | None:
    """(etat, fusionne) de la PR ; None si la lecture echoue (fail-CLOSED)."""
    argv = ["gh", "api", f"repos/{depot}/pulls/{numero}"]
    try:
        texte = gh_bulk._appel(run, argv, "etat_pr", numero)
        donnees = json.loads(texte or "{}")
        return (str(donnees.get("state") or "").upper(),
                bool(donnees.get("merged_at")))
    except Exception:  # noqa: BLE001 - une preuve absente ne vaut jamais exclusion
        return None


def preuve_gh(run, depot: str = gh_bulk.DEPOT_GH):
    """Le callable de preuve : le diff ET l'etat de la PR, lus sur GitHub.

    Rend `None` quand la lecture echoue (preuve absente) : fail-CLOSED vers
    l'exclusion, l'issue reste alors dans la rotation.
    """
    def preuve(numero: int | None) -> Preuve | None:
        if not numero:
            return None
        fichiers = diff_pr(depot, numero, run)
        if fichiers is None:
            return None
        etat = etat_pr(depot, numero, run)
        if etat is None:
            return Preuve(tuple(fichiers))    # etat inconnu -> fail-CLOSED
        return Preuve(tuple(fichiers), etat[0], etat[1])
    return preuve
