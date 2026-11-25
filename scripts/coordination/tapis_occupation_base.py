#!/usr/bin/env python3
"""Le SOCLE de l'occupation : qui est privilegie, comment on retire un
grain de la tete, et quel motif dire.

Extrait de `tapis_occupation.py` le 25/11 (review du coordinateur sur
#28435) : le repli **publie** ses exclusions effectives et sa
reintroduction, et les deux decisions font passer le module au-dessus de
son plafond de lignes. Une extraction, jamais un plafond releve.

Le socle ne depend de rien d'autre que de `tapis_nature` : c'est lui qui
permet a `tapis_occupation` (les trois classes) et a
`tapis_occupation_harnais` (la regle de la lane worker) de partager la
**meme** decision sans dependre l'un de l'autre.
"""
from __future__ import annotations

from coordination import tapis_nature

#: Les trois lanes qui **gerent** l'urne et l'occupation : le coordinateur
#: (`myia-ai-01:CoursIA`), l'adjoint (`myia-po-2025:CoursIA-2`) et le
#: secretaire (`myia-po-2028:CoursIA-3`), qui **ferme** l'urne (Q167 b).
#: Pour elles, les trois classes sont une information, pas une exclusion :
#: elles arbitrent, elles ne perdent pas une opportunite de travail.
LANES_PRIVILEGIEES = frozenset({"myia-ai-01:CoursIA", "myia-po-2025:CoursIA-2",
                                "myia-po-2028:CoursIA-3"})


def privilege(lane: str) -> bool:
    """La lane gerante l'urne et l'occupation (coordinateur, adjoint)."""
    return (lane or "") in LANES_PRIVILEGIEES


def retirer(grains: list, conteneurs: list, occupation: dict[int, str],
            lane: str) -> tuple[list, list, list[dict]]:
    """Retire du tirage les issues occupees ou a l'urne.

    Rend `(grains, conteneurs, exclus)`. Les exclus sont **affiches** (numero
    + marque + motif) : une exclusion silencieuse serait un grain perdu. Une
    lane privilegiee ne perd rien : elle voit les marques sans perdre la tete.
    """
    if privilege(lane) or not occupation:
        return grains, conteneurs, []
    exclus: list[dict] = []

    def _filtre(items: list) -> list:
        restes = []
        for e in items:
            marque = occupation.get(e.numero)
            if marque is None:
                restes.append(e)
            else:
                exclus.append({"numero": e.numero, "marque": marque,
                               "motif": motif(marque)})
        return restes

    return _filtre(grains), _filtre(conteneurs), exclus


def motif(marque: str) -> str:
    """Le motif lisible d'une marque d'occupation."""
    if marque == "urne":
        return ("label candidate-delivered : urne de cloture reservee au "
                "coordinateur, a l'adjoint et au secretaire (#15069) -- la lane "
                "worker rend la main")
    if marque == tapis_nature.MARQUE_HARNAIS:
        return tapis_nature.motif_harnais()
    if marque.startswith("occupee:#"):
        return (f"PR ouverte {marque.split(':', 1)[1]} d'une autre lane la "
                "cite : l'issue est occupee (collision L898 evitee)")
    return marque
