#!/usr/bin/env python3
"""Le RENDU de l'OCCUPATION : les exclus, et la section courte des lanes
qui gerent l'urne.

Extrait de `tapis_occupation.py` le 24/11 (dispatch `c0035b`) : la
**troisieme** classe -- le grain de harnais -- y ajoute une section, et la
greffe faisait passer le module au-dessus de son plafond de lignes. Le
meme geste que `tapis_leger_texte` pour `tapis_leger` (22/11) et que
`tapis_universel_rapport` pour `tapis_universel`.

Le rendu est **plafonne** (`RENDU_MAX`) : une exclusion muette est
interdite, mais une liste de 284 lignes n'est pas un rapport. Au-dela du
plafond, le compte reste affiche -- l'exclusion n'est pas muette, elle est
comptee.
"""
from __future__ import annotations

from coordination import tapis_nature

#: Le rendu des exclusions est plafonne : au-dela, le compte reste affiche.
RENDU_MAX = 12


def rendre_exclus(exclus: list[dict], max_lignes: int = RENDU_MAX) -> list[str]:
    """Les lignes de rendu des exclusions, **plafonnees**.

    Une exclusion muette est interdite ; une liste de 284 lignes n'est pas un
    rapport. Au-dela du plafond, le compte reste affiche.
    """
    if not exclus:
        return []
    lignes = [f"  #{e['numero']}  {e['marque']}  {e['motif']}"
              for e in exclus[:max_lignes]]
    reste = len(exclus) - max_lignes
    if reste > 0:
        lignes.append(f"  ... et {reste} autre(s) exclusion(s) -- le compte "
                      "complet est dans la sortie JSON")
    return lignes


def _apercu(numeros: list, max_lignes: int, rendre) -> str:
    """L'apercu d'une section : la liste, et le reste compte."""
    apercu = ", ".join(rendre(n) for n in numeros[:max_lignes])
    reste = len(numeros) - max_lignes
    return apercu + (f" ... et {reste}" if reste > 0 else "")


def resume(occupation: dict[int, str], max_lignes: int = RENDU_MAX) -> list[str]:
    """La section **Occupation courte** des lanes qui gerent l'urne.

    Elles ne perdent rien : les trois classes sont pour elles une
    information, pas une exclusion. La section dit ce qui est a l'urne, ce
    qui est occupe et ce qui est du harnais, sans la liste complete.
    """
    if not occupation:
        return []
    urnes = sorted(n for n, m in occupation.items() if m == "urne")
    occupees = sorted((n, m) for n, m in occupation.items()
                       if m.startswith("occupee:"))
    harnais = sorted(n for n, m in occupation.items()
                     if m == tapis_nature.MARQUE_HARNAIS)
    lignes: list[str] = []
    if urnes:
        lignes.append(f"  urne ({len(urnes)}) : "
                      + _apercu(urnes, max_lignes, lambda n: f"#{n}"))
    if occupees:
        lignes.append(f"  occupee ({len(occupees)}) : "
                      + _apercu(occupees, max_lignes,
                                lambda t: f"#{t[0]} ({t[1].split(':', 1)[1]})"))
    if harnais:
        lignes.append(f"  harnais ({len(harnais)}) : "
                      + _apercu(harnais, max_lignes, lambda n: f"#{n}"))
    return lignes
