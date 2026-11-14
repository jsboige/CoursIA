"""Motifs périodiques de frise et rosaces, construits par transformations planes.

Les points d'entrée sont des motifs libres : une liste de traits, eux-mêmes
listes de couples (x, y). Pour une frise, la période horizontale vaut 1.
La construction est indépendante de toute bibliothèque de dessin ;
``draw`` utilise Matplotlib uniquement au moment de l'affichage.
"""

from __future__ import annotations

import math
from collections.abc import Sequence

Point = tuple[float, float]
Stroke = Sequence[Point]
Motif = Sequence[Stroke]

# Chaque triplet représente (x, y) -> (sx*x + dx, sy*y), modulo la
# translation horizontale entière. Les classes sont les sept groupes de frise.
FRIEZE_OPERATIONS: dict[str, tuple[tuple[int, int, float], ...]] = {
    "p1": ((1, 1, 0),),
    "p11g": ((1, 1, 0), (1, -1, 0.5)),
    "p1m1": ((1, 1, 0), (-1, 1, 0)),
    "p11m": ((1, 1, 0), (1, -1, 0)),
    "p2": ((1, 1, 0), (-1, -1, 0)),
    "p2mg": ((1, 1, 0), (-1, 1, 0), (1, -1, 0.5), (-1, -1, 0.5)),
    "p2mm": ((1, 1, 0), (-1, 1, 0), (1, -1, 0), (-1, -1, 0)),
}


def frieze(motif: Motif, group: str, periods: int = 5) -> list[list[Point]]:
    """Répéter un motif selon un groupe de frise, sur ``periods`` périodes.

    Les traits ne sont ni découpés ni ramenés dans une boîte : cela préserve
    leur continuité lorsqu'ils traversent la frontière entre deux périodes.
    """
    if group not in FRIEZE_OPERATIONS:
        raise ValueError(f"Groupe de frise inconnu : {group}")
    if not isinstance(periods, int) or isinstance(periods, bool) or periods < 1:
        raise ValueError("Le nombre de périodes doit être un entier positif")
    return [
        [(sx * x + dx + k, sy * y) for x, y in stroke]
        for k in range(periods)
        for sx, sy, dx in FRIEZE_OPERATIONS[group]
        for stroke in motif
    ]


def rosette(motif: Motif, order: int, reflections: bool = False) -> list[list[Point]]:
    """Construire une rosace cyclique C_n ou dièdrale D_n autour de l'origine."""
    if not isinstance(order, int) or isinstance(order, bool) or order < 1:
        raise ValueError("L'ordre doit être un entier positif")
    result: list[list[Point]] = []
    for k in range(order):
        angle = 2 * math.pi * k / order
        c, s = math.cos(angle), math.sin(angle)
        for sign in ((1, -1) if reflections else (1,)):
            for stroke in motif:
                result.append([(c * x - s * sign * y, s * x + c * sign * y)
                               for x, y in stroke])
    return result


def draw(strokes: Sequence[Stroke], ax: object, **plot_options: object) -> None:
    """Dessiner les traits sur un axe Matplotlib fourni par l'appelant."""
    for stroke in strokes:
        if stroke:
            xs, ys = zip(*stroke)
            ax.plot(xs, ys, **plot_options)
    ax.set_aspect("equal", adjustable="datalim")


def gallery():
    """Composer une galerie des sept frises et de deux rosaces à comparer.

    Le même motif asymétrique permet de voir les effets des transformations.
    L'appelant peut afficher ou enregistrer la figure renvoyée.
    """
    import matplotlib.pyplot as plt

    motif = [[(0.1, 0.1), (0.25, 0.4), (0.38, 0.18), (0.46, 0.3)]]
    fig, axes = plt.subplots(9, 1, figsize=(10, 14), layout="constrained")
    for ax, name in zip(axes, FRIEZE_OPERATIONS):
        draw(frieze(motif, name), ax, color="midnightblue")
        ax.set_title(name, loc="left")
        ax.axis("off")
    for ax, reflected, name in zip(axes[7:], (False, True), ("C5", "D5")):
        draw(rosette(motif, 5, reflections=reflected), ax, color="darkred")
        ax.set_title(name, loc="left")
        ax.axis("off")
    return fig


if __name__ == "__main__":
    import matplotlib.pyplot as plt

    gallery()
    plt.show()
