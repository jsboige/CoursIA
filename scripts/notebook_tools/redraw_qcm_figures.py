#!/usr/bin/env python3
"""Redessine la figure du reseau bayesien de la banque QCM (#18263).

Contexte (revue ai-01 du 2026-09-28) : trois figures presentes dans les
exports Moodle ne peuvent pas entrer en l'etat dans un depot public --
`ia4-004` est la photographie d'une page du manuel Russell & Norvig,
`ia4-006`/`ia4-007` deux captures d'ecran de la meme table du manuel, et
`ia2-010` publie une URL Dropbox personnelle. Les deux dernieres sont
remplacees par du texte dans les enonces (tableau markdown pour la table du
dentiste, marqueur neutre pour l'URL) ; `ia4-004` est **redessinee** : le
reseau ne porte que des valeurs, et un trace deterministe les restitue sans
reproduire la mise en page de l'ouvrage.

    python scripts/notebook_tools/redraw_qcm_figures.py \
        --out MyIA.AI.Notebooks/cross-series/qcm/images

`moodle_bank.py convert` appelle `draw_ia4_004` : une re-conversion regenere
la figure redessinee au lieu de reintroduire la photographie.
"""

from __future__ import annotations

import argparse
import os

# Valeurs du reseau (Russell & Norvig, Artificial Intelligence: A Modern
# Approach, fig. 14.23) : seules les valeurs sont reprises, le trace est le
# notre. Variables : T transgresse la loi, P procureur politiquement engage,
# I inculpe, C coupable, E emprisonne.
P_T = 0.9
P_P = 0.1
P_I_T_P = {("V", "V"): 0.9, ("V", "F"): 0.5, ("F", "V"): 0.5, ("F", "F"): 0.1}
P_C_T_I_P = {
    ("V", "V", "V"): 0.9,
    ("V", "V", "F"): 0.8,
    ("V", "F", "V"): 0.0,
    ("V", "F", "F"): 0.0,
    ("F", "V", "V"): 0.2,
    ("F", "V", "F"): 0.1,
    ("F", "F", "V"): 0.0,
    ("F", "F", "F"): 0.0,
}
P_E_C = {"V": 0.9, "F": 0.0}

# Sommets du graphe : lettre -> (position, nom)
NOEUDS = {
    "T": ((0.12, 0.84), "transgresse la loi"),
    "P": ((0.88, 0.84), "procureur politiquement engage"),
    "I": ((0.50, 0.58), "inculpe"),
    "C": ((0.50, 0.32), "coupable"),
    "E": ((0.50, 0.08), "emprisonne"),
}
ARCS = [("T", "I"), ("P", "I"), ("T", "C"), ("P", "C"), ("I", "C"), ("C", "E")]

CREDIT = (
    "Redessine d'apres Russell et Norvig, Artificial Intelligence: A Modern "
    "Approach, fig. 14.23"
)

# Lecture V d'abord (comme la table du dentiste des enonces ia4-006/007).
_ORDRE = {"V": 0, "F": 1}


def _tri(cles):
    return sorted(cles, key=lambda c: tuple(_ORDRE[x] for x in c))


def _table(ax, titre: str, en_tete: list[str], lignes: list[list[str]]) -> None:
    """Rend une table de probabilites conditionnelles dans l'axe `ax`."""
    ax.axis("off")
    ax.set_title(titre, fontsize=10, pad=6)
    table = ax.table(
        cellText=lignes,
        colLabels=en_tete,
        loc="upper center",
        cellLoc="center",
        colLoc="center",
    )
    table.auto_set_font_size(False)
    table.set_fontsize(9)
    table.scale(1.0, 1.25)
    for cellule in table.get_celld().values():
        cellule.set_linewidth(0.4)


def draw_ia4_004(out_dir: str) -> str:
    """Trace la figure redessinee et rend le chemin du PNG ecrit."""
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.patches import FancyBboxPatch

    os.makedirs(out_dir, exist_ok=True)
    chemin = os.path.join(out_dir, "ia4-004.png")

    fig = plt.figure(figsize=(13.0, 7.0), dpi=150)
    grille = fig.add_gridspec(1, 3, width_ratios=[1.25, 0.85, 1.05], wspace=0.12)

    # --- graphe -----------------------------------------------------------
    ax = fig.add_subplot(grille[0, 0])
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis("off")
    ax.set_title("Reseau bayesien", fontsize=11, pad=6)
    for origine, cible in ARCS:
        (x0, y0), _ = NOEUDS[origine]
        (x1, y1), _ = NOEUDS[cible]
        ax.annotate(
            "",
            xy=(x1, y1),
            xytext=(x0, y0),
            arrowprops=dict(arrowstyle="-|>", color="#333333", shrinkA=24, shrinkB=24),
        )
    for lettre, ((x, y), nom) in NOEUDS.items():
        ax.add_patch(
            FancyBboxPatch(
                (x - 0.10, y - 0.055),
                0.20,
                0.11,
                boxstyle="round,pad=0.012,rounding_size=0.02",
                linewidth=1.2,
                edgecolor="#1f4e79",
                facecolor="#dce9f5",
            )
        )
        ax.text(x, y, lettre, ha="center", va="center", fontsize=15, fontweight="bold")
    legende = "   ".join(f"{lettre} : {nom}" for lettre, (_, nom) in sorted(NOEUDS.items()))
    ax.figure.text(0.5, 0.055, legende, ha="center", va="bottom", fontsize=8)

    # --- tables des parents racines et des descendants --------------------
    milieu = grille[0, 1].subgridspec(3, 1, height_ratios=[0.8, 1.7, 0.9], hspace=0.35)
    ax_racines = fig.add_subplot(milieu[0, 0])
    _table(ax_racines, "Probabilites a priori", ["Variable", "P(V)"],
           [["T", f"{P_T:.1f}"], ["P", f"{P_P:.1f}"]])

    ax_i = fig.add_subplot(milieu[1, 0])
    _table(ax_i, "P(I | T, P)", ["T", "P", "P(I|T,P)"],
           [[t, p, f"{P_I_T_P[(t, p)]:.1f}"] for t, p in _tri(P_I_T_P)])

    ax_e = fig.add_subplot(milieu[2, 0])
    _table(ax_e, "P(E | C)", ["C", "P(E|C)"],
           [[c, f"{P_E_C[c]:.1f}"] for c in _tri(P_E_C)])

    ax_c = fig.add_subplot(grille[0, 2])
    _table(ax_c, "P(C | T, I, P)", ["T", "I", "P", "P(C|T,I,P)"],
           [[t, i, p, f"{P_C_T_I_P[(t, i, p)]:.1f}"] for t, i, p in _tri(P_C_T_I_P)])

    fig.text(0.5, 0.015, CREDIT, ha="center", fontsize=8, style="italic", color="#555555")
    fig.savefig(chemin, bbox_inches="tight", facecolor="white",
                metadata={"Software": "redraw_qcm_figures.py (CoursIA #18263)"})
    plt.close(fig)
    return chemin


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", default="MyIA.AI.Notebooks/cross-series/qcm/images",
                    help="dossier images/ de la banque QCM")
    args = ap.parse_args()
    chemin = draw_ia4_004(args.out)
    print(f"ecrit: {chemin}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())