"""Symetrie du plan : groupes de symetrie du plan (les 17 groupes cristallographiques).

Paquet sans dependance externe : l'algebre affine exacte est dans
`symmetry.affine`, les groupes et leurs attributs derives dans
`symmetry.wallpaper`, la fermeture de chaque groupe et la signature lue sur
l'ensemble ferme dans `symmetry.closure`.

Voir `scripts/symmetry/README.md` pour la provenance, la licence et le perimetre.
"""

from .affine import Affine
from .closure import (
    GroupSignature,
    closed_set,
    compare_with_attributes,
    order_of,
    signature,
    verify_all,
)
from .wallpaper import (
    GROUPS,
    GROUPS_BY_SYMBOL,
    BravaisLattice,
    WallpaperAttributes,
    WallpaperGroup,
    attributes,
    classify_lattice,
    point_group,
    render_svg,
    translation_lattice,
)

__all__ = [
    "GROUPS",
    "GROUPS_BY_SYMBOL",
    "Affine",
    "BravaisLattice",
    "GroupSignature",
    "WallpaperAttributes",
    "WallpaperGroup",
    "attributes",
    "classify_lattice",
    "closed_set",
    "compare_with_attributes",
    "order_of",
    "point_group",
    "render_svg",
    "signature",
    "translation_lattice",
    "verify_all",
]
