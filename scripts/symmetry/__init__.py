"""Symetrie du plan : groupes de symetrie du plan (les 17 groupes cristallographiques).

Paquet sans dependance externe : l'algebre affine exacte est dans
`symmetry.affine`, les groupes et leurs attributs derives dans
`symmetry.wallpaper`.

Voir `scripts/symmetry/README.md` pour la provenance, la licence et le perimetre.
"""

from .affine import Affine
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
    "WallpaperAttributes",
    "WallpaperGroup",
    "attributes",
    "classify_lattice",
    "point_group",
    "render_svg",
    "translation_lattice",
]
