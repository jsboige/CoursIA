"""Fermeture des 17 groupes de pavage : l'ensemble ferme et ses signatures.

Le quotient d'un groupe de pavage par son reseau de translation est **fini** :
deux elements qui ont la meme partie lineaire ne different que d'une
translation du reseau. Ramener la translation de chaque element au
representant canonique de sa classe (coefficients de base dans ]-1/2, 1/2])
donne donc un ensemble fini, un element par element du groupe ponctuel, et
composer deux de ses elements reste dans cet ensemble. C'est cette **fermeture**
que le module calcule, depuis les seuls generateurs.

Pourquoi fermer en plus du parcours : `wallpaper._representatives` atteint
chaque element du groupe ponctuel par un parcours en largeur borne. La
fermeture est une preuve plus forte -- l'ensemble est stable par composition,
et son cardinal est celui du groupe ponctuel -- et elle rend les signatures
**lisibles sur l'ensemble ferme** : ordre de chaque element comme isometrie du
plan, lignes de miroir, axes de glissade, centres de rotation.

Deux pieges que l'arithmetique exacte evite :

* l'ordre d'un element se lit sur ses puissances **non reduites** : le carre
  d'une glissade est une translation du reseau, qu'une reduction prematuree
  confondrait avec l'identite ;
* une classe modulo le reseau peut porter **a la fois** un miroir et une
  glissade (c'est le cas de `cm`) : miroir ou glissade se decide sur les
  lignes du groupe, jamais sur le seul representant.

Aucune dependance externe : `fractions.Fraction` suffit.

Provenance et licence : inchangees, voir `scripts/symmetry/README.md`. Le
depot `aberke/coloring-book` (licence non declaree) n'est cite que comme
inspiration ; aucun code ni asset n'en est repris (voie a).
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from fractions import Fraction

from .affine import Affine, Vector
from .wallpaper import (
    GROUPS,
    WallpaperAttributes,
    WallpaperGroup,
    _center_on_glide_axis,
    _center_on_mirror,
    _lines_of,
    _reduce_mod_lattice,
    _rotation_centers,
    attributes,
    point_group,
    translation_lattice,
)

__all__ = [
    "MAX_POINT_GROUP_ORDER",
    "GroupSignature",
    "canonical",
    "closed_set",
    "closure",
    "compare_with_attributes",
    "order_of",
    "shift_origin",
    "signature",
    "signature_from_elements",
    "verify_all",
]

F = Fraction

#: Ordre du plus grand groupe ponctuel des 17 groupes de pavage (``p6m``).
#: Il borne la fermeture : au dela, les generateurs n'engendrent pas un
#: groupe cristallographique et l'ensemble quotient n'est pas fini.
MAX_POINT_GROUP_ORDER = 12

#: Champs de la signature lus sur l'ensemble ferme et champ correspondant de
#: `WallpaperAttributes` (derive du parcours) : la comparaison champ a champ
#: est la garde de fermeture.
COMPARED_FIELDS: tuple[tuple[str, str], ...] = (
    ("order", "point_group_order"),
    ("rotation_orders", "rotation_orders"),
    ("mirror_lines", "mirror_lines"),
    ("mirror_directions", "mirror_directions"),
    ("glide_axes", "glide_axes"),
    ("glide_directions", "glide_directions"),
    ("centers_by_order", "centers_by_order"),
    ("centers_off_mirrors", "centers_off_mirrors"),
    ("centers_on_glide_axes", "centers_on_glide_axes"),
    ("total_centers", "total_centers"),
)


@dataclass(frozen=True)
class GroupSignature:
    """Signature d'un groupe de pavage, lue sur son ensemble ferme.

    Tous les champs sont des **invariants** : ils ne dependent ni du choix des
    representants ni de l'origine des coordonnees. ``rotations_by_order``
    compte les elements de rotation (hors identite) par ordre, une classe
    modulo le reseau comptant pour un ; les autres champs suivent les
    conventions de comptage de `wallpaper` (centres, lignes et directions
    par cellule primitive).
    """

    symbol: str
    conway: str
    order: int
    rotation_orders: tuple[int, ...]
    rotations_by_order: tuple[tuple[int, int], ...]
    mirror_lines: int
    mirror_directions: int
    glide_axes: int
    glide_directions: int
    centers_by_order: tuple[tuple[int, int], ...]
    centers_off_mirrors: int
    centers_on_glide_axes: int
    total_centers: int

    def key(self) -> tuple:
        """La signature sans son nom : c'est elle qui distingue deux groupes."""
        return (
            self.order,
            self.rotation_orders,
            self.rotations_by_order,
            self.mirror_lines,
            self.mirror_directions,
            self.glide_axes,
            self.glide_directions,
            self.centers_by_order,
            self.centers_off_mirrors,
            self.centers_on_glide_axes,
            self.total_centers,
        )


def canonical(element: Affine, basis: tuple[Vector, Vector]) -> Affine:
    """Element equivalent, sa translation ramenee au representant de sa classe."""
    return Affine(element.matrix, _reduce_mod_lattice(element.translation, basis))


def closure(
    generators: Iterable[Affine],
    basis: tuple[Vector, Vector],
    limit: int = MAX_POINT_GROUP_ORDER,
) -> frozenset[Affine]:
    """Fermer un jeu de generateurs par composition, modulo le reseau.

    Partant de l'identite et des generateurs, on compose tous les couples et
    on ajoute les produits jusqu'a ce que l'ensemble n'augmente plus. Pour un
    groupe cristallographique le resultat a exactement ``limit`` elements au
    plus ; sinon la fonction leve `ValueError` au lieu de boucler.
    """
    ferme: set[Affine] = {canonical(Affine.identity(), basis)}
    ferme.update(canonical(generator, basis) for generator in generators)
    while True:
        if len(ferme) > limit:
            raise ValueError(
                "ensemble non fini modulo le reseau : "
                f"{len(ferme)} elements, plus que la borne {limit} "
                "-- generateurs non cristallographiques"
            )
        produits = {canonical(a.compose(b), basis) for a in ferme for b in ferme}
        if produits <= ferme:
            return frozenset(ferme)
        ferme |= produits


def closed_set(group: WallpaperGroup) -> frozenset[Affine]:
    """L'ensemble ferme du groupe : un element par classe modulo son reseau."""
    return closure(group.generators, translation_lattice(group))


def order_of(element: Affine, limit: int = MAX_POINT_GROUP_ORDER) -> int:
    """Ordre de l'element comme isometrie du plan ; ``0`` si l'ordre est infini.

    L'ordre est le plus petit ``k >= 1`` tel que ``element^k`` soit l'identite
    **exactement**. Les puissances ne sont pas reduites modulo le reseau : le
    carre d'une glissade est une translation du reseau, et une glissade
    n'est pas une involution.
    """
    if element.is_identity:
        return 1
    power = element
    for k in range(2, limit + 1):
        power = power.compose(element)
        if power.is_identity:
            return k
    return 0


def shift_origin(element: Affine, origin: Vector) -> Affine:
    """Exprimer l'element en coordonnees ``Y = X - origin``.

    Un changement d'origine translate les translations : une isometrie
    ``X -> A X + t`` s'ecrit ``Y -> A Y + t + (A - I) origin``.
    """
    shifted = (
        element.translation[0] + (element.matrix[0][0] - 1) * origin[0]
        + element.matrix[0][1] * origin[1],
        element.translation[1] + element.matrix[1][0] * origin[0]
        + (element.matrix[1][1] - 1) * origin[1],
    )
    return Affine(element.matrix, shifted)


def signature(group: WallpaperGroup) -> GroupSignature:
    """Lire la signature du groupe sur son ensemble ferme."""
    return signature_from_elements(group, closed_set(group))


def signature_from_elements(
    group: WallpaperGroup, elements: Iterable[Affine]
) -> GroupSignature:
    """Lire la signature d'un groupe sur un jeu d'elements donne.

    ``elements`` doit contenir un representant par classe modulo le reseau de
    translation ; c'est ce que rend `closed_set`, et c'est ce qui permet de
    mesurer l'invariance de la signature sur un ensemble transforme (origine
    deplacee, generateurs equivalents).
    """
    basis = translation_lattice(group)
    ferme = frozenset(elements)
    rotations: dict[int, int] = {}
    for element in ferme:
        if not element.is_orientation_preserving:
            continue
        order = order_of(element)
        if order > 1:
            rotations[order] = rotations.get(order, 0) + 1
    mirror_lines, glide_lines = _lines_of(group, ferme)
    centers = _rotation_centers(group, ferme)
    center_counts: dict[int, int] = {}
    for _, order in centers:
        center_counts[order] = center_counts.get(order, 0) + 1
    return GroupSignature(
        symbol=group.symbol,
        conway=group.conway,
        order=len(ferme),
        rotation_orders=tuple(sorted(rotations)),
        rotations_by_order=tuple(sorted(rotations.items())),
        mirror_lines=len(mirror_lines),
        mirror_directions=len({line.direction for line in mirror_lines}),
        glide_axes=len(glide_lines),
        glide_directions=len({line.direction for line in glide_lines}),
        centers_by_order=tuple(sorted(center_counts.items())),
        centers_off_mirrors=sum(
            1 for center, _ in centers
            if not _center_on_mirror(center, group, basis, ferme)
        ),
        centers_on_glide_axes=sum(
            1 for center, _ in centers
            if _center_on_glide_axis(center, group, basis, ferme)
        ),
        total_centers=len(centers),
    )


def compare_with_attributes(
    group: WallpaperGroup, expected: WallpaperAttributes | None = None
) -> dict[str, tuple[object, object]]:
    """Champs ou la signature fermee et les attributs derives divergent.

    Rend un dictionnaire ``{champ: (valeur fermee, valeur derivee)}`` ; vide
    quand les deux derivations s'accordent sur tous les champs de
    `COMPARED_FIELDS`.
    """
    if expected is None:
        expected = attributes(group)
    fermee = signature(group)
    return {
        field: (getattr(fermee, field), getattr(expected, attribute))
        for field, attribute in COMPARED_FIELDS
        if getattr(fermee, field) != getattr(expected, attribute)
    }


def verify_all(groups: Iterable[WallpaperGroup] | None = None) -> dict[str, dict]:
    """Verifier la fermeture de chaque groupe ; rend les ecarts par symbole.

    Le dictionnaire rendu est vide quand chaque groupe se ferme, a pour
    cardinal l'ordre de son groupe ponctuel, et porte la meme signature par
    les deux derivations. Les cles autres que ``"signature"`` signalent un
    ensemble qui n'est pas un groupe de pavage.
    """
    mismatches: dict[str, dict] = {}
    for group in (GROUPS if groups is None else groups):
        basis = translation_lattice(group)
        ferme = closed_set(group)
        report: dict[str, object] = {}
        matrices = {element.matrix for element in ferme}
        if len(ferme) != len(matrices):
            report["linear_parts"] = (len(ferme), len(matrices))
        if len(ferme) != len(point_group(group)):
            report["point_group_order"] = (len(ferme), len(point_group(group)))
        leaked = [
            (a, b)
            for a in ferme
            for b in ferme
            if canonical(a.compose(b), basis) not in ferme
        ]
        if leaked:
            report["composition"] = leaked[:4]
        if not any(element.is_identity for element in ferme):
            report["identity"] = "absente"
        differences = compare_with_attributes(group)
        if differences:
            report["signature"] = differences
        if report:
            mismatches[group.symbol] = report
    return mismatches
