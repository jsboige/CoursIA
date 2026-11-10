"""Les 17 groupes de symetrie du plan (wallpaper groups).

Ce module fait deux choses, volontairement separees.

1. **Il ENGENDRE** chaque groupe : un jeu de generateurs affines exacts
   (matrice 2x2 rationnelle + translation rationnelle). Rien n'est recopie
   d'une table : la classification est **rederivee** des generateurs.

2. **Il DERIVE** de ces generateurs les attributs qui caracterisent un groupe
   de symetrie du plan : le type de reseau de Bravais, l'ordre du groupe
   ponctuel, les ordres de rotation presents, les directions de miroir, les
   axes de glissade, les centres de rotation (avec leur ordre maximal) et
   ceux qui ne sont sur aucun miroir.

Ces attributs calcules sont compares a une table de reference (celle de la
crystallographie, reprise dans `scripts/tests/test_wallpaper_groups.py`). La
table est donc une **reference opposee**, et non la source du calcul : si les
generateurs etaient faux, le test echouerait.

Conventions de comptage (a lire avant de comparer a une autre source)
-----------------------------------------------------------------------

* Les **centres de rotation** sont comptes modulo le **reseau de translation
  primitif** du groupe, et chaque centre est attribue a son **ordre maximal**
  (un point centre d'un sixieme de tour est aussi centre d'un tiers de tour,
  mais il est compte comme d'ordre 6).
* Les **directions de miroir** sont comptees modulo le signe (une droite et
  son opposée sont la meme direction).
* Les **lignes** de miroir et d'axe de glissade sont comptees **par cellule
  primitive** : une ligne est identifiee par sa direction et son decalage
  normalise modulo l'epaisseur du reseau dans cette direction.
* Une **glissade** est un element orientation-reversing dont la composante le
  long de son axe est non nulle ; son axe est une ligne distincte de toute
  ligne de miroir, sinon la glissade n'est qu'un miroir translate.

Provenance et licence
---------------------
La classification des 17 groupes est un **fait mathematique** (nomenclature
IUC et notation orbifold de Conway). Les valeurs de reference viennent de
pages « Wallpaper group », « Orbifold notation » et « List of planar symmetry
groups » de Wikipedia, **archivees dans le gisement partage** (jamais dans le
depot) : leurs empreintes SHA-256 sont dans `scripts/symmetry/README.md`.

Le depot d'origine `aberke/coloring-book` (art generatif de symetrie,
**licence non declaree**) n'est cite que comme **inspiration** : aucun code, ni
aucun asset, ni aucune illustration n'en est repris ici. La reimplementation
est **independante** (voie a). Voir `scripts/symmetry/README.md`.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction
from math import gcd

from .affine import (
    Affine,
    Matrix,
    Vector,
    identity_matrix,
    mat_det,
    mat_inv,
    mat_mul,
    mat_vec,
    vec_add,
    vec_sub,
)

__all__ = [
    "GROUPS",
    "GROUPS_BY_SYMBOL",
    "BravaisLattice",
    "WallpaperAttributes",
    "WallpaperGroup",
    "attributes",
    "classify_lattice",
    "point_group",
    "render_svg",
    "translation_lattice",
]

F = Fraction

# --------------------------------------------------------------------------
# Reseaux de Bravais
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class BravaisLattice:
    """Un reseau de Bravais, decrit par sa forme quadratique.

    ``metric`` est la matrice de Gram de la base utilisee par les generateurs
    (coordonnees de base). Pour une base (e1, e2), ``metric[i][j] = e_i . e_j``.
    Une metrique rationnelle suffit : aucune racine n'intervient dans les
    invariants, seule la forme de rendu en demande une.
    """

    name: str
    metric: Matrix
    #: description francaise du reseau (affichee par l'outil en ligne de commande)
    description: str

    def cartesian_basis(self) -> tuple[tuple[float, float], tuple[float, float]]:
        """Base cartesienne associee a la metrique (``e1 = (1, 0)`` par convention).

        Avec ``metric = [[a, b], [b, c]]`` et ``e1 = (1, 0)``, on prend
        ``e2 = (b, sqrt(c - b^2))`` : le produit scalaire ``e1 . e2 = b`` et
        ``|e2|^2 = c`` sont alors exacts.
        """
        a = float(self.metric[0][0])
        b = float(self.metric[0][1])
        c = float(self.metric[1][1])
        if a <= 0:
            raise ValueError("metrique invalide")
        e1 = (1.0, 0.0)
        e2 = (b, (c - b * b) ** 0.5)
        # e1 doit porter la longueur de reference : on met a l'echelle.
        scale = a**0.5
        return ((e1[0] * scale, e1[1] * scale), (e2[0] * scale, e2[1] * scale))

    def to_cartesian(self, point: Vector) -> tuple[float, float]:
        """Convertit un point de base en coordonnees cartesiennes."""
        (e1, e2) = self.cartesian_basis()
        return (
            float(point[0]) * e1[0] + float(point[1]) * e2[0],
            float(point[0]) * e1[1] + float(point[1]) * e2[1],
        )


OBLIQUE = BravaisLattice(
    "oblique",
    ((F(1), F(1, 3)), (F(1, 3), F(2))),
    "reseau generique (angles et longueurs sans contrainte)",
)
RECTANGULAR = BravaisLattice(
    "rectangular",
    ((F(1), F(0)), (F(0), F(4))),
    "reseau rectangulaire (a != b, angle droit)",
)
CENTERED_RECTANGULAR = BravaisLattice(
    "centered rectangular",
    ((F(4), F(0)), (F(0), F(1))),
    "reseau rectangulaire centre (cellule conventionnelle a x b, centrage (1/2, 1/2))",
)
SQUARE = BravaisLattice(
    "square",
    ((F(1), F(0)), (F(0), F(1))),
    "reseau carre (a = b, angle droit)",
)
HEXAGONAL = BravaisLattice(
    "hexagonal",
    ((F(1), F(-1, 2)), (F(-1, 2), F(1))),
    "reseau hexagonal (a = b, angle 120 degres)",
)


# --------------------------------------------------------------------------
# Groupes
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class WallpaperGroup:
    """Un groupe de symetrie du plan, par ses generateurs."""

    symbol: str
    conway: str
    lattice: BravaisLattice
    generators: tuple[Affine, ...]
    note: str


def _t(x: Fraction | int, y: Fraction | int = 0) -> Affine:
    return Affine.translation(x, y)


def _lin(a: Matrix) -> Affine:
    return Affine.linear(a)


def _gl(a: Matrix, tx: Fraction | int, ty: Fraction | int) -> Affine:
    """Un element orientation-reversing : reflection * translation."""
    return Affine(a, (F(tx), F(ty)))


# Rotations du reseau carre
_R90 = ((F(0), F(-1)), (F(1), F(0)))
_R180 = ((F(-1), F(0)), (F(0), F(-1)))
# Rotations du reseau hexagonal (base e1 = (1, 0), e2 = (-1/2, sqrt(3)/2))
_R60 = ((F(1), F(-1)), (F(1), F(0)))
_R120 = ((F(0), F(-1)), (F(1), F(-1)))
# Reflexions (parties lineaires ; la position est portee par la translation)
_MIRROR_U = ((F(1), F(0)), (F(0), F(-1)))  # axe parallele a e1
_MIRROR_V = ((F(-1), F(0)), (F(0), F(1)))  # axe parallele a e2
_MIRROR_DIAG_SQUARE = ((F(0), F(1)), (F(1), F(0)))  # axe y = x (carre)
_MIRROR_DIAG_HEX = ((F(1), F(-1)), (F(0), F(-1)))  # axe parallele a e1 (hexa)
_MIRROR_30_HEX = ((F(1), F(0)), (F(1), F(-1)))  # axe a 30 degres (hexa)
_MIRROR_VERT_HEX = ((F(-1), F(1)), (F(0), F(1)))  # axe vertical (hexa)


GROUPS: tuple[WallpaperGroup, ...] = (
    WallpaperGroup(
        "p1",
        "o",
        OBLIQUE,
        (_t(1, 0), _t(0, 1)),
        "translations seules : aucun element de symetrie orientation-reversing",
    ),
    WallpaperGroup(
        "p2",
        "2222",
        OBLIQUE,
        (_t(1, 0), _t(0, 1), _lin(_R180)),
        "translations et demi-tour",
    ),
    WallpaperGroup(
        "pm",
        "**",
        RECTANGULAR,
        (_t(1, 0), _t(0, 1), _lin(_MIRROR_V)),
        "translations et miroir (axe parallele a e2)",
    ),
    WallpaperGroup(
        "pg",
        "xx",
        RECTANGULAR,
        (_t(1, 0), _t(0, 1), _gl(_MIRROR_U, F(1, 2), 0)),
        "translations et glissade (miroir suivi d'une translation d'un demi-demaille)",
    ),
    WallpaperGroup(
        "cm",
        "*x",
        CENTERED_RECTANGULAR,
        (_t(1, 0), _t(0, 1), _t(F(1, 2), F(1, 2)), _lin(_MIRROR_V)),
        "reseau centre (cellule 2 x 1, centrage (1/2, 1/2)) et miroir",
    ),
    WallpaperGroup(
        "pmm",
        "*2222",
        RECTANGULAR,
        (_t(1, 0), _t(0, 1), _lin(_MIRROR_U), _lin(_MIRROR_V)),
        "translations et deux miroirs perpendiculaires",
    ),
    WallpaperGroup(
        "pmg",
        "22*",
        RECTANGULAR,
        (
            _t(1, 0),
            _t(0, 1),
            _lin(_MIRROR_V),
            _gl(_MIRROR_U, F(1, 2), 0),
        ),
        "miroir et glissade sur des axes perpendiculaires",
    ),
    WallpaperGroup(
        "pgg",
        "22x",
        RECTANGULAR,
        (
            _t(1, 0),
            _t(0, 1),
            _gl(_MIRROR_U, F(1, 2), 0),
            _gl(_MIRROR_V, 0, F(1, 2)),
        ),
        "deux glissades perpendiculaires, aucun miroir",
    ),
    WallpaperGroup(
        "cmm",
        "2*22",
        CENTERED_RECTANGULAR,
        (
            _t(1, 0),
            _t(0, 1),
            _t(F(1, 2), F(1, 2)),
            _lin(_MIRROR_V),
            _lin(_MIRROR_U),
        ),
        "reseau centre et deux miroirs perpendiculaires",
    ),
    WallpaperGroup(
        "p4",
        "442",
        SQUARE,
        (_t(1, 0), _t(0, 1), _lin(_R90)),
        "translations et quart de tour",
    ),
    WallpaperGroup(
        "p4m",
        "*442",
        SQUARE,
        (_t(1, 0), _t(0, 1), _lin(_R90), _lin(_MIRROR_U), _lin(_MIRROR_V)),
        "quart de tour et miroirs dans quatre directions",
    ),
    WallpaperGroup(
        "p4g",
        "4*2",
        SQUARE,
        (
            _t(1, 0),
            _t(0, 1),
            _lin(_R90),
            _gl(_MIRROR_V, F(1, 2), 0),
            _gl(_MIRROR_U, 0, F(1, 2)),
        ),
        "quart de tour, miroirs decales et glissades (dont a 45 degres)",
    ),
    WallpaperGroup(
        "p3",
        "333",
        HEXAGONAL,
        (_t(1, 0), _t(0, 1), _lin(_R120)),
        "translations et tiers de tour",
    ),
    WallpaperGroup(
        "p3m1",
        "*333",
        HEXAGONAL,
        (_t(1, 0), _t(0, 1), _lin(_R120), _lin(_MIRROR_30_HEX)),
        "tiers de tour et miroirs passant par les centres d'ordre 3",
    ),
    WallpaperGroup(
        "p31m",
        "3*3",
        HEXAGONAL,
        (_t(1, 0), _t(0, 1), _lin(_R120), _gl(_MIRROR_DIAG_HEX, F(1, 2), 1)),
        "tiers de tour et miroirs de la classe des sommets, decales de sorte "
        "qu'aucun centre d'ordre 3 ne soit sur un axe de miroir",
    ),
    WallpaperGroup(
        "p6",
        "632",
        HEXAGONAL,
        (_t(1, 0), _t(0, 1), _lin(_R60)),
        "translations et sixieme de tour",
    ),
    WallpaperGroup(
        "p6m",
        "*632",
        HEXAGONAL,
        (_t(1, 0), _t(0, 1), _lin(_R60), _lin(_MIRROR_DIAG_HEX)),
        "sixieme de tour et six directions de miroir",
    ),
)

GROUPS_BY_SYMBOL = {group.symbol: group for group in GROUPS}


# --------------------------------------------------------------------------
# Reseau de translation
# --------------------------------------------------------------------------


def _lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def _integer_basis(vectors: Sequence[Vector]) -> tuple[Vector, Vector] | None:
    """Base d'un sous-reseau rationnel de rang 2.

    Les generateurs sont rationnels : on les met a l'echelle entiere, puis on
    calcule une base triangulaire (forme de Hermite) par un algorithme
    d'Euclide sur les coordonnees.
    """
    usable = [v for v in vectors if v != (F(0), F(0))]
    if not usable:
        return None
    denominator = 1
    for v in usable:
        for coordinate in v:
            denominator = _lcm(denominator, coordinate.denominator)
    ints = [(int(v[0] * denominator), int(v[1] * denominator)) for v in usable]

    # gcd des premieres coordonnees, avec suivi des combinaisons.
    gx = 0
    ax = (0, 0)
    for x, y in ints:
        if x == 0:
            continue
        new_g, new_u, new_v = _extended_gcd(gx, x)
        # g = u * gx_precedent + v * x : la combinaison qui porte g est
        # u * (combinaison precedente) + v * (x, y).
        ax = (
            new_u * ax[0] + new_v * x,
            new_u * ax[1] + new_v * y,
        )
        gx = new_g
    if gx == 0:
        return None

    # On force la premiere coordonnee des generateurs restants a zero.
    rest = []
    for x, y in ints:
        if x % gx == 0:
            rest.append((0, y - (x // gx) * ax[1]))
    gy = 0
    for _, y in rest:
        gy = gcd(gy, abs(y))
    if gy == 0:
        return None

    # Base triangulaire : (gx, s) et (0, gy).
    s = ax[1] % gy
    v1 = (F(gx), F(s))
    v2 = (F(0), F(gy))
    scale = F(1, denominator)
    return (v1[0] * scale, v1[1] * scale), (v2[0] * scale, v2[1] * scale)


def _extended_gcd(a: int, b: int) -> tuple[int, int, int]:
    """PGCD et coefficients de Bezout : ``(g, u, v)`` avec ``g = u*a + v*b``."""
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    return old_r, old_s, old_t


def _reduce_basis(v1: Vector, v2: Vector, metric: Matrix) -> tuple[Vector, Vector]:
    """Reduction de Gauss d'une base (vecteurs les plus courts).

    Le multiplicateur est un **entier** : soustraire une fraction de v1
    changerait le sous-reseau engendre, et la base reduite ne decrirait plus
    le reseau du groupe.
    """
    for _ in range(64):
        if _norm2(v2, metric) < _norm2(v1, metric):
            v1, v2 = v2, v1
        ratio = _dot(v1, v2, metric) / _norm2(v1, metric)
        mu = _round_half(ratio)
        if mu == 0:
            break
        v2 = vec_sub(v2, _scale(v1, F(mu)))
    return v1, v2


def _scale(v: Vector, k: Fraction) -> Vector:
    return (v[0] * k, v[1] * k)


def _dot(u: Vector, v: Vector, metric: Matrix) -> Fraction:
    return (
        metric[0][0] * u[0] * v[0]
        + metric[0][1] * (u[0] * v[1] + u[1] * v[0])
        + metric[1][1] * u[1] * v[1]
    )


def _norm2(v: Vector, metric: Matrix) -> Fraction:
    return _dot(v, v, metric)


def _cross(u: Vector, v: Vector) -> Fraction:
    return u[0] * v[1] - u[1] * v[0]


def _round_half(value: Fraction) -> int:
    """Entier le plus proche (moitie egale arrondie vers le haut)."""
    return int((value + F(1, 2)).__floor__())


def _lattice_coordinates(
    point: Vector, basis: tuple[Vector, Vector]
) -> tuple[Fraction, Fraction]:
    """Coordonnees d'un point dans la base du reseau (rationnelles)."""
    (b1, b2) = basis
    det = b1[0] * b2[1] - b1[1] * b2[0]
    if det == 0:
        raise ValueError("base degeneree")
    x = (point[0] * b2[1] - point[1] * b2[0]) / det
    y = (b1[0] * point[1] - b1[1] * point[0]) / det
    return (x, y)


def _reduce_mod_lattice(point: Vector, basis: tuple[Vector, Vector]) -> Vector:
    """Representant canonique d'un point modulo le reseau de translation.

    Les coefficients de base sont ramenes dans ]-1/2, 1/2] : le point
    ramene est le representant du coset modulo le reseau.
    """
    (x, y) = _lattice_coordinates(point, basis)
    m = _round_half(x)
    n = _round_half(y)
    return (
        point[0] - m * basis[0][0] - n * basis[1][0],
        point[1] - m * basis[0][1] - n * basis[1][1],
    )


def _in_lattice(vector: Vector, basis: tuple[Vector, Vector]) -> bool:
    """Le vecteur appartient-il au reseau engendre par ``basis`` ?"""
    (x, y) = _lattice_coordinates(vector, basis)
    return x.denominator == 1 and y.denominator == 1


# --------------------------------------------------------------------------
# Groupe ponctuel et elements
# --------------------------------------------------------------------------


def point_group(group: WallpaperGroup) -> tuple[Matrix, ...]:
    """Les parties lineaires des elements du groupe (le groupe ponctuel)."""
    seen: dict[Matrix, None] = {}
    frontier = [identity_matrix()]
    seen[identity_matrix()] = None
    for _ in range(12):
        new_frontier = []
        for current in frontier:
            for generator in group.generators:
                candidate = mat_mul(generator.matrix, current)
                if candidate not in seen:
                    seen[candidate] = None
                    new_frontier.append(candidate)
        if not new_frontier:
            break
        frontier = new_frontier
    return tuple(seen)


def _representatives(group: WallpaperGroup) -> dict[Matrix, Affine]:
    """Un representant (partie lineaire, translation) par element du groupe ponctuel."""
    identity = identity_matrix()
    found: dict[Matrix, Affine] = {identity: Affine.identity()}
    frontier = [Affine.identity()]
    for _ in range(16):
        new_frontier = []
        for current in frontier:
            for generator in group.generators:
                candidate = generator.compose(current)
                if candidate.matrix not in found:
                    found[candidate.matrix] = candidate
                    new_frontier.append(candidate)
        if not new_frontier:
            break
        frontier = new_frontier
    return found


def translation_lattice(group: WallpaperGroup) -> tuple[Vector, Vector]:
    """Base du sous-groupe des translations (le reseau de translation).

    Le reseau est engendre par les translations pures du groupe, qu'on obtient
    a partir des generateurs : pour chaque element ``(A, t_A)``, la
    composante ``t_A + A . t_{A^{-1}}`` est une translation pure.
    """
    representatives = _representatives(group)
    generators: list[Vector] = []
    for generator in group.generators:
        if generator.is_pure_translation:
            generators.append(generator.translation)
    for matrix, element in representatives.items():
        inverse = representatives.get(mat_inv(matrix))
        if inverse is None:
            continue
        generators.append(
            vec_add(element.translation, mat_vec(matrix, inverse.translation))
        )
    basis = _integer_basis(generators)
    if basis is None:
        raise ValueError(f"le groupe {group.symbol} n'a pas de reseau de translation")
    return _reduce_basis(basis[0], basis[1], group.lattice.metric)


def _matrix_order(matrix: Matrix) -> int:
    """Ordre d'une matrice 2x2 (borne a 12)."""
    current = identity_matrix()
    for order in range(1, 13):
        current = mat_mul(matrix, current)
        if current == identity_matrix():
            return order
    return 0


# --------------------------------------------------------------------------
# Directions, lignes, centres
# --------------------------------------------------------------------------


def _eigen_direction(matrix: Matrix, eigenvalue: Fraction) -> Vector:
    """Vecteur propre d'une matrice 2x2 pour la valeur propre donnee.

    Les quatre cas sont traites separement : une matrice triangulaire
    superieure a `q = 0` a pour vecteur propre `(lambda - s, r)`, et non
    `(s - lambda, 0)` -- perdre `r` donne un axe faux (les miroirs a 30 et 60
    degres du reseau hexagonal ont justement `q = 0`).
    """
    (p, q), (r, s) = matrix
    if q != 0:
        return (q, eigenvalue - p)
    if r != 0:
        return (eigenvalue - s, r)
    if p == eigenvalue:
        return (F(1), F(0))
    if s == eigenvalue:
        return (F(0), F(1))
    # Matrice scalaire : toute direction convient.
    return (F(1), F(0))


def _primitive_direction(vector: Vector) -> Vector:
    """Version canonique d'une direction rationnelle.

    Le vecteur est mis a l'echelle entiere, divise par son PGCD, et oriente
    de facon a ce que sa premiere composante non nulle soit positive : deux
    vecteurs colineaires ont alors la meme forme canonique.
    """
    denominator = 1
    for coordinate in vector:
        denominator = _lcm(denominator, coordinate.denominator)
    ints = [int(coordinate * denominator) for coordinate in vector]
    divisor = 0
    for value in ints:
        divisor = gcd(divisor, abs(value))
    if divisor == 0:
        return (F(0), F(0))
    ints = [value // divisor for value in ints]
    if ints[0] < 0 or (ints[0] == 0 and ints[1] < 0):
        ints = [-value for value in ints]
    return (F(ints[0]), F(ints[1]))


def _layer_step(
    basis: tuple[Vector, Vector], normal: Vector, metric: Matrix
) -> Fraction:
    """Epaisseur du reseau dans la direction normale a ``normal``.

    Valeur de ``lambda . normal`` sur le reseau : c'est un sous-groupe
    cyclique ``delta . Z``, de pas ``delta`` calcule comme le PGCD des
    valeurs prises sur la base.
    """
    values = [_dot(vector, normal, metric) for vector in basis]
    step = F(0)
    for value in values:
        step = _fraction_gcd(step, value)
    if step == 0:
        raise ValueError("direction normale invalide")
    return abs(step)


def _fraction_gcd(a: Fraction, b: Fraction) -> Fraction:
    """PGCD de deux rationnels (positif)."""
    if a == 0:
        return abs(b)
    if b == 0:
        return abs(a)
    denominator = _lcm(a.denominator, b.denominator)
    x = abs(int(a * denominator))
    y = abs(int(b * denominator))
    return F(gcd(x, y), denominator)


def _normalize_offset(offset: Fraction, step: Fraction) -> Fraction:
    """Normalise un decalage de ligne modulo l'epaisseur du reseau.

    Deux lignes **paralleles** de meme famille sont la meme ligne si et
    seulement si leurs decalages different d'une **translation du reseau** :
    le pas est donc le pas du reseau dans la direction normale, et non sa
    moitie. Ecraser modulo la moitie confondrait deux lignes distinctes
    (le miroir et l'axe de glissade de `cm`, par exemple).
    """
    if step == 0:
        raise ValueError("pas de reseau nul")
    return offset % step


@dataclass(frozen=True)
class _Line:
    """Une droite du plan : une direction et un decalage normalise."""

    direction: Vector
    normal: Vector
    offset: Fraction

    def key(self) -> tuple:
        return (self.direction, self.offset)


def _lines_of(group: WallpaperGroup) -> tuple[list[_Line], list[_Line]]:
    """Les lignes de miroir et les axes de glissade du groupe.

    Pour chaque partie lineaire orientation-reversing ``A``, les elements du
    coset sont ``(A, t_A + lambda)``. Un element est un **miroir** si sa
    composante le long de l'axe est nulle ; sinon c'est une **glissade**, dont
    l'axe est la droite parallele a celle du miroir mais decalee.
    """
    metric = group.lattice.metric
    lattice = translation_lattice(group)
    mirrors: dict[tuple, _Line] = {}
    glides: dict[tuple, _Line] = {}
    for matrix, element in _representatives(group).items():
        if mat_det(matrix) >= 0:
            continue
        axis = _primitive_direction(_eigen_direction(matrix, F(1)))
        normal = _primitive_direction(_eigen_direction(matrix, F(-1)))
        step = _layer_step(lattice, normal, metric)
        for i in range(-6, 7):
            for j in range(-6, 7):
                shift = (
                    i * lattice[0][0] + j * lattice[1][0],
                    i * lattice[0][1] + j * lattice[1][1],
                )
                translation = vec_add(element.translation, shift)
                along = _dot(translation, axis, metric)
                offset = _dot(translation, normal, metric) / 2
                line = _Line(axis, normal, _normalize_offset(offset, step))
                if along == 0:
                    mirrors.setdefault(line.key(), line)
                else:
                    glides.setdefault(line.key(), line)
    mirror_lines = list(mirrors.values())
    glide_lines = [line for line in glides.values() if line.key() not in mirrors]
    return mirror_lines, glide_lines


def _mirror_directions(group: WallpaperGroup) -> int:
    """Nombre de directions de miroir (une droite et son opposee : une)."""
    mirror_lines, _ = _lines_of(group)
    return len({line.direction for line in mirror_lines})


def _mirror_lines_count(group: WallpaperGroup) -> int:
    mirror_lines, _ = _lines_of(group)
    return len(mirror_lines)


def _glide_axes_count(group: WallpaperGroup) -> int:
    """Nombre d'axes de glissade distincts d'une ligne de miroir."""
    _, glide_lines = _lines_of(group)
    return len(glide_lines)


def _glide_directions(group: WallpaperGroup) -> int:
    """Nombre de directions d'axes de glissade (une droite et son opposee : une)."""
    _, glide_lines = _lines_of(group)
    return len({line.direction for line in glide_lines})


def _rotation_centers(group: WallpaperGroup) -> list[tuple[Vector, int]]:
    """Les centres de rotation du groupe, avec leur ordre maximal.

    Un centre est un point fixe d'un element de rotation. Pour chaque partie
    lineaire ``A`` d'ordre > 1, le coset ``(A, t_A + lambda)`` a pour point
    fixe ``(I - A)^{-1} (t_A + lambda)`` ; on enumere les centres distincts
    modulo le reseau, puis on attribue a chacun l'**ordre maximal** des
    rotations qui le fixent.
    """
    metric = group.lattice.metric
    lattice = translation_lattice(group)
    representatives = _representatives(group)
    identity = identity_matrix()
    candidates: set[Vector] = set()
    for matrix, element in representatives.items():
        if matrix == identity or mat_det(matrix) <= 0:
            continue
        for i in range(-6, 7):
            for j in range(-6, 7):
                shift = (
                    i * lattice[0][0] + j * lattice[1][0],
                    i * lattice[0][1] + j * lattice[1][1],
                )
                center = _solve_fixed_point(matrix, vec_add(element.translation, shift))
                if center is None:
                    continue
                candidates.add(_reduce_mod_lattice(center, lattice))
    result: list[tuple[Vector, int]] = []
    for center in sorted(candidates):
        best = 1
        for matrix, element in representatives.items():
            if matrix == identity or mat_det(matrix) <= 0:
                continue
            order = _matrix_order(matrix)
            if order <= best:
                continue
            if not _in_lattice(
                vec_sub(_apply_inverse_minus(matrix, center), element.translation),
                lattice,
            ):
                continue
            best = order
        result.append((center, best))
    return result


def _apply_inverse_minus(matrix: Matrix, point: Vector) -> Vector:
    """``(I - A) . point``."""
    (p, q), (r, s) = matrix
    return (
        (F(1) - p) * point[0] - q * point[1],
        -r * point[0] + (F(1) - s) * point[1],
    )


def _solve_fixed_point(matrix: Matrix, translation: Vector) -> Vector | None:
    """Point fixe de ``x -> A x + t`` (resolu exactement) ou None."""
    (p, q), (r, s) = matrix
    a = F(1) - p
    b = -q
    c = -r
    d = F(1) - s
    determinant = a * d - b * c
    if determinant == 0:
        return None
    x = (translation[0] * d - b * translation[1]) / determinant
    y = (a * translation[1] - translation[0] * c) / determinant
    return (x, y)


def _center_on_mirror(
    center: Vector,
    group: WallpaperGroup,
    lattice: tuple[Vector, Vector],
) -> bool:
    """Le centre est-il situe sur une ligne de miroir ?

    Test algebrique exact, sans comparaison d'offsets : un centre est sur un
    miroir si et seulement si un element orientation-reversing du groupe le
    **fixe**. L'element ``(A, t_A + lambda)`` fixe le centre ``c`` exactement
    quand ``(I - A) c - t_A`` appartient au reseau de translation -- et un
    element orientation-reversing qui a un point fixe est un miroir (une
    glissade n'en a pas).
    """
    for matrix, element in _representatives(group).items():
        if mat_det(matrix) >= 0:
            continue
        value = _apply_inverse_minus(matrix, center)
        if _in_lattice(vec_sub(value, element.translation), lattice):
            return True
    return False


def _center_on_glide_axis(
    center: Vector,
    group: WallpaperGroup,
    lattice: tuple[Vector, Vector],
) -> bool:
    """Le centre est-il situe sur un axe de glissade ?

    Une glissade ``(A, t)`` laisse invariant l'axe
    ``{x : dot(x, n) = dot(t, n) / 2}``, ou ``n`` est la direction propre de
    ``A`` pour la valeur ``-1`` : c'est l'axe de la glissade. On balaie les
    elements du coset ``(A, t_A + lambda)`` et on retient ceux dont la
    composante le long de l'axe est non nulle (une glissade, pas un miroir).
    """
    metric = group.lattice.metric
    for matrix, element in _representatives(group).items():
        if mat_det(matrix) >= 0:
            continue
        axis = _primitive_direction(_eigen_direction(matrix, F(1)))
        normal = _primitive_direction(_eigen_direction(matrix, F(-1)))
        for i in range(-6, 7):
            for j in range(-6, 7):
                shift = (
                    i * lattice[0][0] + j * lattice[1][0],
                    i * lattice[0][1] + j * lattice[1][1],
                )
                translation = vec_add(element.translation, shift)
                if _dot(translation, axis, metric) == 0:
                    continue
                if (
                    _dot(center, normal, metric)
                    == _dot(translation, normal, metric) / 2
                ):
                    return True
    return False


# --------------------------------------------------------------------------
# Attributs derives
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class WallpaperAttributes:
    """Attributs d'un groupe de symetrie du plan, derives de ses generateurs."""

    symbol: str
    conway: str
    lattice: str
    point_group_order: int
    rotation_orders: tuple[int, ...]
    mirror_directions: int
    mirror_lines: int
    glide_axes: int
    glide_directions: int
    centers_by_order: tuple[tuple[int, int], ...]
    centers_off_mirrors: int
    centers_on_glide_axes: int
    total_centers: int


def classify_lattice(basis: tuple[Vector, Vector], metric: Matrix) -> str:
    """Type de reseau de Bravais, deduit de la base reduite et de la metrique.

    - base orthogonale, carres egaux -> carre ;
    - base orthogonale, carres differents -> rectangulaire ;
    - losange equilateral, angle 60/120 -> hexagonal ;
    - losange equilateral, autre angle -> rectangulaire centre ;
    - sinon -> oblique.

    Le rectangulaire centre n'a pas de base orthogonale **primitive** quand la
    cellule conventionnelle n'est pas carree : sa base reduite n'est pas un
    losange. On le reconnait donc a l'existence d'une base orthogonale de
    **double** pave (cellule conventionnelle) dont le centre `(u + v) / 2` est
    lui-meme un point du reseau.
    """
    (v1, v2) = basis
    n1 = _norm2(v1, metric)
    n2 = _norm2(v2, metric)
    dot = _dot(v1, v2, metric)
    if dot == 0:
        return "square" if n1 == n2 else "rectangular"
    if n1 == n2 and abs(dot) * 2 == n1:
        return "hexagonal"
    area = abs(v1[0] * v2[1] - v1[1] * v2[0])
    if area == 0:
        return "oblique"
    bound = 4 * max(n1, n2)
    candidates = []
    for m in range(-4, 5):
        for n in range(-4, 5):
            candidate = vec_add(_scale(v1, F(m)), _scale(v2, F(n)))
            if candidate != (F(0), F(0)) and _norm2(candidate, metric) <= bound:
                candidates.append(candidate)
    for u in candidates:
        for v in candidates:
            if _dot(u, v, metric) != 0:
                continue
            if _norm2(u, metric) == _norm2(v, metric):
                continue
            ratio = abs(u[0] * v[1] - u[1] * v[0]) / area
            if ratio == 1:
                return "rectangular"
            if ratio == 2 and _in_lattice(
                ((u[0] + v[0]) / 2, (u[1] + v[1]) / 2), basis
            ):
                return "centered rectangular"
    return "oblique"


def attributes(group: WallpaperGroup) -> WallpaperAttributes:
    """Derive les attributs de classification d'un groupe."""
    metric = group.lattice.metric
    lattice_basis = translation_lattice(group)
    lattice_name = classify_lattice(lattice_basis, metric)
    matrices = point_group(group)
    orders = sorted(
        {
            _matrix_order(m)
            for m in matrices
            if m != identity_matrix() and mat_det(m) > 0
        }
    )
    mirror_lines, _ = _lines_of(group)
    centers = _rotation_centers(group)
    counts: dict[int, int] = {}
    for _, order in centers:
        counts[order] = counts.get(order, 0) + 1
    off_mirrors = sum(
        1
        for (center, _) in centers
        if not _center_on_mirror(center, group, lattice_basis)
    )
    on_glide_axes = sum(
        1
        for (center, _) in centers
        if _center_on_glide_axis(center, group, lattice_basis)
    )
    return WallpaperAttributes(
        symbol=group.symbol,
        conway=group.conway,
        lattice=lattice_name,
        point_group_order=len(matrices),
        rotation_orders=tuple(orders),
        mirror_directions=len({line.direction for line in mirror_lines}),
        mirror_lines=len(mirror_lines),
        glide_axes=_glide_axes_count(group),
        glide_directions=_glide_directions(group),
        centers_by_order=tuple(sorted(counts.items())),
        centers_off_mirrors=off_mirrors,
        centers_on_glide_axes=on_glide_axes,
        total_centers=len(centers),
    )


# --------------------------------------------------------------------------
# Rendu
# --------------------------------------------------------------------------


def render_svg(
    group: WallpaperGroup,
    cells: int = 4,
    size: int = 640,
    color: str = "#1f4e79",
    background: str = "#ffffff",
) -> str:
    """Rend le motif du groupe, par l'orbite d'un motif asymetrique.

    Chaque element du groupe est ``(A, t_A + lambda)`` avec ``lambda`` dans le
    reseau de translation : le rendu couvre ainsi **tous** les elements dont la
    translation tombe dans la fenetre, pas un echantillon.

    La geometrie est calculee en coordonnees cartesiennes, puis **mise a
    l'echelle et centree** dans la toile : le ``viewBox`` vaut ``size`` pixels
    alors que les coordonnees du motif sont de l'ordre de l'unite, si bien
    qu'un rendu non normalise serait un point invisible dans un coin.
    L'axe vertical est inverse (SVG croît vers le bas, la carte vers le haut).
    """
    lattice_basis = translation_lattice(group)
    representatives = _representatives(group)
    (e1, e2) = group.lattice.cartesian_basis()

    motif = ((F(1, 5), F(1, 4)), (F(3, 5), F(2, 5)), (F(1, 4), F(3, 4)))
    dot = (F(7, 10), F(7, 10))

    def affine_to_cartesian(matrix: Matrix, translation: Vector):
        # M = [[e1 e2]] ; la transformation cartesienne vaut M A M^-1.
        m = ((e1[0], e2[0]), (e1[1], e2[1]))
        det = m[0][0] * m[1][1] - m[0][1] * m[1][0]
        inverse = ((m[1][1] / det, -m[0][1] / det), (-m[1][0] / det, m[0][0] / det))
        linear = _mat_mul_float(_mat_mul_float(m, matrix), inverse)
        offset = (
            m[0][0] * float(translation[0]) + m[0][1] * float(translation[1]),
            m[1][0] * float(translation[0]) + m[1][1] * float(translation[1]),
        )
        return linear, offset

    polygones: list[list[tuple[float, float]]] = []
    pastilles: list[tuple[float, float]] = []
    half = cells // 2
    for matrix, element in sorted(
        representatives.items(), key=lambda item: str(item[0])
    ):
        linear, offset = affine_to_cartesian(matrix, element.translation)
        for i in range(-half, cells - half + 1):
            for j in range(-half, cells - half + 1):
                shift = (
                    i * lattice_basis[0][0] + j * lattice_basis[1][0],
                    i * lattice_basis[0][1] + j * lattice_basis[1][1],
                )
                points = []
                for vertex in motif:
                    x, y = vertex
                    px = linear[0][0] * float(x) + linear[0][1] * float(y) + offset[0]
                    py = linear[1][0] * float(x) + linear[1][1] * float(y) + offset[1]
                    points.append(
                        (
                            px + float(shift[0]) * e1[0] + float(shift[1]) * e2[0],
                            py + float(shift[0]) * e1[1] + float(shift[1]) * e2[1],
                        )
                    )
                polygones.append(points)
                dx, dy = float(dot[0]), float(dot[1])
                cx = linear[0][0] * dx + linear[0][1] * dy + offset[0]
                cy = linear[1][0] * dx + linear[1][1] * dy + offset[1]
                cx += float(shift[0]) * e1[0] + float(shift[1]) * e2[0]
                cy += float(shift[0]) * e1[1] + float(shift[1]) * e2[1]
                pastilles.append((cx, cy))

    # Mise a l'echelle : le motif est exprime en unites du reseau, la toile
    # en pixels. Sans cette normalisation, les coordonnees tombent dans un
    # carre de quelques unites pres de l'origine et le rendu est invisible.
    toutes_x = [p[0] for poly in polygones for p in poly] + [c[0] for c in pastilles]
    toutes_y = [p[1] for poly in polygones for p in poly] + [c[1] for c in pastilles]
    if not toutes_x:
        return (
            f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {size} {size}" '
            f'width="{size}" height="{size}">'
            f'<rect width="{size}" height="{size}" fill="{background}"/>'
            f"</svg>"
        )
    xmin, xmax = min(toutes_x), max(toutes_x)
    ymin, ymax = min(toutes_y), max(toutes_y)
    largeur = max(xmax - xmin, 1e-9)
    hauteur = max(ymax - ymin, 1e-9)
    marge = size * 0.06
    echelle = (size - 2 * marge) / max(largeur, hauteur)
    centre_x = (xmin + xmax) / 2
    centre_y = (ymin + ymax) / 2

    def vers_canvas(point: tuple[float, float]) -> tuple[float, float]:
        return (
            size / 2 + (point[0] - centre_x) * echelle,
            size / 2 - (point[1] - centre_y) * echelle,
        )

    rayon = max(1.0, size * 0.008)
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {size} {size}" width="{size}" height="{size}">',
        f'<rect width="{size}" height="{size}" fill="{background}"/>',
        f'<g fill="none" stroke="{color}" stroke-width="1.1" stroke-linejoin="round">',
    ]
    for points in polygones:
        polygon = " ".join(
            f"{x:.3f},{y:.3f}" for (x, y) in (vers_canvas(p) for p in points)
        )
        parts.append(f'<polygon points="{polygon}"/>')
    for centre in pastilles:
        cx, cy = vers_canvas(centre)
        parts.append(
            f'<circle cx="{cx:.3f}" cy="{cy:.3f}" r="{rayon:.3f}" fill="{color}" stroke="none"/>'
        )
    parts.append("</g>")
    parts.append("</svg>")
    return "\n".join(parts)


def _mat_mul_float(a, b):
    return (
        (
            a[0][0] * b[0][0] + a[0][1] * b[1][0],
            a[0][0] * b[0][1] + a[0][1] * b[1][1],
        ),
        (
            a[1][0] * b[0][0] + a[1][1] * b[1][0],
            a[1][0] * b[0][1] + a[1][1] * b[1][1],
        ),
    )
