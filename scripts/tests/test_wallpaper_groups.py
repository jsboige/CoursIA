"""Tests des 17 groupes de symetrie du plan (`scripts/symmetry`).

Reference
---------
Les valeurs attendues proviennent de la page « Wallpaper group » de
Wikipedia, **archivee dans le gisement partage** :

    G:\\Mon Drive\\MyIA\\IA\\Bibliographie IA\\GroupTheory\\
        2026 - Wikipedia - Wallpaper group.html
        sha256 e474cdb659ee888f65c872040caa852dc45db3a81a3071a0dd27acb48cc84a49

Les citations verbatim sont reprises dans les commentaires de chaque test.
Les pages « Orbifold notation » et « List of planar symmetry groups »,
archivees dans le meme rayon, ont servi a verifier les signatures de Conway
et les notations IUC.

Conventions de comptage
-----------------------
* les centres de rotation sont comptes **par cellule primitive** : le
  centre de plus haut ordre en un point donne est le seul compte ;
* les directions sont comptees modulo le signe (une droite et son opposee
  font une direction) ;
* les « axes de glissade » sont les lignes portant une glissade et **ne**
  portant pas de miroir : une glissade dont l'axe coincide avec une ligne de
  miroir n'est pas un axe de glissade distinct.

La reference compte parfois les centres secondaires par **cellule
illustree** et non par cellule primitive (p4 : « one rotation centre of
order two » la ou la cellule primitive en porte deux) : les tests
n'affirment donc le nombre de centres que la reference enonce sans
ambiguite, et les autres proprietes sont verifiees par leur formule
qualitative (« the centres of rotation are not located on the glide
reflection axes »...).
"""

import re
from fractions import Fraction

import pytest
from symmetry import wallpaper as W
from symmetry.affine import Affine, identity_matrix, mat_det, mat_inv, mat_mul, mat_vec

# (reseau de Bravais, ordre du groupe ponctuel, directions de miroir,
#  directions de glissade)
EXPECTED_INVARIANTS = {
    # « The group p 1 contains only translations; there are no rotations,
    #  reflections, or glide reflections. »
    "p1": ("oblique", 1, 0, 0),
    # « The group p 2 contains four rotation centres of order two (180deg),
    #  but no reflections or glide reflections. »
    "p2": ("oblique", 2, 0, 0),
    # « The group pm has no rotations. It has reflection axes, they are all
    #  parallel. »
    "pm": ("rectangular", 2, 1, 0),
    # « The group pg contains glide reflections only, and their axes are all
    #  parallel. There are no rotations or reflections. »
    "pg": ("rectangular", 2, 0, 1),
    # « The group cm contains no rotations. It has reflection axes, all
    #  parallel. There is at least one glide reflection whose axis is not a
    #  reflection axis; it is halfway between two adjacent parallel
    #  reflection axes. »
    "cm": ("centered rectangular", 2, 1, 1),
    # « The group pmm has reflections in two perpendicular directions, and
    #  four rotation centres of order two (180deg) located at the
    #  intersections of the reflection axes. »
    "pmm": ("rectangular", 4, 2, 0),
    # « The group pmg has two rotation centres of order two (180deg), and
    #  reflections in only one direction. It has glide reflections whose
    #  axes are perpendicular to the reflection axes. The centres of rotation
    #  all lie on glide reflection axes. »
    "pmg": ("rectangular", 4, 1, 1),
    # « The group pgg contains two rotation centres of order two (180deg),
    #  and glide reflections in two perpendicular directions. The centres of
    #  rotation are not located on the glide reflection axes. There are no
    #  reflections. »
    "pgg": ("rectangular", 4, 0, 2),
    # « The group cmm has reflections in two perpendicular directions, and a
    #  rotation of order two (180deg) whose centre is not on a reflection
    #  axis. It also has two rotations whose centres are on a reflection
    #  axis. »
    "cmm": ("centered rectangular", 4, 2, 2),
    # « The group p 4 has two rotation centres of order four (90deg) ...
    #  It has no reflections or glide reflections. »
    "p4": ("square", 4, 0, 0),
    # « The group p 4 m has two rotation centres of order four (90deg), and
    #  reflections in four distinct directions (horizontal, vertical, and
    #  diagonals). ... All rotation centres lie on reflection axes. »
    "p4m": ("square", 8, 4, 2),
    # « The group p 4 g has two centres of rotation of order four (90deg) ...
    #  but it has reflections in only two directions, which are
    #  perpendicular. There are rotations of order two (180deg) whose centres
    #  are located at the intersections of reflection axes. It has glide
    #  reflections axes parallel to the reflection axes, in between them,
    #  and also at an angle of 45deg with these. »
    "p4g": ("square", 8, 2, 4),
    # « The group p 3 has three different rotation centres of order three
    #  (120deg), but no reflections or glide reflections. »
    "p3": ("hexagonal", 3, 0, 0),
    # « The group p 3 m 1 has three different rotation centres of order three
    #  (120deg). It has reflections in the three sides of an equilateral
    #  triangle. The centre of every rotation lies on a reflection axis. »
    "p3m1": ("hexagonal", 6, 3, 3),
    # « The group p 31 m has three different rotation centres of order three
    #  (120deg) ... It has reflections in three distinct directions. It has
    #  at least one rotation whose centre does not lie on a reflection axis. »
    "p31m": ("hexagonal", 6, 3, 3),
    # « The group p 6 has one rotation centre of order six (60deg); two
    #  rotation centres of order three (120deg) ... and three rotation
    #  centres of order two (180deg) ... It has no reflections or glide
    #  reflections. »
    "p6": ("hexagonal", 6, 0, 0),
    # « The group p 6 m has one rotation centre of order six (60deg); it has
    #  two rotation centres of order three ... and three of order two ...
    #  It has also reflections in six distinct directions. »
    "p6m": ("hexagonal", 12, 6, 6),
}

# Nombre de centres de l'ordre **principal** (le plus grand ordre present),
# par cellule primitive : la reference enonce ce nombre sans ambiguite pour
# ces groupes-la.
EXPECTED_PRIMARY_CENTERS = {
    "p1": None,
    "p2": 4,
    "pm": None,
    "pg": None,
    "cm": None,
    "pmm": 4,
    # pmg et pgg : la reference compte les centres secondaires par cellule
    # illustree (« two rotation centres of order two ») : le compte par
    # cellule primitive n'est pas affirme.
    "pmg": None,
    "pgg": None,
    "cmm": None,
    "p4": 2,
    "p4m": 2,
    "p4g": 2,
    "p3": 3,
    "p3m1": 3,
    "p31m": 3,
    "p6": 1,
    "p6m": 1,
}


def _attributes(symbol):
    return W.attributes(W.GROUPS_BY_SYMBOL[symbol])


@pytest.mark.parametrize("symbol", sorted(EXPECTED_INVARIANTS))
def test_invariants_conformes_a_la_reference(symbol):
    """Reseau, groupe ponctuel, directions de miroir et de glissade."""
    lattice, point_order, mirror_directions, glide_directions = EXPECTED_INVARIANTS[
        symbol
    ]
    attr = _attributes(symbol)
    assert attr.lattice == lattice
    assert attr.point_group_order == point_order
    assert attr.mirror_directions == mirror_directions
    assert attr.glide_directions == glide_directions


@pytest.mark.parametrize("symbol", sorted(EXPECTED_PRIMARY_CENTERS))
def test_centres_principaux(symbol):
    """Nombre de centres de rotation du plus grand ordre present."""
    expected = EXPECTED_PRIMARY_CENTERS[symbol]
    attr = _attributes(symbol)
    if expected is None:
        # Groupe sans compte non ambigu dans la reference (pmg, pgg, cmm) :
        # seules les proprietes qualitatives sont affirmees ailleurs.
        return
    assert attr.centers_by_order
    highest = max(order for order, _ in attr.centers_by_order)
    count = dict(attr.centers_by_order)[highest]
    assert count == expected


def test_p2_et_p6_et_p6m_detail_entier():
    """Groupes dont la reference donne tous les comptes de centres."""
    assert _attributes("p2").centers_by_order == ((2, 4),)
    assert _attributes("p6").centers_by_order == ((2, 3), (3, 2), (6, 1))
    assert _attributes("p6m").centers_by_order == ((2, 3), (3, 2), (6, 1))


def test_pmm_centres_sur_les_axes_de_miroir():
    """« four rotation centres of order two ... at the intersections of the
    reflection axes » : aucun centre hors miroir."""
    attr = _attributes("pmm")
    assert attr.centers_off_mirrors == 0
    assert attr.total_centers == 4


def test_cmm_un_centre_hors_miroir_et_deux_sur_miroir():
    """« a rotation of order two whose centre is not on a reflection axis.
    It also has two rotations whose centres are on a reflection axis »."""
    attr = _attributes("cmm")
    assert attr.centers_off_mirrors >= 1
    assert attr.total_centers - attr.centers_off_mirrors >= 2


def test_p4m_tous_les_centres_sur_les_miroirs():
    """« All rotation centres lie on reflection axes. »"""
    attr = _attributes("p4m")
    assert attr.centers_off_mirrors == 0


def test_p4g_centres_d_ordre_4_hors_miroirs_et_d_ordre_2_sur_miroirs():
    """« two centres of rotation of order four » hors des axes, « rotations of
    order two whose centres are located at the intersections of reflection
    axes » sur les axes."""
    group = W.GROUPS_BY_SYMBOL["p4g"]
    lattice = W.translation_lattice(group)
    centers = W._rotation_centers(group)
    off = {
        order
        for (center, order) in centers
        if not W._center_on_mirror(center, group, lattice)
    }
    assert off == {4}
    assert sum(1 for _ in centers) == 4


def test_p3m1_tous_les_centres_sur_les_miroirs():
    """« The centre of every rotation lies on a reflection axis. »"""
    assert _attributes("p3m1").centers_off_mirrors == 0


def test_p31m_au_moins_un_centre_hors_miroir():
    """« It has at least one rotation whose centre does not lie on a
    reflection axis. »"""
    assert _attributes("p31m").centers_off_mirrors >= 1


def test_pmg_centres_sur_les_axes_de_glissade():
    """« The centres of rotation all lie on glide reflection axes. »"""
    attr = _attributes("pmg")
    assert attr.centers_on_glide_axes == attr.total_centers


def test_pgg_centres_hors_des_axes_de_glissade():
    """« The centres of rotation are not located on the glide reflection
    axes. »"""
    attr = _attributes("pgg")
    assert attr.centers_on_glide_axes == 0


def test_pmg_les_axe_de_glissade_sont_perpendiculaires_au_miroir():
    """« It has glide reflections whose axes are perpendicular to the
    reflection axes. »"""
    group = W.GROUPS_BY_SYMBOL["pmg"]
    metric = group.lattice.metric
    mirrors, glides = W._lines_of(group)
    assert len({line.direction for line in mirrors}) == 1
    assert len({line.direction for line in glides}) == 1
    mirror_direction = next(iter({line.direction for line in mirrors}))
    glide_direction = next(iter({line.direction for line in glides}))
    assert W._dot(mirror_direction, glide_direction, metric) == 0


def test_pgg_les_axes_de_glissade_sont_perpendiculaires():
    """« glide reflections in two perpendicular directions »."""
    group = W.GROUPS_BY_SYMBOL["pgg"]
    metric = group.lattice.metric
    _, glides = W._lines_of(group)
    directions = sorted({line.direction for line in glides})
    assert len(directions) == 2
    assert W._dot(directions[0], directions[1], metric) == 0


def test_pg_les_axes_de_glissade_sont_paralleles():
    """« their axes are all parallel »."""
    group = W.GROUPS_BY_SYMBOL["pg"]
    _, glides = W._lines_of(group)
    assert len({line.direction for line in glides}) == 1


def test_les_miroirs_et_les_glissades_ne_se_superposent_pas():
    """Une ligne porte soit un miroir, soit une glissade, jamais les deux."""
    for group in W.GROUPS:
        mirrors, glides = W._lines_of(group)
        mirror_keys = {line.key() for line in mirrors}
        glide_keys = {line.key() for line in glides}
        assert mirror_keys & glide_keys == set(), group.symbol


# --------------------------------------------------------------------------
# Temoins positifs : le moteur est-il exact ?
# --------------------------------------------------------------------------


@pytest.mark.parametrize("group", W.GROUPS, ids=lambda group: group.symbol)
def test_le_type_de_reseau_derive_agree_avec_le_reseau_declare(group):
    """Le reseau derive doit etre du type Bravais annonce par le groupe."""
    basis = W.translation_lattice(group)
    assert W.classify_lattice(basis, group.lattice.metric) == group.lattice.name


@pytest.mark.parametrize("group", W.GROUPS, ids=lambda group: group.symbol)
def test_chaque_partie_lineaire_preserve_le_reseau(group):
    """A.b du reseau est dans le reseau : le groupe ponctuel agit sur la
    cellule primitive (controle d'exactitude, sans flottant)."""
    basis = W.translation_lattice(group)
    for matrix in W.point_group(group):
        for vector in basis:
            image = mat_vec(matrix, vector)
            assert W._in_lattice(image, basis)


@pytest.mark.parametrize("group", W.GROUPS, ids=lambda group: group.symbol)
def test_le_groupe_est_ferme(group):
    """Le produit de deux elements derives a une partie lineaire du groupe
    ponctuel, et differe du representant derive d'un vecteur du reseau."""
    basis = W.translation_lattice(group)
    representatives = W._representatives(group)
    for matrix_a, element_a in representatives.items():
        for matrix_b, element_b in representatives.items():
            product = element_a.compose(element_b)
            assert product.matrix in representatives
            target = representatives[product.matrix]
            assert W._in_lattice(
                W.vec_sub(product.translation, target.translation), basis
            )


@pytest.mark.parametrize("group", W.GROUPS, ids=lambda group: group.symbol)
def test_la_multiplicite_des_centres_est_celle_de_l_algebre(group):
    """Le nombre de positions fixees par une rotation d'ordre ``n`` vaut
    ``|det(I - A)|`` : le compte est verifie par l'algebre, pas par la meme
    fonction que le moteur.

    Le moteur attribue a chaque position son **ordre maximal** : une position
    fixee a la fois par un quart de tour et par un demi-tour est comptee
    comme d'ordre quatre. Le compte du moteur est donc une borne
    inferieure de la multiplicite algebrique, et l'egalite est exigee pour
    l'ordre le plus eleve du groupe, ou rien ne peut absorber les centres.
    """
    centers = W._rotation_centers(group)
    counts = {}
    for _, order in centers:
        counts[order] = counts.get(order, 0) + 1
    multiplicities = {}
    for matrix in W.point_group(group):
        if mat_det(matrix) <= 0:
            continue
        order = W._matrix_order(matrix)
        if order <= 1 or order in multiplicities:
            continue
        identity_minus = (
            (Fraction(1) - matrix[0][0], -matrix[0][1]),
            (-matrix[1][0], Fraction(1) - matrix[1][1]),
        )
        multiplicities[order] = abs(
            identity_minus[0][0] * identity_minus[1][1]
            - identity_minus[0][1] * identity_minus[1][0]
        )
    for order, multiplicity in multiplicities.items():
        if order in counts:
            assert counts[order] <= multiplicity, (group.symbol, order)
    if multiplicities:
        highest = max(multiplicities)
        assert counts.get(highest, 0) == multiplicities[highest], group.symbol


@pytest.mark.parametrize("group", W.GROUPS, ids=lambda group: group.symbol)
def test_les_calculs_restent_exacts(group):
    """Aucun flottant ne doit apparaitre dans les invariants derives."""
    attr = W.attributes(group)
    basis = W.translation_lattice(group)
    for vector in basis:
        assert all(isinstance(coordinate, Fraction) for coordinate in vector)
    for center, order in W._rotation_centers(group):
        assert all(isinstance(coordinate, Fraction) for coordinate in center)
        assert isinstance(order, int)
    assert isinstance(attr.point_group_order, int)
    assert isinstance(attr.mirror_directions, int)


@pytest.mark.parametrize("group", W.GROUPS, ids=lambda group: group.symbol)
def test_le_rendu_svg_produit_un_svg(group):
    """Temoin de fumee : le rendu du motif ne doit pas lever."""
    svg = W.render_svg(group, cells=2, size=64)
    assert svg.startswith("<svg")
    assert svg.count("<polygon") > 0
    assert svg.rstrip().endswith("</svg>")


@pytest.mark.parametrize("group", W.GROUPS, ids=lambda group: group.symbol)
def test_le_rendu_svg_remplit_la_toile(group):
    """Le rendu doit etre visible : la geometrie tient dans la toile.

    Regression : les coordonnees du motif sont exprimees en unites du reseau
    (de l'ordre de 1) alors que le ``viewBox`` vaut ``size`` pixels. Sans
    normalisation, toutes les coordonnees tombaient dans un carre de quelques
    unites pres de l'origine : le SVG etait valide mais le motif etait un
    point invisible dans un coin de la toile.
    """
    size = 240
    svg = W.render_svg(group, cells=2, size=size)
    couples = []
    for points in re.findall(r'points="([^"]+)"', svg):
        for couple in points.split():
            x, y = couple.split(",")
            couples.append((float(x), float(y)))
    for x, y in re.findall(r'<circle cx="(-?[\d.]+)" cy="(-?[\d.]+)"', svg):
        couples.append((float(x), float(y)))
    assert couples, group.symbol
    for x, y in couples:
        assert 0.0 <= x <= size, (group.symbol, x)
        assert 0.0 <= y <= size, (group.symbol, y)
    largeur = max(x for x, _ in couples) - min(x for x, _ in couples)
    hauteur = max(y for _, y in couples) - min(y for _, y in couples)
    assert max(largeur, hauteur) >= 0.5 * size, (group.symbol, largeur, hauteur)


def test_le_moteur_affine_est_exact_et_inversible():
    """Controle de l'algebre affine : composition, inverse, determinant."""
    matrix = ((Fraction(1), Fraction(2)), (Fraction(3), Fraction(4)))
    element = Affine(matrix, (Fraction(1, 3), Fraction(-1, 2)))
    assert element.determinant == Fraction(-2)
    identity = element.compose(element.inverse())
    assert identity.matrix == identity_matrix()
    assert identity.translation == (Fraction(0), Fraction(0))
    point = (Fraction(2), Fraction(-3))
    assert element.inverse().apply(element.apply(point)) == point
    assert mat_mul(matrix, mat_inv(matrix)) == identity_matrix()
