"""Tests de la fermeture des 17 groupes de pavage (`scripts/symmetry/closure`).

Ce que la fermeture ajoute au parcours en largeur
-------------------------------------------------
`wallpaper._representatives` atteint chaque element du groupe ponctuel par un
parcours borne, et `test_wallpaper_groups.py::test_le_groupe_est_ferme` verifie
que le produit de deux representants retombe sur un representant **a une
translation du reseau pres**. `closure` ferme l'ensemble dans sa **forme
canonique** (translation ramenee au representant de sa classe) et exige trois
choses de plus :

1. le produit de deux elements quelconques de l'ensemble ferme, ramene a sa
   forme canonique, est **un element de l'ensemble** (egalite, pas « a un
   vecteur du reseau pres ») ;
2. l'ensemble porte une classe par partie lineaire et son cardinal est celui
   du groupe ponctuel ;
3. il porte **la meme signature** que les attributs derives du parcours,
   champ a champ. Les deux derivations sont independantes : la table de
   reference reste opposee a l'une comme a l'autre, elle n'est la source
   d'aucune.

Reference externe : la page « Wallpaper group » de Wikipedia, archivee dans le
gisement partage ; son empreinte SHA-256 et les citations verbatim sont dans
`scripts/tests/test_wallpaper_groups.py` (non recopiees ici pour ne pas
deriver). Ce fichier ne relit pas la reference : il verifie l'accord interne
des deux derivations du depot, et les invariants qui doivent tenir pour tout
choix de representants.

Controles negatifs et controle positif
--------------------------------------
* **Changement d'origine** : la signature ne doit pas bouger (une signature
  qui bouge mesure la jauge, pas le groupe).
* **Jauge** : translater un generateur d'un vecteur du reseau ne doit rien
  changer.
* **Controle positif** : un jeu de generateurs dont les parties lineaires sont
  celles de `pmm` (deux miroirs perpendiculaires) mais dont les elements
  affines sont des glissades doit se refermer sur `pgg` -- l'analogue, pour
  les pavages, du controle de frise « l'ancien `p2gg` se referme sur `p2mg` ».
* **Generateurs non cristallographiques** : la fermeture refuse de boucler.
"""

from fractions import Fraction

import pytest
from symmetry import closure as C
from symmetry import wallpaper as W
from symmetry.affine import Affine

F = Fraction

GROUPES = W.GROUPS
par_groupe = pytest.mark.parametrize("group", GROUPES, ids=lambda g: g.symbol)


def reseau_canonique() -> tuple[tuple[Fraction, Fraction], tuple[Fraction, Fraction]]:
    """Le reseau carre unite, en coordonnees de base."""
    return ((F(1), F(0)), (F(0), F(1)))


@par_groupe
def test_ensemble_ferme_est_stable_par_composition(group):
    """Tout produit de deux elements de l'ensemble y retombe, en forme canonique."""
    basis = W.translation_lattice(group)
    ferme = C.closed_set(group)
    for a in ferme:
        for b in ferme:
            assert C.canonical(a.compose(b), basis) in ferme


@par_groupe
def test_une_classe_par_partie_lineaire_et_identite_presente(group):
    """Une classe modulo le reseau par element du groupe ponctuel, identite incluse."""
    ferme = C.closed_set(group)
    assert len(ferme) == len({element.matrix for element in ferme})
    assert len(ferme) == len(W.point_group(group))
    assert any(element.is_identity for element in ferme)


@par_groupe
def test_signature_fermee_egale_les_attributs(group):
    """La signature lue sur l'ensemble ferme et les attributs derives concordent."""
    assert C.compare_with_attributes(group) == {}


def test_les_17_signatures_sont_distinctes():
    """Deux groupes distincts ne peuvent pas avoir la meme signature."""
    par_signature = {}
    for group in GROUPES:
        par_signature.setdefault(C.signature(group).key(), []).append(group.symbol)
    doublons = {cle: noms for cle, noms in par_signature.items() if len(noms) > 1}
    assert doublons == {}
    assert len(par_signature) == len(GROUPES) == 17


@par_groupe
def test_signature_invariante_par_changement_d_origine(group):
    """Deplacer l'origine translate les translations sans changer la signature."""
    reference = C.signature(group).key()
    basis = W.translation_lattice(group)
    for origin in ((F(1, 4), F(1, 3)), (F(1, 7), F(-2, 5)), (F(-3, 8), F(5, 11))):
        decales = [C.shift_origin(generateur, origin) for generateur in group.generators]
        signature = C.signature_from_elements(group, C.closure(decales, basis))
        assert signature.key() == reference


@par_groupe
def test_signature_invariante_par_jauge(group):
    """Translater un generateur d'un vecteur du reseau ne change pas le groupe."""
    reference = C.signature(group).key()
    basis = W.translation_lattice(group)
    decalage = basis[0]
    generateurs = list(group.generators)
    dernier = generateurs[-1]
    generateurs[-1] = Affine(
        dernier.matrix,
        (dernier.translation[0] + decalage[0], dernier.translation[1] + decalage[1]),
    )
    signature = C.signature_from_elements(group, C.closure(generateurs, basis))
    assert signature.key() == reference


def test_ordre_d_une_glissade_est_infini_et_son_carre_est_une_translation():
    """Une glissade n'est pas une involution : la reduire avant de la composer
    ferait passer son carre (une translation du reseau) pour l'identite."""
    pg = W.GROUPS_BY_SYMBOL["pg"]
    basis = W.translation_lattice(pg)
    glissades = [element for element in C.closed_set(pg) if element.determinant < 0]
    assert len(glissades) == 1
    glissade = glissades[0]
    assert C.order_of(glissade) == 0
    carre = glissade.compose(glissade)
    assert carre.is_pure_translation
    assert not carre.is_identity
    assert W._in_lattice(carre.translation, basis)


def test_un_miroir_est_une_involution():
    """Le miroir de `pm`, lui, se referme en deux pas sur l'identite exacte."""
    pm = W.GROUPS_BY_SYMBOL["pm"]
    miroirs = [element for element in C.closed_set(pm) if element.determinant < 0]
    assert len(miroirs) == 1
    assert C.order_of(miroirs[0]) == 2


def test_cm_porte_miroir_et_glissade_dans_la_meme_classe():
    """`cm` a une seule classe orientation-reversing, qui porte a la fois un
    miroir et un axe de glissade : lire le representant ne suffit pas a la
    nommer, il faut lire les lignes du groupe."""
    cm = W.GROUPS_BY_SYMBOL["cm"]
    anti = [element for element in C.closed_set(cm) if element.determinant < 0]
    assert len(anti) == 1
    signature = C.signature(cm)
    assert (signature.mirror_lines, signature.glide_axes) == (1, 1)


def test_controle_positif_la_partie_lineaire_ne_nomme_pas_le_groupe():
    """Deux miroirs perpendiculaires transformes en glissades : le nom lu sur
    les parties lineaires serait `pmm`, la fermeture lit `pgg`."""
    pmg = W.GROUPS_BY_SYMBOL["pmg"]
    pgg = W.GROUPS_BY_SYMBOL["pgg"]
    pmm = W.GROUPS_BY_SYMBOL["pmm"]
    translations = [g for g in pmg.generators if g.is_pure_translation]
    miroir_v = next(g for g in pmg.generators if g.matrix == W._MIRROR_V)
    glissade_u = next(g for g in pmg.generators if g.matrix == W._MIRROR_U)
    # Le miroir translate d'une demi-maille le long de son axe est une glissade.
    glissade_v = Affine(miroir_v.matrix, (F(0), F(1, 2)))
    generateurs = (*translations, glissade_u, glissade_v)
    assert set(generateurs) == set(pgg.generators)
    parties_lineaires = {g.matrix for g in generateurs if g.determinant < 0}
    assert parties_lineaires == {W._MIRROR_U, W._MIRROR_V}
    basis = W.translation_lattice(pgg)
    signature = C.signature_from_elements(pgg, C.closure(generateurs, basis))
    assert signature.key() == C.signature(pgg).key()
    assert signature.key() != C.signature(pmg).key()
    assert signature.key() != C.signature(pmm).key()


def test_generateurs_non_cristallographiques_sont_refuses():
    """Un cisaillement engendre un groupe infini modulo le reseau : la
    fermeture leve au lieu de boucler."""
    cisaillement = Affine(((F(1), F(1)), (F(0), F(1))), (F(0), F(0)))
    with pytest.raises(ValueError):
        C.closure(
            [Affine.translation(1, 0), Affine.translation(0, 1), cisaillement],
            reseau_canonique(),
        )


def test_verify_all_ne_trouve_aucun_ecart():
    """Les 17 groupes se ferment et portent les memes champs par les deux voies."""
    assert C.verify_all() == {}
