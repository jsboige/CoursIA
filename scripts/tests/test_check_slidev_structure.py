"""Tests de `scripts/check_slidev_structure.py`.

Les cas ne sont pas inventes : ce sont les **trois** tetes de PR du rollout
#10950 du 2026-08-20, plus `main`. Deux portent un defaut reel, une est saine,
`main` est sain. Un detecteur se recette sur ses faux negatifs autant que sur
ses hits -- un motif absent ne leve pas d'erreur, il rend juste un resultat
plus petit et plus propre que la verite (cf. #11668).
"""

import pathlib
import sys

import pytest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from check_slidev_structure import check, parse_slides, selftest  # noqa: E402


def _deck(tmp_path, content):
    p = tmp_path / "slides.md"
    p.write_text(content, encoding="utf-8")
    return str(p)


ROOT_FM = "---\ntheme: default\n---\n\n# Titre\n\ntexte\n"


# --------------------------------------------------------------------------
# defaut 1 : marqueur de colonne orphelin (build VERT, contenu perdu)
# --------------------------------------------------------------------------

def test_orphan_right_est_signale(tmp_path):
    """Le cas #11912 : `two-cols` retire, `::right::` laisse en place."""
    deck = _deck(tmp_path, ROOT_FM + """
---

# Slide cassee

gauche

::right::

droite -- jetee par Slidev
""")
    hits = [h for h in check(deck) if "MARQUEUR_ORPHELIN" in h]
    assert len(hits) == 1


def test_two_cols_legitime_reste_muet(tmp_path):
    """Le controle negatif : un `::right::` sous `two-cols` est correct.

    C'est la moitie qui compte le plus. Un detecteur qui signale aussi les
    slides saines forme les reviewers a l'ignorer -- plus nuisible que pas de
    detecteur du tout.
    """
    deck = _deck(tmp_path, ROOT_FM + """
---
layout: two-cols
---

# Slide legitime

gauche

::right::

droite
""")
    assert [h for h in check(deck) if "MARQUEUR_ORPHELIN" in h] == []


def test_left_marker_aussi_couvert(tmp_path):
    deck = _deck(tmp_path, ROOT_FM + "\n---\n\n# X\n\n::left::\n\ny\n")
    assert len([h for h in check(deck) if "MARQUEUR_ORPHELIN" in h]) == 1


def test_marqueur_inline_nest_pas_un_marqueur(tmp_path):
    """`::right::` cite au milieu d'une phrase n'est pas un marqueur de colonne.

    Slidev n'honore le marqueur que seul sur sa ligne. Une prose qui *parle*
    du marqueur -- typiquement la doc de la convention -- ne doit pas
    declencher le gate : c'est la meme classe de faux positif que #11861, ou
    un detecteur accusait le commentaire qui documentait le defaut.
    """
    deck = _deck(tmp_path, ROOT_FM + "\n---\n\n# X\n\nOn ecrit ::right:: pour separer.\n")
    assert [h for h in check(deck) if "MARQUEUR_ORPHELIN" in h] == []


def test_deux_slides_deux_constats(tmp_path):
    body = "\n---\n\n# A\n\n::right::\n\nx\n\n---\n\n# B\n\n::right::\n\ny\n"
    assert len([h for h in check(_deck(tmp_path, ROOT_FM + body))
                if "MARQUEUR_ORPHELIN" in h]) == 2


# --------------------------------------------------------------------------
# defaut 2 : separateur colle a un titre (build ROUGE, message trompeur)
# --------------------------------------------------------------------------

def test_separateur_colle_au_titre_est_signale(tmp_path):
    """Le cas #11914 : `---` puis `# Titre` sans ligne vide."""
    deck = _deck(tmp_path, "---\ntheme: default\n---\n\n# A\n\ntexte\n---\n# B colle\n\n**gras**\n")
    hits = [h for h in check(deck) if "SEP_COLLE_AU_TITRE" in h]
    assert len(hits) == 1
    assert "B colle" in hits[0]


def test_separateur_avec_ligne_vide_reste_muet(tmp_path):
    deck = _deck(tmp_path, "---\ntheme: default\n---\n\n# A\n\ntexte\n\n---\n\n# B\n\nprose\n")
    assert [h for h in check(deck) if "SEP_COLLE_AU_TITRE" in h] == []


def test_frontmatter_racine_nest_pas_un_constat(tmp_path):
    """Le `---` d'ouverture du frontmatter racine n'est jamais un separateur."""
    assert check(_deck(tmp_path, ROOT_FM)) == []


# --------------------------------------------------------------------------
# parseur
# --------------------------------------------------------------------------

def test_frontmatter_de_slide_nouvre_pas_une_slide():
    """`---\\nlayout: x\\n---` est UN delimiteur, pas deux slides vides."""
    lines = (ROOT_FM + "\n---\nlayout: two-cols\n---\n\n# S2\n\nx\n").splitlines()
    slides = parse_slides(lines)
    assert len(slides) == 2
    assert any("two-cols" in f for f in slides[1][1])


def test_selftest_passe():
    """Le controle embarque doit passer -- c'est lui que la CI appelle."""
    assert selftest() is True


# --------------------------------------------------------------------------
# mesure repo-wide : la garde anti-sur-accusation
# --------------------------------------------------------------------------

@pytest.mark.skipif(not pathlib.Path("slides").is_dir(),
                    reason="lance hors racine du depot")
def test_aucun_deck_de_main_nest_accuse():
    """Zero constat sur les decks du depot.

    Une suite verte prouve ce que l'auteur a imagine ; cette mesure-la prouve
    ce que l'outil fait sur le monde. Si elle rougit un jour, la question est
    d'abord "le deck a-t-il regresse ?" -- et seulement ensuite "le detecteur
    sur-accuse-t-il ?".
    """
    decks = sorted(pathlib.Path("slides").rglob("slides.md"))
    assert decks, "aucun deck trouve : le test ne mesure rien"
    constats = []
    for d in decks:
        constats += check(str(d))
    assert constats == [], "\n".join(constats)
