"""Tests de scan_slides_html_block_markdown (#13360 landing, #13216 classe).

Le detecteur garde la classe « markdown avale par un bloc HTML » (regle
CommonMark HTML block : une balise seule sur sa ligne avale tout jusqu'a la
ligne vide). #13230 a corrige les 3 decks touches ; ce test couvre le
detecteur lui-meme, jamais atterre sur main avant #13360.

Un detecteur se valide par ses faux negatifs : le controle positif (defaut
fabrique) DOIT etre signale, les formes saines NE DOIVENT PAS l'etre.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scan_slides_html_block_markdown import (  # noqa: E402
    iter_decks,
    main,
    scan_file,
    scan_text,
)

_REPO_ROOT = Path(__file__).resolve().parents[3]

# Les 3 decks corriges par #13230 (classe balise OUVRANTE). Le non-regres
# attendu : aucun d'eux ne reapparait dans les findings du corpus.
DECKS_FIXED_BY_13230 = [
    "slides/01-introduction/slides.md",
    "slides/06-apprentissage/slides.md",
    "slides/S8-semantic-web/slides.md",
]


def test_positive_control_opening_tag_fabricated():
    """Acceptance #13360 : une instance FABRIQUEE du defaut est detectee."""
    text = (
        '<div class="grid grid-cols-2 gap-5">\n'
        "**Environnement multi-agents**\n"
    )
    hits = scan_text(text)
    assert hits == [(2, "**Environnement multi-agents**")]


def test_positive_control_closing_tag_fabricated():
    """Forme FERMANTE (#13345) : un `</div>` seul avale la ligne suivante
    exactement comme un `<div>` seul (HTML block type 6 ouvre sur les deux)."""
    text = "</div>\n- Behaviourism\n"
    hits = scan_text(text)
    assert hits == [(2, "- Behaviourism")]


def test_blank_line_closes_the_block():
    text = "<div>\n\n**gras voulu**\n"
    assert scan_text(text) == []


def test_self_contained_tag_not_flagged():
    """`<span>x</span>` ne correspond jamais a _OPENING_TAG (texte apres le
    premier `>` casse l'ancre de fin) : negatif nomme du script."""
    text = "<span>x</span>\n- liste saine\n"
    assert scan_text(text) == []


def test_inline_markdown_not_flagged():
    """Le markdown INLINE n'est pas signale -- garde anti-sur-accusation (le
    detecteur naif rapportait 7 hits dont 0 reel sur S3-acculturation)."""
    text = "<div>\nSome prose with *emphasis* inside\n"
    assert scan_text(text) == []


def test_tag_with_trailing_content_out_of_scope():
    """Gap documente : `<div>du texte` avale aussi, mais la regle enforcee
    est la balise SEULE sur sa ligne. Le test nomme le gap, il ne le nie pas."""
    text = "<div>du texte\n- item\n"
    assert scan_text(text) == []


def test_nested_tag_chain_flags_deepest_only():
    """Balise suivie d'une autre balise : le bloc reste ouvert mais la 2e
    balise ne porte pas de markdown ; la ligne MARkDOWN est vue a l'iteration
    de la balise qui la precede directement -- un seul hit, pas deux."""
    text = "<div>\n<div>\n- item\n"
    assert scan_text(text) == [(3, "- item")]


def test_tag_at_eof_is_silent():
    assert scan_text('<div class="x">') == []


def test_all_block_markdown_forms_detected():
    for md in ("- item", "* item", "1. item", "# Titre", "> quote", "| a | b |"):
        text = f"<div>\n{md}\n"
        assert scan_text(text) == [(2, md)], md


def test_check_nonexistent_path_returns_2(capsys):
    assert main(["--check", "no/such/path"]) == 2


def test_corpus_no_regression_on_decks_fixed_by_13230():
    """Acceptance #13360 : la sortie ne REGRESSE pas les decks corriges par
    #13230 (classe balise OUVRANTE). Subtilite mesuree : slides/01-introduction
    est a la fois un deck #13230 ET le porteur de l'unique occurrence vivante
    -- de la classe FERMANTE (#13345), pas une regression de #13230. On
    verifie donc la CLASSE du finding (ligne precedente = `</tag>` seul), pas
    son numero de ligne (il derive a chaque edition du deck)."""
    slides_root = _REPO_ROOT / "slides"
    findings = {}
    for deck in iter_decks(slides_root):
        hits = scan_file(deck)
        if hits:
            findings[deck.relative_to(_REPO_ROOT).as_posix()] = hits

    # Les 2 decks non concernes par #13345 : zero finding.
    for deck in DECKS_FIXED_BY_13230:
        if deck == "slides/01-introduction/slides.md":
            continue
        assert deck not in findings, f"regression de #13230 sur {deck}"

    # Corpus total connu : exactement 1 occurrence vivante.
    assert list(findings) == ["slides/01-introduction/slides.md"], findings
    hits = findings["slides/01-introduction/slides.md"]
    assert len(hits) == 1, hits

    # Et elle est de la classe FERMANTE (#13345), pas de la classe que
    # #13230 a corrige (ouvrante) : la ligne precedente est un `</tag>` seul.
    import re
    lines = (slides_root / "01-introduction" / "slides.md").read_text(
        encoding="utf-8"
    ).split("\n")
    hit_line = hits[0][0]
    preceding = lines[hit_line - 2]
    assert re.match(r"^\s*</[a-zA-Z][a-zA-Z0-9-]*>\s*$", preceding), (
        f"l'occurrence vivante devait etre de classe fermante (#13345), "
        f"ligne precedente = {preceding!r}"
    )


def test_corpus_deck_discovery_is_non_recursive_and_finds_the_deck_dirs():
    """36 decks au landing #13360 : le denominateur est borne -- un iter_decks
    qui decouvrirait 0 deck rendrait le test de corpus vert et muet."""
    decks = list(iter_decks(_REPO_ROOT / "slides"))
    assert len(decks) >= 30, f"decouverte de deck trop maigre : {len(decks)}"
