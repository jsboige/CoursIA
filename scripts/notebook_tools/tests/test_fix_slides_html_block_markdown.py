"""Tests unitaires de fix_slides_html_block_markdown.

Le scanner source (scan_slides_html_block_markdown.py, #13218) reste couvert
par son propre test ; ici on teste le script de fix : parser la sortie du
scanner + inserer les lignes vides sans introduire de modifications
parasites."""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fix_slides_html_block_markdown import (  # noqa: E402
    parse_scanner_output,
    would_insert_blank,
    apply_fix,
)


SAMPLE_SCANNER_OUTPUT = """\
scanned 36 markdown file(s) under slides

slides/01-introduction/slides.md  (1)
  L595    - Intelligence animale

slides/06-apprentissage/slides.md  (39)
  L286    - **Tri des symboles selon**
  L1878   - **Step 2: New Mean: 5.25**
  L2297   - **Comportements problematiques observes** :

slides/S8-semantic-web/slides.md  (9)
  L189    ## Types de requetes SPARQL
  L303    ## OWL 2 : au-dela de RDFS

total: 11 line(s) of block markdown swallowed by an HTML block
fix: insert a blank line after the opening tag preceding each line above
"""


def test_parse_scanner_output_extracts_files_and_lines():
    hits = parse_scanner_output(SAMPLE_SCANNER_OUTPUT)
    # SAMPLE_SCANNER_OUTPUT declare 11 hits en total mais n'en liste
    # qu'un par deck : 1 + 3 + 2 = 6.
    assert len(hits) == 6
    files = {h.file for h in hits}
    assert Path("slides/01-introduction/slides.md") in files
    assert Path("slides/06-apprentissage/slides.md") in files
    assert Path("slides/S8-semantic-web/slides.md") in files
    lines_by_file = {h.file: [] for h in hits}
    for h in hits:
        lines_by_file[h.file].append(h.line)
    assert lines_by_file[Path("slides/06-apprentissage/slides.md")] == [286, 1878, 2297]
    assert lines_by_file[Path("slides/S8-semantic-web/slides.md")] == [189, 303]


def test_would_insert_blank_on_opening_tag():
    """La ligne precedent doit etre non-vide et contenir <+> (sanity check)."""
    lines = ["", '<div class="grid">', "- **item**", ""]
    assert would_insert_blank(lines, 3) is True


def test_would_insert_blank_false_on_blank_line():
    """Si la ligne d'avant est deja vide, ne pas re-inserer."""
    lines = ["", "", "- **item**", ""]
    assert would_insert_blank(lines, 3) is False


def test_would_insert_blank_false_on_line_1():
    """Pas de hit a la ligne 1 (rien a inserer avant)."""
    lines = ["- **item**"]
    assert would_insert_blank(lines, 1) is False


def test_apply_fix_inserts_blank_lines(tmp_path):
    """Le script doit inserer une ligne vide AVANT chaque hit signale,
    en ordre decroissant pour eviter les decalages d'index."""
    src = tmp_path / "deck.md"
    src.write_text(
        '<div v-click="2">\n'
        '- **Item 1**\n'
        '- Suite item 1\n'
        '\n'
        '<div v-click="3">\n'
        '- **Item 2**\n'
        '- Suite item 2\n'
        '',
        encoding='utf-8',
    )
    # Hit sur les lignes 2 et 6 (1-based) : les markdown Items 1 et 2.
    insertions = apply_fix(src, [6, 2], dry_run=False)
    assert len(insertions) == 2
    text = src.read_text(encoding='utf-8')
    # Attendu : ligne vide inseree entre <div v-click="2"> et "- **Item 1**"
    #           ligne vide inseree entre <div v-click="3"> et "- **Item 2**"
    expected = (
        '<div v-click="2">\n'
        '\n'
        '- **Item 1**\n'
        '- Suite item 1\n'
        '\n'
        '<div v-click="3">\n'
        '\n'
        '- **Item 2**\n'
        '- Suite item 2\n'
    )
    assert text == expected, f"got:\n{text!r}\nexpected:\n{expected!r}"


def test_apply_fix_dry_run_does_not_modify(tmp_path):
    src = tmp_path / "deck.md"
    original = (
        '<div class="dense-list">\n'
        '- **Item**\n'
    )
    src.write_text(original, encoding='utf-8')
    insertions = apply_fix(src, [2], dry_run=True)
    assert len(insertions) == 1
    assert src.read_text(encoding='utf-8') == original, "dry-run modified file"


def test_apply_fix_idempotent_on_already_repaired(tmp_path):
    """Si une ligne vide est deja la, le script la signale mais ne la duplique pas."""
    src = tmp_path / "deck.md"
    src.write_text(
        '<div class="dense-list">\n'
        '\n'
        '- **Deja repare**\n',
        encoding='utf-8',
    )
    # Hit 3, mais ligne 2 deja vide -> would_insert_blank False
    insertions = apply_fix(src, [3], dry_run=False)
    assert len(insertions) == 0
    # Fichier inchange
    assert src.read_text(encoding='utf-8') == (
        '<div class="dense-list">\n'
        '\n'
        '- **Deja repare**\n'
    )


def test_apply_fix_handles_trailing_blank_line(tmp_path):
    """Le fichier termine par un newline : split('\n') ajoute un '' final.
    Le script ne doit pas se laisser perturber."""
    src = tmp_path / "deck.md"
    src.write_text(
        '<div v-click="1">\n'
        '- **Final item**\n',
        encoding='utf-8',
    )
    insertions = apply_fix(src, [2], dry_run=False)
    assert len(insertions) == 1
    assert src.read_text(encoding='utf-8') == (
        '<div v-click="1">\n'
        '\n'
        '- **Final item**\n'
    )
