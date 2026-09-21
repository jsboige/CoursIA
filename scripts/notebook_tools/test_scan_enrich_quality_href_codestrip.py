"""Tests unitaires pour le fix #17187 -- scan_enrich_quality.scan_href doit
neutraliser les code-spans et blocs fences AVANT _MD_LINK_RE, sinon une
formule comme `` `[]((p => q))` `` dans une table déclenche un faux positif
HREF_MISSING sur la cible `(p => q)`.

Couvre :
- _strip_code (inline code-span + fenced block, longueur preservee)
- scan_href (ne signale plus les formules en code-span, garde les vrais
  liens casses)

Run: python scripts/notebook_tools/test_scan_enrich_quality_href_codestrip.py
"""
import sys
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS_DIR))

from scan_enrich_quality import (  # noqa: E402
    _INLINE_CODE_RE,
    _strip_code,
    scan_href,
)


def _md(source_lines):
    return {"cells": [{"cell_type": "markdown", "source": source_lines}]}


class TestStripCode(unittest.TestCase):
    def test_inline_code_span_neutralized(self):
        # La formule entre backticks est passee en espaces de meme longueur.
        src = "Formule : `[]((p => q))` ici.\n"
        out = _strip_code(src)
        # Meme longueur (l'indexation en aval est stable).
        self.assertEqual(len(out), len(src))
        # Plus aucun backtick dans la sortie (code-span neutralise).
        self.assertNotIn("`", out)
        # Le texte autour est preserve verbatim.
        self.assertTrue(out.startswith("Formule : "))
        self.assertTrue(out.endswith(" ici.\n"))

    def test_inline_code_preserves_surrounding_prose(self):
        src = "Avant `code` apres\n"
        out = _strip_code(src)
        self.assertTrue(out.startswith("Avant "))
        self.assertTrue(out.endswith(" apres\n"))

    def test_double_backtick_code_span(self):
        # CommonMark: `` `text` `` (deux backticks) est aussi un code-span.
        src = "Voir `` `inline` `` svp.\n"
        out = _strip_code(src)
        self.assertNotIn("`inline`", out)

    def test_fenced_block_neutralized(self):
        src = "Before\n```python\ndef foo():\n    return [link](http://example.com)\n```\nAfter\n"
        out = _strip_code(src)
        # Les `` ``` `` ouvrants/fermants sont conservés (ils sont des marqueurs
        # de bloc), mais le contenu du bloc est blanché en espaces.
        # Vérif simple : aucune sequence "[link]" ne survit dans le bloc.
        # Note: le regex _MD_LINK_RE vise `[x](y)` avec [x] non-vide -- ici
        # le def foo() / return [...] ne matche pas, mais on teste quand meme
        # qu'aucun caractere du bloc ne pourrait leurrer le matcher.
        lines = out.split("\n")
        # Le bloc ``` ... ``` est neutralisé par _INLINE_CODE_RE (les 3 backticks
        # d'ouverture et de fermeture matchent comme un seul code-span inline).
        # Le contenu est blanché en espaces ; ce qui compte est qu'aucun
        # [link] ni URL ne survive, et que les indices sont stables.
        self.assertNotIn("[link]", out)
        self.assertNotIn("http://example.com", out)
        self.assertNotIn("def foo", out)
        # Longueur préservée (offsets en aval stables).
        self.assertEqual(len(out), len(src))
        # Avant / Après survivent.
        self.assertTrue(out.startswith("Before"))
        self.assertTrue(out.rstrip().endswith("After"))

    def test_no_code_no_op(self):
        src = "Pure prose, aucun backtick, aucun fence.\n"
        out = _strip_code(src)
        self.assertEqual(out, src)


class TestScanHrefCodeStrip(unittest.TestCase):
    """Le bug originel #17187 -- scan_href matchait des `[x](y)` dans des
    code-spans, declenchant des HREF_MISSING pour des formules modales."""

    def setUp(self):
        self.root = Path(".")

    def test_pure_code_span_no_findings(self):
        # Avant fix : aurait declenche HREF_MISSING sur `(p`, `(q`, etc.
        nb = _md([
            "Formules : `[]((p => q))` et `<>((p))`.\n",
        ])
        self.assertEqual(scan_href(Path("test.ipynb"), nb["cells"], self.root), [])

    def test_mixed_code_span_and_real_link(self):
        # Le code-span ne doit pas etre signale ; le vrai lien broken doit l'etre.
        nb = _md([
            "Mix : `[]((p))` et [vrai](nonexistent/path.md)\n",
        ])
        findings = scan_href(Path("test.ipynb"), nb["cells"], self.root)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0]["category"], "HREF_MISSING")
        self.assertEqual(findings[0]["evidence"], "nonexistent/path.md")

    def test_real_working_link_not_flagged(self):
        # Lien qui résout réellement -> pas de finding.
        nb = _md([
            "Voir [`[]((p))` est une formule, et [le code](scripts/notebook_tools/scan_enrich_quality.py)]\n",
        ])
        # Le regex markdown matche `[le code](scripts/notebook_tools/scan_enrich_quality.py)`
        # mais le contenu de `` ` `` à l'intérieur n'est pas matche. Le path
        # cible existe -> pas de finding.
        self.assertEqual(scan_href(Path("test.ipynb"), nb["cells"], self.root), [])

    def test_fenced_block_with_link_pattern_not_flagged(self):
        # Lien markdown à l'interieur d'un bloc code : pas un finding.
        src = (
            "Avant\n"
            "```python\n"
            "x = [link](http://example.com)\n"
            "```\n"
            "Apres\n"
        )
        nb = _md([src])
        self.assertEqual(scan_href(Path("test.ipynb"), nb["cells"], self.root), [])


if __name__ == "__main__":
    unittest.main(verbosity=2)
