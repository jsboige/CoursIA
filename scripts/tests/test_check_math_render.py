"""Unit tests for check_math_render.py (positive AND negative controls).

Lesson #14859: a detector is validated by its false negatives -- write the
forms it must catch and check it catches them, and the forms it must spare.
"""

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

import check_math_render as m  # noqa: E402

STATIC = {"with_katex": False}


def kinds(source):
    defects, _ = m.find_defects(source, **STATIC)
    return {d["kind"] for d in defects}


class TestLatexPureDelims(unittest.TestCase):
    def test_inline_paren_detected(self):
        self.assertIn("LATEX-PURE-DELIMS", kinds(r"le flux \(\Phi_{DM}\) croit"))

    def test_block_bracket_detected(self):
        self.assertIn("LATEX-PURE-DELIMS", kinds(r"formule \[EI(A \to B)\] directe"))

    def test_delim_in_backtick_spared(self):
        self.assertNotIn("LATEX-PURE-DELIMS", kinds("utilise `\\(x\\)` en LaTeX pur"))

    def test_dollar_scope_spared(self):
        self.assertNotIn("LATEX-PURE-DELIMS", kinds(r"le flux $\Phi$ croit"))


class TestOddDollars(unittest.TestCase):
    def test_odd_dollar_paragraph(self):
        src = "prix : 5$ et $\\Phi$ puis\n\nun $ orphelin"
        self.assertIn("ODD-DOLLARS", kinds(src))

    def test_even_dollars_spared(self):
        self.assertNotIn("ODD-DOLLARS", kinds(r"$a$ et $b$ dans le meme paragraphe"))

    def test_display_block_spared(self):
        self.assertNotIn("ODD-DOLLARS", kinds("$$x = 1$$"))

    def test_dollar_in_backtick_spared(self):
        self.assertNotIn("ODD-DOLLARS", kinds("la commande `$FILE` vaut 5"))

    def test_odd_count_confined_to_paragraph(self):
        src = "$a$ pair ici\n\nparagraphe $ orphelin\n\n$a$ redevient $b$"
        self.assertIn("ODD-DOLLARS", kinds(src))

    def test_currency_dollar_spared(self):
        # "$100" est de la devise, pas un delimiteur math (mesure corpus v1)
        self.assertNotIn("ODD-DOLLARS", kinds("le cout depasse $100 par run et $200 cumules"))

    def test_dollar_in_fenced_code_spared(self):
        src = "config bash :\n```bash\nK=$(pwd)\necho $HOME\n```\nfin"
        self.assertNotIn("ODD-DOLLARS", kinds(src))


class TestNudeLatex(unittest.TestCase):
    def test_nude_command_detected(self):
        self.assertIn("NUDE-LATEX", kinds(r"le \Phi du systeme"))

    def test_command_in_scope_spared(self):
        self.assertNotIn("NUDE-LATEX", kinds(r"le $\Phi$ du systeme"))

    def test_command_in_backtick_spared(self):
        self.assertNotIn("NUDE-LATEX", kinds(r"la commande `\frac{a}{b}` en code"))

    def test_known_command_word_boundary(self):
        # "\top" n'est pas dans la liste ; "\to" l'est -- frontiere de mot
        self.assertIn("NUDE-LATEX", kinds(r"flèche A \to B"))

    def test_lone_backslash_spared(self):
        self.assertNotIn("NUDE-LATEX", kinds("un antislash \\ seul"))

    def test_command_in_fenced_code_spared(self):
        # code Lean dans un bloc fence : du code, pas de la prose (v1 FP massif)
        src = "preuve :\n```lean\ntheorem t : x \\in S := by simp\n```\nfin"
        self.assertNotIn("NUDE-LATEX", kinds(src))

    def test_latex_delim_in_fenced_code_spared(self):
        src = "exemple :\n```text\nf\\(x\\) brute\n```\nfin"
        self.assertNotIn("LATEX-PURE-DELIMS", kinds(src))


class TestKatexLeg(unittest.TestCase):
    def test_payload_positions_are_list_indices(self):
        # Incident corpus v1 : la position TEXTE (m.start()) etait passee comme
        # index de liste -> "list index out of range" sur 13 notebooks. Le
        # payload doit porter des indices ENUMERES, et le retour est recale
        # sur scopes[index].
        import json as _json

        captured = {}

        class FakeProc:
            returncode = 0
            stdout = _json.dumps([{"pos": 1, "error": "KaTeX parse error"}])
            stderr = ""

        def fake_run(cmd, input=None, **kw):
            captured["payload"] = _json.loads(input)
            return FakeProc()

        import subprocess
        orig = subprocess.run
        subprocess.run = fake_run
        try:
            defects, scopes = m.find_defects(
                "texte " + "$a$" * 1 + " milieu " * 200 + "$b$ final", with_katex=True)
        finally:
            subprocess.run = orig
        self.assertEqual([p["pos"] for p in captured["payload"]], [0, 1])
        self.assertTrue(all(d["kind"] == "KATEX-UNRENDERABLE" for d in defects))
        # le defaut reference scopes[1] -- la DEUXIEME formule, pas la position
        # texte : le detail porte l'erreur + la formule fautive
        self.assertIn("b", defects[0]["detail"])
        self.assertEqual(defects[0]["context"], "b")


class TestScanNotebook(unittest.TestCase):
    def _nb(self, tmp, cells):
        import json
        nb = {"cells": [{"cell_type": t, "source": s, "id": f"c{i}"}
                        for i, (t, s) in enumerate(cells)]}
        p = tmp / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        return p

    def test_markdown_only_code_cell_spared(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            p = self._nb(Path(d), [("code", r"x = '\Phi'  # pas du markdown")])
            self.assertEqual(m.scan_notebook(p, with_katex=False), [])

    def test_defect_carries_cell_index(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            p = self._nb(Path(d), [
                ("markdown", "propre"),
                ("markdown", r"un \(\Phi\) nu"),
            ])
            defects = m.scan_notebook(p, with_katex=False)
            self.assertEqual(len(defects), 1)
            self.assertEqual(defects[0]["cell_index"], 1)


class TestExitContract(unittest.TestCase):
    def test_clean_returns_zero(self):
        import json, tempfile
        with tempfile.TemporaryDirectory() as d:
            p = self._nb(Path(d), [("markdown", "rien a signaler")])
            self.assertEqual(m.main(["--path", str(p), "--no-katex"]), 0)

    def test_defect_returns_one(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            p = self._nb(Path(d), [("markdown", r"\(x\) nu")])
            self.assertEqual(m.main(["--path", str(p), "--no-katex"]), 1)

    _nb = TestScanNotebook._nb


if __name__ == "__main__":
    unittest.main()
