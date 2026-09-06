#!/usr/bin/env python3
"""Tests for scripts/notebook_tools/check_latex_control_chars.py (#14859).

The issue demands a positive control AND a negative control: during the
original measurement a wrong pattern set twice produced a clean zero (once
by over-accusing, once by staying completely mute). A detector is validated
by its false negatives, so every positive below is a REAL defect shape from
the measured corpus, and every negative is a shape the first probe version
got wrong.
"""
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path


def _load_check_latex_control_chars():
    """Direct path-based load (same rationale as test_check_cell_source_parses:
    namespace-package ambiguity of scripts/notebook_tools/ between local
    pytest and CI's combined collect)."""
    TOOL_PATH = (
        Path(__file__).resolve().parent.parent
        / "notebook_tools" / "check_latex_control_chars.py"
    )
    spec = importlib.util.spec_from_file_location(
        "check_latex_control_chars", str(TOOL_PATH)
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


clc = _load_check_latex_control_chars()


def md(source: str) -> dict:
    return {"cell_type": "markdown", "id": "md-test", "source": source}


# --- Positive controls: measured defect shapes, MUST be detected ----------
#
# NOTE ON THE LITERALS BELOW: a SINGLE backslash in these Python strings is
# the defect's ghost -- `\t` is a real TAB (what Python left of `\theta`),
# `\r` a real CR, `\f` a real FF, `\v` a real VT, `\b` a real BS, `\n` a
# real LF. The cell therefore carries exactly the bytes found in the
# measured corpus. Double backslashes (`\\text`) are real LaTeX, kept to
# prove the detector is not just matching any backslash.

class TestPositiveControls(unittest.TestCase):

    def hit(self, text):
        hits = clc.find_defects(text)
        self.assertEqual(len(hits), 1, f"expected 1 hit, got {hits}")
        return hits[0]

    def test_tab_heta_inline(self):
        # GameTheory-15 d6a75983: `$<TAB>heta = 0.8$`
        h = self.hit("Pour $\theta = 0.8$, la probabilite")
        self.assertEqual(h["command"], "\\theta")

    def test_cr_ightarrow_inline(self):
        # GameTheory-15 e109ee46: `$v : 2^N <CR>ightarrow \mathbb{R}$`
        # (`\m` doubled: invalid Python escape, and \mathbb is real LaTeX)
        h = self.hit("$v : 2^N \rightarrow \\mathbb{R}$")
        self.assertEqual(h["command"], "\\rightarrow")

    def test_ff_rac_display(self):
        h = self.hit("$$\frac{|S|!(n-|S|-1)!}{n!}$$")
        self.assertEqual(h["command"], "\\frac")

    def test_lf_eg_glued_display(self):
        # LF glued to the previous token (no space) inside $$...$$
        h = self.hit("$$x \neg y$$")
        self.assertEqual(h["command"], "\\neg")

    def test_lf_eq_neq(self):
        # GameTheory-15c tranche2-glop: `S<LF>eq<VT>arnothing` = \neq\varnothing
        hits = clc.find_defects("$$S\neq\varnothing$$")
        self.assertEqual([h["command"] for h in hits], ["\\neq", "\\varnothing"])

    def test_vt_arnothing_queue_missing_from_issue_table(self):
        # \varnothing's queue was absent from the issue's own queue table
        h = self.hit("pour tout $S \varnothing$")
        self.assertEqual(h["command"], "\\varnothing")

    def test_bs_eta_binom(self):
        hits = clc.find_defects("donne $\binom{n-1}{k-1}$ et $\beta_i(v)$")
        self.assertEqual([h["command"] for h in hits], ["\\binom", "\\beta"])

    def test_tab_o_to_with_word_boundary(self):
        # Planners-4 tranche2-fd-intro: `$<TAB>o$ SAS+` = \to
        h = self.hit("translation domaine $\to$ SAS+")
        self.assertEqual(h["command"], "\\to")


# --- Negative controls: shapes a looser detector gets wrong ----------------

class TestNegativeControls(unittest.TestCase):

    def test_code_cell_newline_else_never_scanned(self):
        # discriminant 1: code cells are out of scope (`\nelse:` was the
        # first version's false-positive flood)
        nb = {"cells": [{"cell_type": "code", "id": "c1",
                         "source": "x = 1\nelse:\n    pass"}]}
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "n.ipynb"
            p.write_text(json.dumps(nb), encoding="utf-8")
            self.assertEqual(clc.scan_notebook(p), [])

    def test_latex_rowbreak_then_newline_is_legitimate(self):
        # `\\` + real newline inside $$...$$ (measured exclusion)
        text = "$$1 & \\text{si } x \\leq 0 \\\\\ne^{-x} & \\text{sinon}$$"
        self.assertEqual(clc.find_defects(text), [])

    def test_single_backslash_newline_excluded(self):
        text = "$$f(x) =\\\n\\max(x, 0)$$"
        self.assertEqual(clc.find_defects(text), [])

    def test_dollar_in_backticks_is_code(self):
        # v1 FP class: `$FILE` in backticks paired with a later `$`
        text = "run `cat $FILE` then\necho \"$REVIEW\" > out.rev"
        self.assertEqual(clc.find_defects(text), [])

    def test_prose_newline_between_currency_dollars(self):
        # v1 FP class: two unrelated dollars on two lines, LF between,
        # next word starts with "un"/"est" (single-letter queue collision)
        text = "Le montant est $100k\nun risque de $1k par trade suffit"
        self.assertEqual(clc.find_defects(text), [])

    def test_single_letter_queue_requires_word_boundary(self):
        # TAB + "op" as a whole word is \top; TAB + "option" is not a command
        text = "le sommet $\top$ mais pas $	optionnel$"
        hits = clc.find_defects(text)
        self.assertEqual([h["command"] for h in hits], ["\\top"])

    def test_plain_tab_whitespace_inside_math(self):
        # a TAB that is just spacing, followed by a non-queue word
        text = "$ x + y $\t et $\tz + t$ mais $\tzero$"
        hits = clc.find_defects(text)
        # \tzero: "z" is not a queue for t; only... none match
        self.assertEqual(hits, [])

    def test_escaped_dollar_not_a_delimiter(self):
        text = "prix \\$5 et \\$10 : pas de portee math du tout\nestimation"
        self.assertEqual(clc.find_defects(text), [])


# --- Exit codes -------------------------------------------------------------

class TestMainExitCodes(unittest.TestCase):

    def _run(self, nb: dict) -> int:
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "n.ipynb"
            p.write_text(json.dumps(nb), encoding="utf-8")
            return clc.main(["--path", str(p)])

    def test_exit_1_on_defect(self):
        nb = {"cells": [md("Pour $\theta = 0.8$")]}
        self.assertEqual(self._run(nb), 1)

    def test_exit_0_on_clean(self):
        nb = {"cells": [md(r"Pour $\theta = 0.8$ rendu correctement")]}
        self.assertEqual(self._run(nb), 0)

    def test_exit_2_on_unreadable(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "broken.ipynb"
            p.write_text("{not json", encoding="utf-8")
            self.assertEqual(clc.main(["--path", str(p)]), 2)


if __name__ == "__main__":
    unittest.main()
