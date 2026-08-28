#!/usr/bin/env python3
"""Tests for scripts/notebook_tools/check_cell_source_parses.py.

Issue #13326 acceptance, 5 criteria:

  - 3 controls NEGATIFS must PASS (compile() succeeds):
      - `x = await foo()` (await de haut niveau, legitimate Jupyter)
      - `!pip install ...` and `%%time` (IPython magics)
      - any ordinary code
  - 3 controls POSITIFS must FAIL with the right KIND:
      - `print(f"a "b" c")` (motif exact PR #13287) -> 'syntax_error'
      - `print(1` (paren non fermée) -> 'syntax_error'
      - markdown source typed code -> 'markdown_typed_code'
  - main returns EXACTLY 1 (instance b GameTheory-03d cell[7]) on this checkout.
    On a runtime that recognises PEP 701, this drops to 0 if (b) is fixed.

The PEP 701 nested-quote f-string (`print(f"{d["k"]}")`) is only valid on
3.12+; the guard depends on runtime >= 3.12 to recognise it. The runtime
on the CI runner is the binding; tests here use the runtime available.
"""

import sys
import unittest
from pathlib import Path

# Make the script importable from tests/
TOOLS_DIR = Path(__file__).resolve().parent.parent / "notebook_tools"
sys.path.insert(0, str(TOOLS_DIR.parent))

from notebook_tools.check_cell_source_parses import (  # noqa: E402
    _compile_cell,
    _looks_like_markdown_typed_code,
    _strip_ipython_magics,
)


class TestCompileCellNegatives(unittest.TestCase):
    """Cell source that LOOKS like Python and must compile cleanly."""

    def test_top_level_await_legitimate(self):
        # Control #1: top-level await is legitimate in Jupyter.
        # ast.PyCF_ALLOW_TOP_LEVEL_AWAIT must be set, or this raises.
        err, _ = _compile_cell("x = await foo()")
        self.assertIsNone(err, f"top-level await rejected: {err}")

    def test_ipython_shell_magic_skipped(self):
        # `!pip install` is an IPython shell magic, not Python.
        err, _ = _compile_cell("!pip install numpy")
        self.assertIsNone(err, f"shell magic rejected: {err}")

    def test_ipython_cell_magic_skipped(self):
        # `%%time` is an IPython cell magic.
        err, _ = _compile_cell("%%time\nfor i in range(10):\n    pass")
        self.assertIsNone(err, f"cell magic rejected: {err}")

    def test_ordinary_function_compiles(self):
        err, _ = _compile_cell("def foo():\n    return 42\n")
        self.assertIsNone(err)


class TestCompileCellPositives(unittest.TestCase):
    """Cell source that must FAIL with the right KIND."""

    def test_pr_13287_motif(self):
        # The exact motif from PR #13287: `print(f"..."..."...")` -- double-quote
        # OUTSIDE the substitution field, invalid in 3.11 as in 3.14 (PEP 701
        # only governs inside the `{}`).
        src = 'print(f"  donne un levier "prononce" (0.746), kappa=2")'
        err, _ = _compile_cell(src)
        self.assertIsNotNone(err)
        self.assertFalse(_looks_like_markdown_typed_code(src))

    def test_unclosed_paren(self):
        err, _ = _compile_cell("print(1")
        self.assertIsNotNone(err)
        self.assertFalse(_looks_like_markdown_typed_code("print(1"))

    def test_markdown_typed_code_separate_kind(self):
        # Instance (b) pattern: a `### Lecture du résultat` cell typed `code`.
        # Must produce 'markdown_typed_code', not just 'syntax_error'.
        src = (
            "### Lecture du resultat\n\n"
            "La cellule montre les profils detailles par personnage.\n\n"
            "**576 profils distincts** observes sur le corpus.\n"
        )
        err, _ = _compile_cell(src)
        self.assertIsNotNone(err)
        self.assertTrue(_looks_like_markdown_typed_code(src))


class TestStripMagics(unittest.TestCase):
    """Magics `!`/`%` must be dropped before compile."""

    def test_shell_magic_line_dropped(self):
        cleaned = _strip_ipython_magics("!pip install x\ny = 1")
        self.assertNotIn("!pip", cleaned)
        self.assertIn("y = 1", cleaned)

    def test_cell_magic_line_dropped(self):
        cleaned = _strip_ipython_magics("%%time\nfor i in range(3):\n    pass")
        self.assertNotIn("%%time", cleaned)
        self.assertIn("for i in range(3):", cleaned)


class TestMarkdownHeuristic(unittest.TestCase):
    """`_looks_like_markdown_typed_code` must catch markdown-as-code without
    false-positiving on legitimate code that happens to start with `#`."""

    def test_legitimate_module_docstring_not_markdown(self):
        src = "# Compute the entropy\ndef entropy(p):\n    return -sum(p * log(p))"
        self.assertFalse(_looks_like_markdown_typed_code(src))

    def test_heading_only_markdown(self):
        src = "### Lecture du resultat"
        self.assertTrue(_looks_like_markdown_typed_code(src))

    def test_bold_text_only(self):
        src = "**576 profils distincts**"
        self.assertTrue(_looks_like_markdown_typed_code(src))


if __name__ == "__main__":
    unittest.main()
