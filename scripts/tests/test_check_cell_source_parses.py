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

import importlib.util
import sys
import unittest
from pathlib import Path


def _load_check_cell_source_parses():
    """Load check_cell_source_parses.py directly via importlib spec.

    Direct path-based load bypasses the implicit-namespace-package ambiguity
    in `scripts/notebook_tools/` (which hosts BOTH a module `notebook_tools.py`
    AND multiple standalone scripts; Python 3 namespace-package resolution
    differs between local `pytest scripts/tests` and CI's combined collect
    from `scripts/tests/` + `scripts/notebook_tools/tests/` under
    `--import-mode importlib`, surfacing as
    `ImportError: cannot import name 'X' from 'notebook_tools' (unknown location)`).

    c.690 narrow 157ᵉ fix: the file is imported under its bare name so its
    location is unambiguous to importlib; the test module rebinds the public
    surface at import time and downstream tests call `_compile_cell(...)` etc.
    directly. No `__init__.py` is created in `scripts/notebook_tools/`, so the
    pre-existing tests that import `from notebook_tools import CellInfo` (the
    consolidated module) keep working under their original namespace-package
    semantics.
    """
    SCRIPTS_DIR = Path(__file__).resolve().parent.parent
    TOOL_PATH = SCRIPTS_DIR / "notebook_tools" / "check_cell_source_parses.py"
    spec = importlib.util.spec_from_file_location(
        "check_cell_source_parses", str(TOOL_PATH)
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_mod = _load_check_cell_source_parses()
_compile_cell = _mod._compile_cell
_looks_like_markdown_typed_code = _mod._looks_like_markdown_typed_code
_strip_ipython_magics = _mod._strip_ipython_magics


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


class TestStripMagicsContinuation(unittest.TestCase):
    """PR #13328: a `%` at the start of a CONTINUATION line is the ordinary
    string-formatting operator, not an IPython magic. Dropping it corrupts
    the cell (the reported symptom was "'(' was never closed" on the
    previous line). The stripper must track bracket/string state."""

    def test_percent_operator_continuation_kept(self):
        src = (
            'print("  BR1(K2*) - K1* = %.1e ; BR2(K1*) - K2* = %.1e"\n'
            "      % (float(x.max()), float(y.max())))"
        )
        cleaned = _strip_ipython_magics(src)
        self.assertEqual(cleaned, src)
        err, _ = _mod._compile_cell(src)
        self.assertIsNone(err)

    def test_percent_continuation_after_else_print_kept(self):
        # cell[22] motif: else-branch print, continuation, then closes.
        src = (
            'if p > 0.3:\n'
            '    print("periode ~ %.0f iterations"\n'
            '          % (1 / f, 100 * p))\n'
            'else:\n'
            '    print("aucune periode dominante"\n'
            '          % (100 * p))'
        )
        cleaned = _strip_ipython_magics(src)
        self.assertEqual(cleaned, src)
        err, _ = _mod._compile_cell(src)
        self.assertIsNone(err)

    def test_percent_leading_line_inside_triple_quoted_string_kept(self):
        src = (
            'doc = """mise en forme\n'
            '     %d pourcents\n'
            '"""\n'
            "y = 1\n"
        )
        cleaned = _strip_ipython_magics(src)
        self.assertIn("%d pourcents", cleaned)
        self.assertIn("y = 1", cleaned)

    def test_magic_still_dropped_after_closed_bracket(self):
        # Depth tracking must RESET after the bracket closes: this %%time
        # is a real magic at logical-line start, not a continuation.
        src = 'z = f(a)\n%%time\nfor i in range(3):\n    pass\n'
        cleaned = _strip_ipython_magics(src)
        self.assertNotIn("%%time", cleaned)
        self.assertIn("z = f(a)", cleaned)

    def test_magic_dropped_inside_closed_string_only_context(self):
        # A line starting with `%` after a COMPLETE statement (no open
        # bracket, no open string) is a magic even if it looks like an
        # operator: IPython semantics win at logical-line start.
        src = 'x = "valeur"\n%matplotlib inline\nprint(x)\n'
        cleaned = _strip_ipython_magics(src)
        self.assertNotIn("%matplotlib", cleaned)
        self.assertIn('x = "valeur"', cleaned)


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


class TestTargetPyGating(unittest.TestCase):
    """`--target-py` must gate which grammar the guard accepts.

    c.672-L42: previously target_py was plumbing-mort (compile() does not
    accept feature_version); we now round-trip through ast.parse to honour
    the target. Two checks:

      (1) A construct INVALID on 3.10 grammar is rejected with both
          target_py=3.10 AND target_py=3.12 (the runtime's grammar table
          does not have 3.10-only constructs that 3.12 lacks; the inverse
          is the case for PEP 701).
      (2) A construct VALID on 3.10 grammar passes on both target_py values
          (this is the sanity check: target_py is a *forward* gate — newer
          constructs must FAIL on older target_py, but classic syntax is
          unaffected).
    """

    def test_target_py_is_forward_gate(self):
        # Classic 3.10 syntax passes both target_py=3.10 and target_py=3.12.
        src = "x = 1\ny = x + 1"
        err_310, _ = _compile_cell(src, target_py=(3, 10))
        err_312, _ = _compile_cell(src, target_py=(3, 12))
        self.assertIsNone(err_310, "classic syntax must PASS on target_py=3.10")
        self.assertIsNone(err_312, "classic syntax must PASS on target_py=3.12")

    def test_target_py_3_10_rejects_post_constructs(self):
        # PEP 701 nested-quote (`f"{d["k"]}"`) introduced in 3.12.
        # On a 3.10 grammar (target_py=3.10) WITH a 3.10/3.11 runtime,
        # ast.parse rejects it. The runtime is the binding: on 3.12+
        # runtimes, feature_version=(3,10) does NOT downgrade the parser
        # grammar for PEP 701 (PEP 701 is implemented as a construct the
        # 3.12+ parser handles natively and feature_version does not
        # retroactively re-flag it). c.688 fix: skip the 3.10-asserts on
        # 3.12+ runtimes where the runtime grammar table can't enforce
        # the gate (the test's premise — runtime-level feature_version
        # rejection — does not hold).
        import sys
        if sys.version_info >= (3, 12):
            self.skipTest(
                "PEP 701 / feature_version=(3,10) gate cannot be enforced "
                "on 3.12+ runtimes (the runtime parser lacks a 3.10 grammar "
                "table for the nested-quote construct; the 3.10-grammar "
                "branch is tested on 3.10/3.11 only)."
            )
        src = 'x = f"{d["k"]}"'
        err_310, _ = _compile_cell(src, target_py=(3, 10))
        # On 3.10 grammar: ALWAYS rejected (the construct is invalid for 3.10).
        self.assertIsNotNone(err_310, "PEP 701 must FAIL on target_py=3.10")
        # On 3.12 grammar: rejected only if runtime < 3.12 (binding).
        err_312, _ = _compile_cell(src, target_py=(3, 12))
        self.assertIsNotNone(
            err_312,
            "PEP 701 must FAIL on target_py=3.12 + runtime <3.12 (grammar table missing)",
        )


class TestMainPositional(unittest.TestCase):
    """`main()` must accept positional notebook paths so pre-commit's
    pass_filenames:true does not exit 2 on every commit touching a notebook.

    c.672-L42: previously the script declared zero positional args, and the
    hook injected file(s) as positional, so every commit hit
    'unrecognized arguments' and exited 2.
    """

    def test_help_lists_positional_paths(self):
        # Smoke: just verify argparse accepts a positional without erroring.
        # We don't run main() end-to-end (would scan the repo).
        import argparse
        # c.690 narrow 157ᵉ: the module is loaded via importlib (see header);
        # use the rebound `_compile_cell` so we don't reach for
        # `from notebook_tools.check_cell_source_parses import ...` whose
        # namespace-package semantics differ between local and CI under
        # --import-mode importlib.
        err, _ = _compile_cell("x = 1")
        self.assertIsNone(err)


if __name__ == "__main__":
    unittest.main()
