"""Unit tests for prover ``lean_utils.py`` degenerate-input guards + happy-path.

Loads ``lean_utils.py`` DIRECTLY by file path, bypassing
``prover/__init__.py`` (which cascades the ``agent_framework`` LLM stack,
absent on a bare CPU runner). The module's top level is stdlib-only
(``re`` / ``pathlib`` / ``typing``); the ``from .verifier import`` statements
are deferred inside the verifier-probing functions, so the module loads
cleanly anywhere. Mirrors ``tests/test_decomposition_regression.py``'s
file-path load.

These tests pin two things:
  1. **Guards (#7596-pattern, G.9):** every public ``filepath`` / ``content``
     entry point rejects ``None`` / non-str with a clear ``ValueError`` naming
     the offending argument — converting the OPAQUE ``TypeError`` ("NoneType
     has no len", "expected str") / ``AttributeError`` ("None.split") that an
     agent-generated None filepath/content previously produced into a
     diagnosable message. ``filepath`` params also reject empty (silent
     garbage: ``resolve_lake_module('')`` returned ``('C:\\', 'dev.CoursIA')``);
     ``content`` params allow ``''`` (an empty Lean file has 0 sorries).
  2. **Happy-path preservation:** the guard is pure defense-in-depth and must
     not change behavior for valid inputs (FX-6 word-bounded sorry counting,
     Lake-root resolution, comment stripping, sorry-block extraction).

Run from ``agent_tests/``:
    python -m pytest tests/test_lean_utils.py -q

See #1453 (prover co-evolution epic), See #7477 (prover harness forensic).
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

_spec = importlib.util.spec_from_file_location(
    "prover_lean_utils_under_test",
    ROOT / "prover" / "lean_utils.py",
)
lu = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(lu)


# A minimal .lean file used by the filepath-function happy-path tests.
_SAMPLE_LEAN = """\
theorem foo (n : Nat) : n = n := by
  sorry
"""


# ──────────────────────────────────────────────────────────────────────────
# Happy-path preservation — guards must not change valid-input behavior
# ──────────────────────────────────────────────────────────────────────────

class TestCountRealSorriesHappyPath:
    """FX-6 (#1453): word-bounded, comment-stripped sorry counting."""

    def test_single_sorry(self):
        assert lu.count_real_sorries("theorem foo := by sorry") == 1

    def test_empty_content_is_zero(self):
        # Empty string is a LEGITIMATE content input (empty file = 0 sorries).
        assert lu.count_real_sorries("") == 0

    def test_prose_sorry_in_comment_not_counted(self):
        # "sorry" mentioned in a line comment must NOT inflate the count.
        src = "-- sorry about the mess below\ntheorem foo := by sorry"
        assert lu.count_real_sorries(src) == 1

    def test_prose_sorry_in_block_comment_not_counted(self):
        src = "/- this sorry is prose -/\ntheorem foo := by sorry"
        assert lu.count_real_sorries(src) == 1

    def test_multiple_real_sorries(self):
        src = "theorem a := by sorry\ntheorem b := by sorry"
        assert lu.count_real_sorries(src) == 2


class TestStripLeanCommentsHappyPath:
    def test_keeps_newline_after_line_comment(self):
        assert lu.strip_lean_comments("-- a comment\nfoo") == "\nfoo"

    def test_empty_content(self):
        assert lu.strip_lean_comments("") == ""

    def test_nested_block_comments(self):
        # Lean allows nested /- -/ block comments.
        assert lu.strip_lean_comments("/- outer /- inner -/ still outer -/x") == "x"


class TestResolveLakeModuleHappyPath:
    def test_finds_lake_root_and_dotted_module(self, tmp_path):
        (tmp_path / "lakefile.lean").write_text("")
        pkg = tmp_path / "Conway" / "Life"
        pkg.mkdir(parents=True)
        f = pkg / "HashlifeCorrectness.lean"
        f.write_text("")
        root, module = lu.resolve_lake_module(str(f))
        assert root == str(tmp_path)
        assert module == "Conway.Life.HashlifeCorrectness"

    def test_fallback_legacy_depth2_when_no_lakefile(self, tmp_path):
        # No lakefile anywhere up the tree -> legacy depth-2 derivation.
        pkg = tmp_path / "Foo"
        pkg.mkdir(parents=True)
        f = pkg / "Nim.lean"
        f.write_text("")
        root, module = lu.resolve_lake_module(str(f))
        assert module == "Foo.Nim"


class TestClassifyDefinitionsHappyPath:
    def test_classifies_inductive_and_def(self, tmp_path):
        f = tmp_path / "M.lean"
        f.write_text(
            "inductive Nat where\n"
            "  | zero\n"
            "def inc (n : Nat) := Nat.zero\n"
        )
        defs = lu.classify_definitions(str(f))
        kinds = {d["name"]: d["kind"] for d in defs}
        assert kinds.get("Nat") == "inductive"
        assert kinds.get("inc") == "def"


class TestExtractSorryBlockHappyPath:
    def test_returns_sorry_context(self, tmp_path):
        f = tmp_path / "P.lean"
        f.write_text(_SAMPLE_LEAN)
        block = lu.extract_sorry_block(str(f), 2)
        assert "error" not in block
        assert block["sorry_line"] == 2
        assert "sorry" in block["sorry_text"]

    def test_out_of_range_line_returns_error_dict(self, tmp_path):
        f = tmp_path / "P.lean"
        f.write_text(_SAMPLE_LEAN)
        block = lu.extract_sorry_block(str(f), 99)
        assert "error" in block  # graceful, not an exception


class TestSorryIsInStatementHappyPath:
    def test_sorry_in_body_returns_false(self):
        src = "theorem foo : True := by\n  sorry"
        assert lu.sorry_is_in_statement(src, 2) is False

    def test_empty_content_returns_false(self):
        assert lu.sorry_is_in_statement("", 1) is False


# ──────────────────────────────────────────────────────────────────────────
# Guards — degenerate inputs raise clear ValueError (#7596-pattern)
# ──────────────────────────────────────────────────────────────────────────

class TestContentGuardsRejectNone:
    """content params reject None / non-str but ALLOW empty string."""

    @pytest.mark.parametrize("fn", [
        lu.count_real_sorries,
        lu.strip_lean_comments,
        lu.sorry_is_in_statement,
    ])
    def test_none_rejected(self, fn):
        with pytest.raises(ValueError, match="expected str"):
            if fn is lu.sorry_is_in_statement:
                fn(None, 1)
            else:
                fn(None)

    def test_non_str_rejected(self):
        with pytest.raises(ValueError, match="expected str"):
            lu.count_real_sorries(123)


class TestFilepathGuardsRejectNoneAndEmpty:
    """filepath params reject None / non-str / empty (empty = silent garbage)."""

    FILEPATH_FNS = [
        ("resolve_lake_module", lambda: lu.resolve_lake_module(None)),
        ("extract_sorry_block", lambda: lu.extract_sorry_block(None, 1)),
        ("classify_definitions", lambda: lu.classify_definitions(None)),
        ("extract_hypotheses", lambda: lu.extract_hypotheses(None, 1)),
        ("extract_local_lemmas", lambda: lu.extract_local_lemmas(None)),
        ("get_goal_state", lambda: lu.get_goal_state(None, 1)),
        ("is_true_placeholder_goal", lambda: lu.is_true_placeholder_goal(None, 1)),
        ("is_honest_sorry", lambda: lu.is_honest_sorry(None, 1)),
        ("verify_sorry_replacement", lambda: lu.verify_sorry_replacement(None, 1, "trivial")),
    ]

    @pytest.mark.parametrize("name,call", FILEPATH_FNS)
    def test_none_rejected(self, name, call):
        with pytest.raises(ValueError, match="filepath: expected str"):
            call()

    @pytest.mark.parametrize("name,call", [
        ("resolve_lake_module", lambda: lu.resolve_lake_module("")),
        ("extract_sorry_block", lambda: lu.extract_sorry_block("", 1)),
        ("classify_definitions", lambda: lu.classify_definitions("")),
        ("extract_hypotheses", lambda: lu.extract_hypotheses("", 1)),
        ("extract_local_lemmas", lambda: lu.extract_local_lemmas("")),
        ("get_goal_state", lambda: lu.get_goal_state("", 1)),
    ], ids=lambda x: x if isinstance(x, str) else "")
    def test_empty_rejected(self, name, call):
        # Empty filepath was previously silent garbage (resolve_lake_module('')
        # returned ('C:\\', 'dev.CoursIA')) — now a clear ValueError.
        with pytest.raises(ValueError, match="non-empty str"):
            call()


class TestProbeRelativePathGuards:
    def test_none_filepath_rejected(self):
        with pytest.raises(ValueError, match="filepath: expected str"):
            lu.probe_relative_path(None, ".", "_X.lean")

    def test_none_project_dir_rejected(self):
        with pytest.raises(ValueError, match="project_dir: expected str"):
            lu.probe_relative_path("x.lean", None, "_X.lean")

    def test_none_tmp_name_rejected(self):
        with pytest.raises(ValueError, match="tmp_name: expected str"):
            lu.probe_relative_path("x.lean", ".", None)


class TestVerifySorryReplacementReplacementGuard:
    def test_none_replacement_rejected(self):
        # filepath is guarded first; use a valid-looking path to reach the
        # replacement guard.
        with pytest.raises(ValueError, match="replacement: expected str"):
            lu.verify_sorry_replacement("x.lean", 1, None)


# ──────────────────────────────────────────────────────────────────────────
# Implicit-sorry detection (Epic #1500, c.1301+209)
# ──────────────────────────────────────────────────────────────────────────
#
# Founding incident: BG2 GaleShapley L98 (2026-05-23) reported "SUCCESS
# sorry 1→0" but the prover had replaced ``sorry`` with ``apply?`` — the
# tactic failed silently and compiled as an implicit ``sorry``. Lake emits
# ``declaration uses 'sorry'`` for these. ``count_real_sorries`` reads
# source text only and misses the warning; the new ``count_implicit_sorries``
# reads the build output and closes the gap.

class TestCountImplicitSorries:
    """Epic #1500: parse ``declaration uses 'sorry'`` warnings from lake build."""

    def test_none_yields_zero(self):
        # No build ran — no warning possible.
        assert lu.count_implicit_sorries(None) == 0

    def test_empty_string_yields_zero(self):
        assert lu.count_implicit_sorries("") == 0

    def test_modern_wording_single_occurrence(self):
        # The current Lake wording: ``declaration uses 'sorry'`` (single quotes).
        out = "info: myfile.lean:42: declaration uses 'sorry'"
        assert lu.count_implicit_sorries(out) == 1

    def test_modern_wording_multiple_occurrences(self):
        # Two warnings on two different lines.
        out = (
            "info: myfile.lean:42: declaration uses 'sorry'\n"
            "info: myfile.lean:73: declaration uses 'sorry'\n"
        )
        assert lu.count_implicit_sorries(out) == 2

    def test_legacy_wording_fallback(self):
        # Older Lake wording — kept as a fallback for robustness.
        out = "warning: myfile.lean:42: uses 'sorry'"
        assert lu.count_implicit_sorries(out) == 1

    def test_unrelated_warning_ignored(self):
        # Sanity: a warning that does NOT mention sorry yields 0.
        out = "info: myfile.lean:42: some unrelated warning\n"
        assert lu.count_implicit_sorries(out) == 0

    def test_pure_sorry_string_ignored(self):
        # Bare "sorry" without "declaration uses" or "uses" prefix = noise.
        out = "the tactic emitted sorry at line 42\n"
        assert lu.count_implicit_sorries(out) == 0

    def test_real_sorry_prose_ignored(self):
        # Lake output mentioning "sorry" in plain prose (no warning form) = 0.
        out = "warning: a sorried proof will fail in subsequent steps\n"
        assert lu.count_implicit_sorries(out) == 0

    def test_double_quotes_variant(self):
        # Some Lake versions emit ``declaration uses "sorry"`` with double quotes.
        out = 'info: myfile.lean:42: declaration uses "sorry"'
        assert lu.count_implicit_sorries(out) == 1


class TestCountSorriesCombined:
    """Epic #1500: combined REAL + IMPLICIT count for full coverage."""

    def test_textual_only(self):
        # No build output → combined == textual (no false positive).
        src = "theorem foo := by sorry\n"
        assert lu.count_sorries_combined(src, None) == 1
        assert lu.count_sorries_combined(src, "") == 1

    def test_textual_and_implicit(self):
        # Source has 1 textual sorry, build output has 1 implicit warning
        # (a different declaration): combined = 2.
        src = "theorem foo := by sorry\n"
        out = "info: bar.lean:73: declaration uses 'sorry'\n"
        assert lu.count_sorries_combined(src, out) == 2

    def test_textual_zero_implicit_one_is_false_positive(self):
        # The founding scenario: source has 0 textual sorry, build output
        # has 1 implicit warning → combined = 1 (this is the FP the prover
        # would have reported as success without this fix).
        src = "theorem foo := by apply?\n"  # no textual "sorry"
        out = "info: foo.lean:1: declaration uses 'sorry'\n"
        assert lu.count_sorries_combined(src, out) == 1

    def test_both_zero_is_clean(self):
        # No textual sorry, no build warning = 0 (clean proof).
        src = "theorem foo := by rfl\n"
        out = "info: foo.lean:1: ok\n"
        assert lu.count_sorries_combined(src, out) == 0
