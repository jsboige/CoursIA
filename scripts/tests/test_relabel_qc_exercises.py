"""Unit tests for relabel_qc_exercises pure helpers.

Covers the three pure (I/O-free) functions used by the QC exercise-relabel
pipeline:
  - ``_to_text``           : normalize cell source (str | list[str]) to text.
  - ``get_exercice_num``   : extract the trailing integer of a
                             ``### Exercice N`` / ``### Exemple guide N`` heading.
  - ``_replace_in_source`` : find-replace ``Exercice <old>`` -> ``Exercice <new>``
                             (and ``Exemple guide``), preserving the str|list
                             container type.

The notebook-iteration entry points (``audit_qc``, ``relabel_notebook``,
``main``) do filesystem I/O and are out of scope for unit tests; they are
exercised indirectly by the relabel PRs (#2660/#2669/#2672).

Run with: pytest scripts/tests/test_relabel_qc_exercises.py -v
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from relabel_qc_exercises import (  # noqa: E402
    _replace_in_source,
    _to_text,
    get_exercice_num,
)


# ---------------------------------------------------------------------------
# _to_text
# ---------------------------------------------------------------------------


class TestToText:
    def test_str_passthrough(self):
        assert _to_text("### Exercice 1") == "### Exercice 1"

    def test_list_joined(self):
        # Notebook cell source is often a list of lines.
        assert _to_text(["### Exercice 1\n", "body line"]) == "### Exercice 1\nbody line"

    def test_empty_list(self):
        assert _to_text([]) == ""

    def test_empty_str(self):
        assert _to_text("") == ""


# ---------------------------------------------------------------------------
# get_exercice_num
# ---------------------------------------------------------------------------


class TestGetExerciceNum:
    def test_exercice_heading(self):
        assert get_exercice_num("### Exercice 5") == 5

    def test_exemple_guide_heading(self):
        assert get_exercice_num("### Exemple guide 12") == 12

    def test_case_insensitive(self):
        # EXERCICE_PAT is compiled with re.IGNORECASE.
        assert get_exercice_num("### exercice 3") == 3
        assert get_exercice_num("### EXEMPLE GUIDE 7") == 7

    def test_multi_digit(self):
        assert get_exercice_num("### Exercice 42") == 42

    def test_trailing_text_after_number(self):
        # Regex is (prefix) \d+ with no end anchor; trailing text is allowed.
        assert get_exercice_num("### Exercice 4 — Titre du sujet") == 4

    def test_no_heading_returns_none(self):
        assert get_exercice_num("Some prose without any heading") is None

    def test_number_in_body_not_heading(self):
        # A bare "exercise 5" in prose must NOT match (requires ### prefix).
        assert get_exercice_num("See exercise 5 below for details.") is None

    def test_heading_without_keyword_returns_none(self):
        assert get_exercice_num("### Section 5 - introduction") is None

    def test_list_source_uses_first_match(self):
        # When source is a list, the whole text is searched; first match wins.
        assert get_exercice_num(["### Exercice 7\n", "body"]) == 7

    def test_empty_source_returns_none(self):
        assert get_exercice_num("") is None
        assert get_exercice_num([]) is None

    def test_hash_level_not_anchored(self):
        # The pattern is NOT anchored at start-of-string/line: '###' matches
        # as a substring inside '####' (h4). Documenting current behavior —
        # an h4 'Exercice' heading is still detected. This is a spec looseness
        # rather than a bug (relabeling an h4 exercise heading is harmless),
        # but pinning it here so any future anchoring change is caught.
        assert get_exercice_num("#### Exercice 9") == 9


# ---------------------------------------------------------------------------
# _replace_in_source
# ---------------------------------------------------------------------------


class TestReplaceInSource:
    def test_basic_str_replace(self):
        out = _replace_in_source("### Exercice 1", 1, 4)
        assert out == "### Exercice 4"

    def test_exemple_guide_also_replaced(self):
        out = _replace_in_source("### Exemple guide 1", 1, 4)
        assert out == "### Exemple guide 4"

    def test_both_prefixes_in_same_source(self):
        out = _replace_in_source("### Exercice 1\n### Exemple guide 1", 1, 4)
        assert out == "### Exercice 4\n### Exemple guide 4"

    def test_no_match_returns_unchanged(self):
        out = _replace_in_source("### Exercice 5", 99, 1)
        assert out == "### Exercice 5"

    def test_other_numbers_preserved(self):
        # Replacing 1 -> 4 must leave an unrelated "Exercice 2" untouched.
        out = _replace_in_source("### Exercice 1\n### Exercice 2", 1, 4)
        assert out == "### Exercice 4\n### Exercice 2"

    def test_list_source_preserved(self):
        # When the input is a list[str], the output must also be a list[str].
        src = ["### Exercice 1\n", "body"]
        out = _replace_in_source(src, 1, 4)
        assert isinstance(out, list)
        assert out == ["### Exercice 4\n", "body"]

    def test_noop_when_old_equals_new(self):
        out = _replace_in_source("### Exercice 1", 1, 1)
        assert out == "### Exercice 1"

    def test_str_round_trips_through_text(self):
        # The relabel pipeline reads cell["source"], replaces, writes back.
        # A str input must yield a str output (not accidentally a list).
        out = _replace_in_source("### Exercice 1", 1, 5)
        assert isinstance(out, str)

    @pytest.mark.xfail(
        reason=(
            "KNOWN BUG (boundary): str.replace('Exercice 1', ...) matches the "
            "'Exercice 1' prefix inside 'Exercice 12', corrupting it to "
            "'Exercice 92'. get_exercice_num uses \\d+ (correct) but "
            "_replace_in_source uses naive str.replace. Fix = regex with a "
            "non-digit boundary (e.g. r'Exercice 1(?=\\D|$)'). Tracked for a "
            "separate fix PR — kept here as non-vacuous regression bait: if "
            "someone fixes the bug, this xfail flips to XPASS and the marker "
            "must be removed."
        ),
        strict=True,
    )
    def test_multidigit_boundary_bug(self):
        # 'Exercice 1' must NOT match the prefix of 'Exercice 12'.
        out = _replace_in_source("### Exercice 1\n### Exercice 12", 1, 9)
        # Correct behavior:
        assert out == "### Exercice 9\n### Exercice 12"
        # Current (buggy) behavior would be '### Exercice 9\n### Exercice 92'.
