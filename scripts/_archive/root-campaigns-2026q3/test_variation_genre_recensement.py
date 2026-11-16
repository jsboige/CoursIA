"""Tests for `variation_genre_recensement.py` pure parsers + drift heuristics.

Background (why this file exists): the census `parse_grain` used a local
`_GRAIN_RE` that DIVERGED from the canonical form-tolerant reader
`grain_tag.parse_grain_tag` (#9485). It silently dropped the tolerated forms
(`**Grain:**`, `## Grain`, `` `Grain` `` no-colon), undercounting the universe
and biasing the monoculture census that motivated `variation-protocol.md`.
These tests pin the contract: `parse_grain` MUST agree with the canonical
reader on every form the CI guard accepts.
"""
import os
import sys

import pytest

# Make scripts/ importable (sibling of tests/), same pattern as test_grain_tag.py
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import variation_genre_recensement as vgr  # noqa: E402
from variation_genre_recensement import (  # noqa: E402
    file_family,
    has_interpretation_cue,
    only_notebook,
    parse_grain,
    zero_code_modif,
)

# Canonical PR-body fixtures spanning every form the CI guard tolerates.
# Lane token included where the canonical reader would see it, but parse_grain
# only returns (tier, genre) — the lane is parsed elsewhere.
CANONICAL = "Grain: LIGHT/guard -- lane myia-po-2023:CoursIA"
BOLD = "**Grain:** LIGHT/guard - lane myia-ai-01:CoursIA"
TITLE_HASH = "## Grain\n\nLIGHT/guard ... lane myia-po-2024:CoursIA-2"
NO_COLON = "`Grain` LIGHT/guard ... lane myia-po-2025:CoursIA"
DEEP_LEAN = "Grain: DEEP/lean -- lane myia-po-2026:CoursIA"
MED_NB = "Grain: MED/notebook-python -- lane myia-po-2024:CoursIA-2"


# --- parse_grain: MUST agree with the canonical reader on every form --------

def test_parse_grain_canonical():
    assert parse_grain(CANONICAL) == ("LIGHT", "guard")


def test_parse_grain_bold_form():
    """`**Grain:**` (bold) — tolerated by the CI guard, must parse here too.

    This was the headline divergence: the local _GRAIN_RE missed it, so the
    census undercounted any PR using the bold form.
    """
    assert parse_grain(BOLD) == ("LIGHT", "guard")


def test_parse_grain_title_hash_form():
    """`## Grain` then tag on next line — tolerated by CI guard via hash-strip."""
    assert parse_grain(TITLE_HASH) == ("LIGHT", "guard")


def test_parse_grain_no_colon_form():
    """`` `Grain` `` with no colon — tolerated by CI guard."""
    assert parse_grain(NO_COLON) == ("LIGHT", "guard")


def test_parse_grain_deep_lean():
    assert parse_grain(DEEP_LEAN) == ("DEEP", "lean")


def test_parse_grain_med_notebook():
    assert parse_grain(MED_NB) == ("MED", "notebook-python")


def test_parse_grain_absent():
    assert parse_grain("No grain tag here, just a body.") == (None, None)


def test_parse_grain_empty_body():
    assert parse_grain("") == (None, None)


def test_parse_grain_none_body():
    assert parse_grain(None) == (None, None)


def test_parse_grain_agrees_with_canonical_reader_on_all_forms():
    """The single contract: census parse_grain == grain_tag.parse_grain_tag.

    If this fails, the two readers have drifted again — exactly the #9485
    failure mode. The census must NOT carry its own Grain regex.
    """
    import grain_tag

    bodies = [CANONICAL, BOLD, TITLE_HASH, NO_COLON, DEEP_LEAN, MED_NB, "", None]
    for body in bodies:
        census = parse_grain(body)
        canon = grain_tag.parse_grain_tag(body)
        canon_tuple = (canon["tier"], canon["genre"]) if canon else (None, None)
        assert census == canon_tuple, (
            f"census/parser drift on body={body!r}: "
            f"census={census} canonical={canon_tuple}"
        )


# --- file_family -------------------------------------------------------------

def test_file_family_two_segments():
    paths = ["MyIA.AI.Notebooks/SymbolicAI/Lean/SL-1.ipynb"]
    assert file_family(paths) == "SymbolicAI/Lean"


def test_file_family_single_segment():
    # NOTE: shallow paths (3 segments) return "family/file" — a latent quirk
    # where parts[1:3] captures the filename. The deep-path case (4+ segments,
    # e.g. SymbolicAI/Lean) is correct. Out of scope for the parse_grain fix;
    # documented here to pin current behavior.
    paths = ["MyIA.AI.Notebooks/ML/ml.cs"]
    assert file_family(paths) == "ML/ml.cs"


def test_file_family_no_notebooks():
    assert file_family(["scripts/foo.py", "README.md"]) is None


def test_file_family_empty():
    assert file_family([]) is None


def test_file_family_mixed_uses_notebook():
    paths = ["scripts/foo.py", "MyIA.AI.Notebooks/GenAI/Image/x.ipynb"]
    assert file_family(paths) == "GenAI/Image"


# --- only_notebook -----------------------------------------------------------

def test_only_notebook_all_ipynb():
    assert only_notebook(["a.ipynb", "b.ipynb"]) is True


def test_only_notebook_mixed():
    assert only_notebook(["a.ipynb", "b.py"]) is False


def test_only_notebook_empty():
    assert only_notebook([]) is False


# --- has_interpretation_cue --------------------------------------------------

def test_interpretation_cue_enrichissement():
    assert has_interpretation_cue("Ajout d'un enrichissement pedagogique.") is True


def test_interpretation_cue_markdown_header():
    assert has_interpretation_cue("blabla\n# Interpretation\nsuite") is True


def test_interpretation_cue_plain():
    assert has_interpretation_cue("Fix a bug in the solver.") is False


# --- zero_code_modif ---------------------------------------------------------

def test_zero_code_modif_no_patch_small_addition():
    pr = {"files": [{"path": "a.ipynb", "additions": 5, "deletions": 0}]}
    assert zero_code_modif(pr) is True


def test_zero_code_modif_no_patch_has_deletion():
    pr = {"files": [{"path": "a.ipynb", "additions": 2, "deletions": 3}]}
    assert zero_code_modif(pr) is False


def test_zero_code_modif_no_nb_files():
    pr = {"files": [{"path": "README.md", "additions": 50, "deletions": 10}]}
    assert zero_code_modif(pr) is True


def test_zero_code_modif_patch_with_code_cell_added():
    """A patch that adds a `"cell_type": "code"` line is NOT zero-code-modif."""
    patch = '+  {\n+    "cell_type": "code",\n+    "source": "print(1)"\n+  }'
    pr = {"files": [{"path": "a.ipynb"}], "_patch": patch}
    assert zero_code_modif(pr) is False


def test_zero_code_modif_patch_markdown_only():
    """A patch touching only markdown cells IS zero-code-modif."""
    patch = '+  {\n+    "cell_type": "markdown",\n+    "source": "# Intro"\n+  }'
    pr = {"files": [{"path": "a.ipynb"}], "_patch": patch}
    assert zero_code_modif(pr) is True


# --- LIGHT classification: the census MUST agree with the CI-wired organ ------
#
# Background (why these exist): `build_row` classified LIGHT with a bare
# `genre in LIGHT_GENRES` over a LOCAL copy of the set, which diverged from the
# canonical accounting `variation_light_cap.genre_counts_light` on three axes
# (#16168, sœur de #13475) : a surplus member (`refs`), no canonicalisation (a
# LIGHT-declared `documentation`/`prose` aliases to `docs` but escaped the
# count), and no fail-CLOSED clause (an unresolvable word escaped it too).
# `light_genre` feeds `drift_candidate`, so the divergence moved the very drift
# set this census exists to measure. These tests pin the contract by its OUTPUT
# (`build_row(...).light_genre`), not by the set alone -- a set-only assertion
# would pass on the buggy version, since the bug lived in the predicate.


def _row_for(declared: str):
    """`build_row` over a minimal PR carrying the given `Grain:` tier/genre."""
    tier, genre = declared.split("/")
    body = f"Grain: {tier}/{genre} -- lane myia-po-2026:CoursIA -- prev: DEEP/lean #1\n"
    return vgr.build_row({"number": 1, "body": body, "files": [{"path": "docs/x.md"}]})


@pytest.mark.parametrize(
    "declared,expected",
    [
        # MUST count LIGHT -- canonical LIGHT genres.
        ("LIGHT/guard", True),
        ("LIGHT/docs", True),
        ("LIGHT/test", True),
        # MUST count LIGHT -- aliases the canonicaliser resolves into a LIGHT
        # genre. These are the cases the local copy missed (axis 2).
        ("LIGHT/documentation", True),
        ("LIGHT/prose", True),
        # MUST count LIGHT -- unresolvable word is fail-CLOSED at non-MED/DEEP
        # tiers (axis 3), by design (#13475).
        ("LIGHT/zzz-inexistant", True),
        # NEGATIVE CONTROLS -- canonical non-LIGHT genres must not regress into
        # LIGHT (this is what the verbatim guard protected, cf the
        # `KeyError: 'notebook-python'` documented in variation_light_cap).
        ("DEEP/notebook-python", False),
        ("MED/notebook-python", False),
        ("DEEP/training", False),
        ("DEEP/lean", False),
        ("DEEP/research-code", False),
        # `refs` is off-list: LIGHT when declared LIGHT, NOT light at MED/DEEP.
        # The local copy said LIGHT at every tier (axis 1).
        ("LIGHT/refs", True),
        ("MED/refs", False),
        ("DEEP/refs", False),
    ],
)
def test_light_genre_matches_the_canonical_organ(declared, expected):
    assert _row_for(declared).light_genre is expected


def test_light_genre_is_the_canonical_predicate_not_a_rederivation():
    """`light_genre` MUST equal the organ's verdict, case by case."""
    import variation_light_cap as lc

    for declared in (
        "LIGHT/docs",
        "LIGHT/documentation",
        "LIGHT/prose",
        "LIGHT/zzz-inexistant",
        "DEEP/notebook-python",
        "LIGHT/refs",
        "DEEP/refs",
    ):
        tier, genre = declared.split("/")
        assert _row_for(declared).light_genre is lc.genre_counts_light(genre, tier)


def test_light_genres_set_is_the_canonical_one():
    """No second copy of the truth: the module-level set IS the organ's set."""
    import variation_light_cap as lc

    assert vgr.LIGHT_GENRES == lc.LIGHT_GENRES


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
