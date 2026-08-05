"""Unit tests for scripts/variation_tags.py (shared Grain: tag extractor).

Issue #9485: the cap organe (`variation_light_cap.py`) and the guard workflow
(`variation-tag-guard.yml`) BOTH extract {tier, genre, lane} from PR bodies,
but each had its own parser. The two parsers disagreed on 38 percent of
merges (13/34 on the 2026-08-05 lot) because:

  (1) `## Grain` header form -- the tag is a multi-line block, header-form,
      with TIER/GENRE on subsequent lines.
  (2) `Grain` without colon -- the inline form omits the `:`.
  (3) Decoration like `#` (header) and `>` (blockquote) was not stripped.
  (4) `lane` is on a separate line, sometimes wrapped in `**Lane** :` -- the
      guard's regex was anchored to the Grain line, losing the lane.

These tests pin the SHARED extractor on every form observed in the wild.
Run: `python -m pytest scripts/tests/test_variation_tags.py`.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import variation_tags as vt  # noqa: E402


# --- constraint (1): `## Grain` / `### Grain` header form ----------------

# The canonical offender -- PR #9458, the example pasted in #9485.
HEADER_FORM_BODY = """\
## Grain
`MED/tooling (#8056 cost-honesty / under-declaration correction)` -- lane `myia-po-2023:CoursIA` -- prev: `MED/tooling #9457`.
"""


def test_header_form_closes_tag_misclass():
    """The motivating case: #9458's body is `## Grain` + backticked tag."""
    g = vt.extract_tag(HEADER_FORM_BODY)
    assert g is not None, "header-form `## Grain` rejected (see #9485)"
    assert g["tier"] == "MED"
    assert g["genre"] == "tooling"
    assert g["lane"] == "myia-po-2023:CoursIA"


def test_header_form_three_levels():
    """Both `## Grain` and `### Grain` work, plus `# Grain` (any level)."""
    body_d3 = "### Grain\nLIGHT/guard -- lane myia-po-2024:CoursIA-2"
    body_d1 = "# Grain\nDEEP/lean -- lane myia-ai-01:CoursIA"
    assert vt.extract_tag(body_d3)["tier"] == "LIGHT"
    assert vt.extract_tag(body_d1)["tier"] == "DEEP"


def test_header_form_without_colon():
    """Header line is `## Grain` (most common) or `## Grain:` (rare)."""
    body = "## Grain\nMED/lean -- lane myia-po-2026:CoursIA"
    assert vt.extract_tag(body)["genre"] == "lean"


def test_header_form_stops_at_next_section():
    """Recollation must NOT swallow the next paragraph's content.

    The next section (any header level) ends the Grain block. The TIER
    word on the next line must NOT be mistakenly captured as the TIER of
    the Grain tag.
    """
    body = (
        "## Grain\n"
        "MED/tooling -- lane myia-po-2023:CoursIA\n"
        "\n"
        "## Suite\n"
        "DEEP/lean -- lane myia-ai-01:CoursIA\n"
    )
    g = vt.extract_tag(body)
    assert g["tier"] == "MED", "next section's TIER leaked into Grain block"
    assert g["lane"] == "myia-po-2023:CoursIA"


def test_header_form_no_content_returns_none():
    """A `## Grain` header with no following content is malformed."""
    body = "## Grain\n"
    g = vt.extract_tag(body)
    # When the recollation finds no content, the tag is malformed. The
    # organe returns None -- missing in the wild, same as no tag at all.
    assert g is None


# --- constraint (2): `Grain` without colon --------------------------------

def test_inline_form_without_colon():
    """`Grain DEEP/lean` (no colon) is equivalent to `Grain: DEEP/lean`."""
    body = "Grain DEEP/lean -- lane myia-po-2023:CoursIA"
    g = vt.extract_tag(body)
    assert g is not None
    assert g["tier"] == "DEEP"
    assert g["genre"] == "lean"


def test_inline_form_with_colon_still_works():
    """Non-regression: the existing colon form continues to match."""
    body = "Grain: DEEP/lean -- lane myia-po-2023:CoursIA"
    assert vt.extract_tag(body)["tier"] == "DEEP"


def test_inline_form_bold_space_colon_space():
    """`**Grain** : DEEP/lean` (bold + space-colon-space, observed #9477/#9479).

    The same shape that previously challenged the lane extractor (`**Lane** :`)
    also appears for the grain label: `**Grain** : DEEP/...`. The widened
    regex (constraint #4 sibling) accepts both. Without this, the #9477 and
    #9479 wave would stay unattributed.
    """
    body = "**Grain** : DEEP/research-code -- bridge #2 -- lane myia-po-2025:CoursIA-2"
    g = vt.extract_tag(body)
    assert g is not None
    assert g["tier"] == "DEEP"
    assert g["genre"] == "research-code"
    assert g["lane"] == "myia-po-2025:CoursIA-2"


# --- constraint (3): `#` (header) and `>` (blockquote) decoration ---------

def test_blockquote_prefix():
    """A `> Grain: DEEP/lean` in a blockquote is read normally."""
    body = "> Grain: DEEP/lean -- lane myia-po-2023:CoursIA"
    g = vt.extract_tag(body)
    assert g is not None
    assert g["tier"] == "DEEP"


def test_list_bullet_prefix():
    """A `- Grain: ...` in a list item is read normally."""
    body = "- Grain: DEEP/lean -- lane myia-po-2023:CoursIA"
    assert vt.extract_tag(body)["tier"] == "DEEP"


def test_astérisque_top_prefix():
    """A `* Grain: ...` in a list item is read normally."""
    body = "* Grain: DEEP/lean -- lane myia-po-2023:CoursIA"
    assert vt.extract_tag(body)["tier"] == "DEEP"


# --- constraint (4): `lane` independently of position --------------------

# Reference: PR #9480 used `**Lane** :` on its own line.
BODY_LANE_BOLD_SEPARATE = (
    "**Grain:** `LIGHT/refs` . **Lane** : `myia-po-2024:CoursIA-2`"
)


def test_lane_bold_independent_line():
    """`**Lane** :` on a separate part of the body is still parsed."""
    g = vt.extract_tag(BODY_LANE_BOLD_SEPARATE)
    assert g is not None
    assert g["lane"] == "myia-po-2024:CoursIA-2"
    assert g["tier"] == "LIGHT"


def test_lane_label_no_colon():
    """`lane myia-po-2024:CoursIA-2` (no colon) is read normally."""
    body = "Grain: LIGHT/guard . lane myia-po-2024:CoursIA-2"
    assert vt.extract_tag(body)["lane"] == "myia-po-2024:CoursIA-2"


def test_lane_capitalized():
    """`Lane:` (capital L) is read normally."""
    body = "Grain: LIGHT/guard . Lane: myia-po-2024:CoursIA-2"
    assert vt.extract_tag(body)["lane"] == "myia-po-2024:CoursIA-2"


# --- substance: bodies genuinely without TIER/GENRE remain missing -------

def test_no_tag_at_all_returns_none():
    """A body without any Grain: tag is None -- substance > form."""
    assert vt.extract_tag("This PR fixes a bug, no tag.") is None


def test_grain_word_without_tier_returns_none():
    """`Grain` as a prose word (not a tag) is NOT a tag -- no slash follows."""
    body = "Grain storage is the bottleneck. Nothing else here."
    assert vt.extract_tag(body) is None


def test_grain_without_lane_extracts_tier_genre():
    """Tier and genre are extracted; lane is None if absent (substance preserved)."""
    body = "Grain: LIGHT/guard"
    g = vt.extract_tag(body)
    assert g is not None
    assert g["tier"] == "LIGHT"
    assert g["genre"] == "guard"
    assert g["lane"] is None


# --- normalization (the building block) -----------------------------------

def test_normalize_empty():
    assert vt.normalize_body("") == ""


def test_normalize_strips_header_markers():
    """`#`, `##`, `###` line prefixes are stripped without residue."""
    assert vt.normalize_body("## Grain") == "Grain"
    assert vt.normalize_body("# Grain") == "Grain"
    assert vt.normalize_body("### Grain") == "Grain"


def test_normalize_strips_blockquote_markers():
    assert vt.normalize_body("> Grain: DEEP/lean") == "Grain: DEEP/lean"


def test_normalize_strips_inline_noise():
    """Asterisks and backticks are removed mid-line."""
    assert vt.normalize_body("**Grain:** `DEEP/lean`") == "Grain: DEEP/lean"


def test_normalize_preserves_internal_text():
    """The decorator strip only removes the noise; prose content is preserved."""
    body = "Grain: DEEP/lean -- lane x:y. The rest of the body is unchanged."
    assert vt.normalize_body(body) == body


# --- check_conformity (the guard's interface) ------------------------------

def test_check_conformity_ok():
    """A fully tagged body is `ok: true` with no defects."""
    r = vt.check_conformity("Grain: DEEP/lean -- lane myia-po-2023:CoursIA")
    assert r["ok"] is True
    assert r["defects"] == []
    assert r["grain"]["tier"] == "DEEP"


def test_check_conformity_missing():
    """Body without any tag is `variation-tag-missing`."""
    r = vt.check_conformity("No tag here, just prose.")
    assert r["ok"] is False
    assert "variation-tag-missing" in r["defects"]
    assert r["grain"] is None


def test_check_conformity_malformed_tier():
    """Tier outside the §1 enumeration is `variation-tag-malformed`."""
    r = vt.check_conformity("Grain: BALONEY/lean -- lane myia-po-2023:CoursIA")
    assert r["ok"] is False
    assert "variation-tag-malformed" in r["defects"]


def test_check_conformity_offlist_genre():
    """Genre outside the §1 enumeration is `variation-tag-genre-offlist`."""
    r = vt.check_conformity("Grain: DEEP/exotic -- lane myia-po-2023:CoursIA")
    assert r["ok"] is False
    assert "variation-tag-genre-offlist" in r["defects"]


def test_check_conformity_lane_missing():
    """Tag present but no lane -> `variation-tag-lane-missing`."""
    r = vt.check_conformity("Grain: DEEP/lean -- prose without lane")
    assert r["ok"] is False
    assert "variation-tag-lane-missing" in r["defects"]


def test_check_conformity_header_form_ok():
    """The header form is `ok: true` when the content is well-formed."""
    r = vt.check_conformity(HEADER_FORM_BODY)
    assert r["ok"] is True, f"unexpected defects: {r['defects']}"
    assert r["grain"]["lane"] == "myia-po-2023:CoursIA"


# --- list of §1 accepted genres (for cross-validation) -------------------

def test_grain_genres_includes_documented_set():
    """The canonical set is pinned: any addition must be a deliberate edit."""
    expected = {
        "lean", "qc", "training", "genai",
        "notebook-python", "notebook-dotnet",
        "docs", "guard", "refactor", "ledger",
        "readme", "test",
        "tooling", "research-code",
    }
    assert vt.GRAIN_GENRES == expected
