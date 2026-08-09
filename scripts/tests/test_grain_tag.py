#!/usr/bin/env python3
"""Unit tests for grain_tag.py -- the shared Grain-tag extractor (fix #9485).

One test per recognised form (#9485 acceptance: "un test par forme reconnue"),
plus the substance guard: a body with no <TIER>/<GENRE> anywhere MUST still
return None -- the tolerance is on PRESENTATION, not on substance. Run:
    python -m pytest scripts/tests/test_grain_tag.py

#9861 -- short-header trio (Quoi/Preuve/Perimetre). The tests cover the
canonical 3-keys form, the bold variants, partial coverage (1 or 2 keys,
not all 3), and the case where the trio is absent on a body that has the
Grain tag (existing-PR scenario: advisory must NOT flag these).
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import grain_tag as gt  # noqa: E402


# --- canonical form: `Grain: TIER/GENRE` -----------------------------------

def test_canonical_grain_colon():
    g = gt.parse_grain_tag("Grain: LIGHT/guard -- lane myia-po-2023:CoursIA\n\nbody")
    assert g == {"tier": "LIGHT", "genre": "guard", "lane": "myia-po-2023:CoursIA"}


def test_bold_grain_colon():
    # `**Grain:**` -- bold wrapper, the form the coordinator uses.
    g = gt.parse_grain_tag("**Grain:** LIGHT/guard - lane myia-ai-01:CoursIA")
    assert g == {"tier": "LIGHT", "genre": "guard", "lane": "myia-ai-01:CoursIA"}


# --- title form: `## Grain` then tag on the next line (#9485 motivation) ----

def test_title_form_hash_grain_next_line():
    # The exact form that was invisible: `## Grain` (title), tag on the line
    # after a blank line, backticks around the tier/genre.
    body = (
        "Some intro.\n\n"
        "## Grain\n\n"
        "`MED/tooling (#8056 cost-honesty)` — lane `myia-po-2023:CoursIA` "
        "— prev: `MED/tooling #9457`.\n\n"
        "Rest of body."
    )
    g = gt.parse_grain_tag(body)
    assert g == {"tier": "MED", "genre": "tooling", "lane": "myia-po-2023:CoursIA"}


def test_title_form_h3_grain():
    # `### Grain` -- three hashes, same mechanism (# stripped -> `Grain` + ws).
    body = "### Grain\n\nDEEP/lean -- lane myia-po-2024:CoursIA-2"
    g = gt.parse_grain_tag(body)
    assert g == {"tier": "DEEP", "genre": "lean", "lane": "myia-po-2024:CoursIA-2"}


# --- no-colon form (#9485 point 2) -----------------------------------------

def test_no_colon_grain_space_tier():
    # `Grain LIGHT/guard` -- no colon at all, tolerated when TIER/GENRE follows.
    g = gt.parse_grain_tag("`Grain` LIGHT/guard -- lane myia-po-2025:CoursIA")
    assert g == {"tier": "LIGHT", "genre": "guard", "lane": "myia-po-2025:CoursIA"}


def test_bold_grain_space_colon():
    # `**Grain** :` -- bold, space BEFORE the colon (#9477 form).
    g = gt.parse_grain_tag(
        "**Grain** : DEEP/research-code -- bridge #2 (no lane on this line)"
    )
    assert g["tier"] == "DEEP"
    assert g["genre"] == "research-code"
    assert g["lane"] is None  # no lane anywhere -> the guard flags lane-missing


# --- lane declared elsewhere (#9485 point 4) -------------------------------

def test_lane_on_separate_bold_line():
    # `**Lane** :` on its own line, away from the Grain line.
    body = (
        "**Grain:** LIGHT/refs . **See** #1206\n\n"
        "**Lane** : myia-po-2024:CoursIA-2\n"
    )
    g = gt.parse_grain_tag(body)
    assert g == {"tier": "LIGHT", "genre": "refs", "lane": "myia-po-2024:CoursIA-2"}


def test_lane_absent_when_no_token():
    # Tag present, but no `lane <machine:workspace>` anywhere -> lane None.
    # This is the real defect #9477/#9462 expose: the guard must flag it
    # (`variation-tag-lane-missing`), and the organ leaves the PR unattributed.
    g = gt.parse_grain_tag("Grain: DEEP/research-code -- bridge #2, no lane")
    assert g == {"tier": "DEEP", "genre": "research-code", "lane": None}


# --- substance guard: tolerance ends where substance is absent -------------

def test_empty_body_returns_none():
    assert gt.parse_grain_tag("") is None
    assert gt.parse_grain_tag(None) is None  # type: ignore[arg-type]


def test_no_grain_word_returns_none():
    assert gt.parse_grain_tag("no tag anywhere in this body") is None


def test_grain_word_without_tier_genre_returns_none():
    # "Grain" appears but no `<TIER>/<GENRE>` follows -- the tolerance on
    # punctuation must NOT become tolerance on the substance (#9485: "Aucune
    # tolérance sur la substance").
    assert gt.parse_grain_tag("## Grain\n\nSome prose, no tier/genre here.") is None
    assert gt.parse_grain_tag("Grain: -- lane myia-po-2023:CoursIA") is None


def test_tier_uppercased_genre_lowercased():
    # Normalisation preserved: tier canonical upper, genre canonical lower
    # (so the guard's case-statement and G-VAR-3 adjacency compare cleanly).
    g = gt.parse_grain_tag("grain: light/GUARD -- lane myia-po-2023:CoursIA")
    assert g["tier"] == "LIGHT"
    assert g["genre"] == "guard"


def test_genre_with_underscore_and_digits():
    # GENRE charset: letters, digits, _, - (e.g. notebook-python, research-code).
    g = gt.parse_grain_tag("Grain: MED/notebook-python -- lane x:y")
    assert g["genre"] == "notebook-python"
    g = gt.parse_grain_tag("Grain: DEEP/research-code -- lane x:y")
    assert g["genre"] == "research-code"


# --- #9861 short-header trio (Quoi / Preuve / Perimetre) ------------------

def test_short_header_canonical_three_keys():
    """The reference body from #9861 -- three keys, one line each."""
    body = (
        "Grain: MED/guard — lane myia-po-2023:CoursIA-2 — prev: MED/tooling #9848\n"
        "\n"
        "Quoi:       Extend grain_tag.py with short-header keys per #9861.\n"
        "Preuve:     pytest scripts/tests/test_grain_tag.py -v\n"
        "Perimetre:  scripts/grain_tag.py + .github/workflows/variation-tag-guard.yml + "
        "scripts/tests/test_grain_tag.py. Out of scope: variation_light_cap.py organ "
        "(untouched, no API change).\n"
        "\n"
        "## Context\n"
        "..."
    )
    sh = gt.parse_short_header(body)
    assert sh["quoi"] == "Extend grain_tag.py with short-header keys per #9861."
    assert sh["preuve"] == "pytest scripts/tests/test_grain_tag.py -v"
    assert sh["perimetre"].startswith("scripts/grain_tag.py +")
    assert "Out of scope" in sh["perimetre"]


def test_short_header_bold_keys():
    """`**Quoi** :` etc. -- the same bold-wrapped form the coordinator uses."""
    body = (
        "**Grain:** MED/guard -- lane myia-ai-01:CoursIA\n"
        "\n"
        "**Quoi** : split the hashlife module\n"
        "**Preuve** : lake build conway_lean (exit 0)\n"
        "**Perimetre** : conway_lean/Conway/Life/HashlifeCorrectness.lean"
    )
    sh = gt.parse_short_header(body)
    assert sh["quoi"] == "split the hashlife module"
    assert sh["preuve"] == "lake build conway_lean (exit 0)"
    assert sh["perimetre"] == "conway_lean/Conway/Life/HashlifeCorrectness.lean"


def test_short_header_partial_two_of_three():
    """Body carries only Quoi + Preuve -- the guard must NOT flag complete."""
    body = (
        "Grain: LIGHT/guard -- lane myia-po-2026:CoursIA\n"
        "\n"
        "Quoi: doc-resync for #9756\n"
        "Preuve: diff --stat on README.md\n"
    )
    sh = gt.parse_short_header(body)
    assert sh["quoi"] == "doc-resync for #9756"
    assert sh["preuve"] == "diff --stat on README.md"
    assert sh["perimetre"] is None
    # The guard checks `all three absent`: partial coverage does NOT trip the
    # `variation-short-header-missing` label. (Hardening to "1 absent = flag"
    # is a separate decision; see issue body.)
    assert not all(sh[k] is not None for k in ("quoi", "preuve", "perimetre"))


def test_short_header_none_when_absent():
    """An existing-PR body: tag present, trio absent -- must return all None."""
    body = (
        "Grain: LIGHT/guard -- lane myia-po-2024:CoursIA\n"
        "\n"
        "## What this does\n"
        "Some body, no short-header keys, no `Quoi:` / `Preuve:` / `Perimetre:`."
    )
    sh = gt.parse_short_header(body)
    assert sh == {"quoi": None, "preuve": None, "perimetre": None}


def test_short_header_empty_body_returns_all_none():
    """Edge: empty body / None -- same shape as parse_grain_tag."""
    assert gt.parse_short_header("") == {"quoi": None, "preuve": None, "perimetre": None}
    assert gt.parse_short_header(None) == {"quoi": None, "preuve": None, "perimetre": None}  # type: ignore[arg-type]


def test_short_header_keys_in_indented_blockquote():
    """Blockquote-prefixed lines (the > noise is stripped before matching)."""
    body = (
        "Grain: MED/refactor -- lane myia-po-2025:CoursIA\n"
        "\n"
        "> Quoi: cleanup\n"
        "> Preuve: pytest scripts/tests/\n"
        "> Perimetre: scripts/audit/\n"
    )
    sh = gt.parse_short_header(body)
    assert sh["quoi"] == "cleanup"
    assert sh["preuve"] == "pytest scripts/tests/"
    assert sh["perimetre"] == "scripts/audit/"


def test_short_header_does_not_pollute_parse_grain_tag():
    """Adding the trio must NOT change parse_grain_tag's return shape (#9485
    contract: the organ imports parse_grain_tag and reads only tier/genre/lane).
    A body that has both the tag and the trio returns the same {tier, genre,
    lane} from parse_grain_tag -- the trio is parsed by the OTHER function."""
    body = (
        "Grain: DEEP/lean -- lane myia-po-2023:CoursIA-2\n"
        "\n"
        "Quoi: prove L3423 SE\n"
        "Preuve: lake build conway_lean\n"
        "Perimetre: conway_lean/\n"
    )
    g = gt.parse_grain_tag(body)
    assert g == {"tier": "DEEP", "genre": "lean", "lane": "myia-po-2023:CoursIA-2"}


def test_short_header_first_hit_wins_per_key():
    """If a key appears twice, the FIRST captured value wins -- the convention
    says "one line per key", so a duplicate is commentary to ignore."""
    body = (
        "Quoi: first answer (canonical)\n"
        "\n"
        "Then later: Quoi: second answer (commentary, ignored)\n"
    )
    sh = gt.parse_short_header(body)
    assert sh["quoi"] == "first answer (canonical)"


# --- short-header section form (#10163) -------------------------------------
#
# #10163 extends the trio: key on its own line (optionally with title hashes or
# `**` wrapper), value in the NEXT paragraph (until blank-line break). The
# inline form (#9861) must continue to work unchanged -- non-regression.

def test_short_header_section_form_h2():
    """`## Quoi` then the answer in the next paragraph (#10163 reference form)."""
    body = (
        "Grain: MED/guard -- lane myia-po-2024:CoursIA-2 -- prev: MED/guard #10162\n"
        "\n"
        "## Quoi\n"
        "\n"
        "Extend parse_short_header to recognise the section form (#10163) --\n"
        "key on its own line, value in the next paragraph.\n"
        "\n"
        "## Preuve\n"
        "\n"
        "pytest scripts/tests/test_grain_tag.py -v (30/30 PASS expected)\n"
        "\n"
        "## Perimetre\n"
        "\n"
        "scripts/grain_tag.py + scripts/tests/test_grain_tag.py. Out of scope:\n"
        "variation-tag-guard.yml (no API change, the guard consumes parse_short_header\n"
        "identically).\n"
        "\n"
        "## Context\n"
        "..."
    )
    sh = gt.parse_short_header(body)
    assert sh["quoi"].startswith("Extend parse_short_header")
    assert "next paragraph" in sh["quoi"]
    assert sh["preuve"].startswith("pytest scripts/tests/test_grain_tag.py")
    assert "(30/30 PASS expected)" in sh["preuve"]
    assert sh["perimetre"].startswith("scripts/grain_tag.py +")
    assert "variation-tag-guard.yml" in sh["perimetre"]


def test_short_header_section_form_bold_alone():
    """`**Quoi**` (bold wrapper, NO colon, NO value on the line) -- section form."""
    body = (
        "Grain: MED/guard -- lane myia-po-2024:CoursIA-2\n"
        "\n"
        "**Quoi**\n"
        "\n"
        "split the parser into two phases (#10163)\n"
        "\n"
        "**Preuve** : lake build conway_lean (exit 0)\n"
        "\n"
        "**Perimetre** : conway_lean/Conway/Life/HashlifeCorrectness.lean\n"
    )
    sh = gt.parse_short_header(body)
    # Section form (Quoi): value is the next paragraph.
    assert sh["quoi"] == "split the parser into two phases (#10163)"
    # Inline form (Preuve/Perimetre) coexists -- non-regression check.
    assert sh["preuve"] == "lake build conway_lean (exit 0)"
    assert sh["perimetre"] == "conway_lean/Conway/Life/HashlifeCorrectness.lean"


def test_short_header_section_form_h3():
    """`### Quoi` -- three hashes, same mechanism as `## Quoi`."""
    body = (
        "Grain: LIGHT/guard -- lane myia-po-2024:CoursIA-2\n"
        "\n"
        "### Quoi\n"
        "\n"
        "doc-resync for #9756 (h3 form, same as h2)\n"
    )
    sh = gt.parse_short_header(body)
    assert sh["quoi"] == "doc-resync for #9756 (h3 form, same as h2)"
    assert sh["preuve"] is None
    assert sh["perimetre"] is None


def test_short_header_section_form_paragraph_boundary():
    """Section form: value spans MULTIPLE lines, joined into one capture."""
    body = (
        "## Quoi\n"
        "\n"
        "First line of the answer.\n"
        "Second line, same paragraph (no blank between).\n"
        "Third line, still the same paragraph.\n"
        "\n"
        "## Preuve\n"
        "\n"
        "single-line preuve\n"
    )
    sh = gt.parse_short_header(body)
    assert sh["quoi"] == "First line of the answer. Second line, same paragraph (no blank between). Third line, still the same paragraph."
    assert sh["preuve"] == "single-line preuve"
    assert sh["perimetre"] is None


def test_short_header_inline_form_no_regression():
    """The reference body from #9861 -- inline form, still captured (non-regression)."""
    body = (
        "Quoi: fix the parser\n"
        "Preuve: pytest -v\n"
        "Perimetre: scripts/x.py\n"
    )
    sh = gt.parse_short_header(body)
    assert sh["quoi"] == "fix the parser"
    assert sh["preuve"] == "pytest -v"
    assert sh["perimetre"] == "scripts/x.py"


def test_short_header_mid_paragraph_silence():
    """A key mid-paragraph (after commentary) is NOT captured -- the anchor
    is at the START of the line, and section form keys must lead their
    paragraph too. This is the test that proves we didn't widen too much."""
    body = (
        "## Context\n"
        "\n"
        "We discuss the trio convention here. Note that Quoi: the convention\n"
        "is anchored at start of line, NOT inside running prose -- this body\n"
        "has no canonical answer, only commentary.\n"
        "\n"
        "## Preuve\n"
        "\n"
        "actual proof line\n"
    )
    sh = gt.parse_short_header(body)
    # The first paragraph starts with "We discuss..." -- not a key line.
    # The mid-paragraph "Quoi: the convention" must NOT be captured.
    assert sh["quoi"] is None
    assert sh["preuve"] == "actual proof line"


def test_short_header_section_form_mixed_inline_and_section():
    """A body mixing the two forms: Quoi inline, Preuve/Perimetre section."""
    body = (
        "Grain: MED/guard -- lane myia-po-2024:CoursIA-2\n"
        "\n"
        "Quoi: fix the parser\n"
        "\n"
        "## Preuve\n"
        "\n"
        "pytest scripts/tests/test_grain_tag.py -v\n"
        "\n"
        "## Perimetre\n"
        "\n"
        "scripts/grain_tag.py only\n"
    )
    sh = gt.parse_short_header(body)
    assert sh["quoi"] == "fix the parser"
    assert sh["preuve"] == "pytest scripts/tests/test_grain_tag.py -v"
    assert sh["perimetre"] == "scripts/grain_tag.py only"


def test_short_header_section_form_first_paragraph_no_value():
    """Section form: key leads, but next paragraph is empty -> still None."""
    body = (
        "## Quoi\n"
        "\n"
        "## Preuve\n"
        "\n"
        "actual proof\n"
    )
    sh = gt.parse_short_header(body)
    # Quoi: key alone, no following non-empty paragraph -> None.
    assert sh["quoi"] is None
    assert sh["preuve"] == "actual proof"


# --- prev: close-keyword detection (#10093) ---------------------------------
#
# find_prev_close_keywords() scans any text (body OR commit message) for a
# `prev: <TIER>/<genre>` whose genre is a GitHub closing keyword. The #10093
# incident: a commit `prev: MED/fix #10067` made GitHub auto-close #10067 at
# squash-merge. The 14 canonical genres contain no closing keyword, so a
# closing-keyword genre in prev: is ALWAYS a misuse.

def test_prev_close_keyword_fix_detected():
    # The exact #10093 incident line: `prev: MED/fix #10067`.
    hits = gt.find_prev_close_keywords(
        "Grain: MED/fix -- lane myia-po-2024:CoursIA-2 -- prev: MED/fix #10067 (c.1331+50)"
    )
    assert len(hits) == 1
    assert hits[0] == {"tier": "MED", "genre": "fix"}


def test_prev_close_keyword_all_inflections():
    # Every GitHub closing keyword in the genre slot is flagged.
    for kw in ("fix", "fixes", "fixed", "close", "closes", "closed",
               "resolve", "resolves", "resolved"):
        hits = gt.find_prev_close_keywords(f"prev: LIGHT/{kw} #42")
        assert len(hits) == 1, f"expected hit for genre={kw}"
        assert hits[0]["genre"] == kw


def test_prev_canonical_genres_pass():
    # The 14 canonical genres contain NO closing keyword -> all pass.
    for genre in ("lean", "qc", "training", "genai", "notebook-python",
                  "notebook-dotnet", "docs", "guard", "refactor", "ledger",
                  "readme", "test", "tooling", "research-code"):
        hits = gt.find_prev_close_keywords(f"prev: MED/{genre} #100")
        assert hits == [], f"canonical genre {genre} must NOT be flagged"


def test_prev_close_keyword_backtick_wrapped():
    # Backticks around the prev: value are stripped (same noise discipline as
    # parse_grain_tag) -- a `prev: `MED/fix #9457`` still triggers.
    hits = gt.find_prev_close_keywords("prev: `MED/fix #9457`.")
    assert len(hits) == 1
    assert hits[0] == {"tier": "MED", "genre": "fix"}


def test_prev_close_keyword_no_prev_field():
    # A body without any prev: field -> no hits (the leading tag's genre is
    # NOT scanned, only the prev: slot).
    hits = gt.find_prev_close_keywords(
        "Grain: MED/fix -- lane myia-po-2024:CoursIA-2\n\nFixes #100."
    )
    # `MED/fix` is the LEADING tag genre (not prev:), and `Fixes #100` is an
    # intended close (no prev: prefix) -> neither is flagged. Only the prev:
    # genre slot is in scope.
    assert hits == []


def test_prev_close_keyword_empty_and_none():
    assert gt.find_prev_close_keywords(None) == []
    assert gt.find_prev_close_keywords("") == []
    assert gt.find_prev_close_keywords("no grain tag here at all") == []


def test_prev_close_keyword_multiple_prevs():
    # Two offending prev: fields in one text -> two hits.
    hits = gt.find_prev_close_keywords(
        "prev: MED/fix #100\nGrain: LIGHT/close -- prev: LIGHT/closes #200"
    )
    assert len(hits) == 2
    genres = {h["genre"] for h in hits}
    assert genres == {"fix", "closes"}
