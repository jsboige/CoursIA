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


# --- #13633: the bare lowercase token in prose must NOT arm the extractor ---
#
# `re.IGNORECASE` on `_GRAIN_FULL_RE` let a lowercase `grain` (a noun in
# running prose, not a key) match `<TIER>/<GENRE>` after it. The #13550 body
# carried NO `Grain:` key -- it described ANOTHER PR's next grain: "est le
# grain MED/tooling suivant" + a signature "Lane myia-po-2027:CoursIA-2".
# parse_grain composed {'tier': 'MED', 'lane': ...} and the gate returned
# `cap_reached: false` instead of the #9465 `null` ("not evaluated"). Controls
# A-E below pin the fix in BOTH directions (A/B -> None; D still parses).

def test_13633_control_a_prose_lowercase_token_with_lane():
    # A: no key, prose "le grain MED/tooling suivant" + a Lane signature line.
    # The trigger is the tier/genre TOKEN, but the token is a lowercase noun --
    # it must NOT arm the extractor. This is the exact #13550 shape.
    body = (
        "#13544 (renderer hard gate before rerender) est le grain MED/tooling "
        "suivant, priorite P1.\n"
        "Lane myia-po-2027:CoursIA-2 -- c.1331p250"
    )
    g = gt.parse_grain_tag(body)
    assert g is None, f"prose lowercase token must not parse, got {g!r}"


def test_13633_control_b_prose_lowercase_token_no_lane():
    # B: no key, prose ONLY (no Lane line) -> None too.
    g = gt.parse_grain_tag("est le grain MED/tooling suivant, priorite P1.")
    assert g is None, f"prose-only must not parse, got {g!r}"


def test_13633_control_c_lane_line_alone_is_none():
    # C: no key, "Lane x:y" line alone -> None. The trigger is the tier/genre
    # token, NOT the lane line (the lane line alone is no tag at all).
    g = gt.parse_grain_tag("Lane myia-po-2027:CoursIA-2 -- c.1331p250")
    assert g is None


def test_13633_control_d_real_key_still_parses():
    # D (positive control): a real capitalised `Grain:` key STILL parses.
    g = gt.parse_grain_tag("Grain: DEEP/lean - lane myia-ai-01:CoursIA")
    assert g == {"tier": "DEEP", "genre": "lean", "lane": "myia-ai-01:CoursIA"}


def test_13633_control_e_empty_body_is_none():
    # E (negative control): empty body -> None (already pinned, kept explicit).
    assert gt.parse_grain_tag("") is None
    assert gt.parse_grain_tag(None) is None  # type: ignore[arg-type]


def test_13633_uppercase_token_at_line_start_is_still_a_key():
    # The 5 tolerated forms all capitalise the key; the no-colon form
    # `Grain LIGHT/guard` (capital G) is indistinguishable from prose by
    # shape alone (space before T/G) -- so capitalisation IS the boundary.
    # A capitalised key at the start of a line must still parse.
    g = gt.parse_grain_tag("Grain LIGHT/guard -- lane myia-po-2026:CoursIA")
    assert g == {"tier": "LIGHT", "genre": "guard", "lane": "myia-po-2026:CoursIA"}


def test_tier_uppercased_genre_lowercased():
    # Normalisation preserved: tier canonical upper, genre canonical lower
    # (so the guard's case-statement and G-VAR-3 adjacency compare cleanly).
    # #13633 -- the KEY stays capitalised `Grain:` (a lowercase `grain` in
    # prose is a noun, not a key); only TIER/GENRE are case-tolerant.
    g = gt.parse_grain_tag("Grain: light/GUARD -- lane myia-po-2023:CoursIA")
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
    # The trio is partial: c.10330 / PR retired the `check-short-header` job
    # that labelled `variation-short-header-missing` on PRs with all three keys
    # absent. The parser here is still used (kept for a future convention
    # rollout); what changed is the gating decision -- no job, no flag.
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
# squash-merge. The 15 canonical genres contain no closing keyword, so a
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
    # Iterate gt.GENRES itself, NOT a copy of it. A hardcoded list here would
    # be a fourth duplicate of the enumeration, silently drifting from the one
    # the guard actually enforces -- which is the very defect that let
    # notebook-lean be labelled off-list while the cap ranked it CONTENT.
    for genre in gt.GENRES:
        hits = gt.find_prev_close_keywords(f"prev: MED/{genre} #100")
        assert hits == [], f"canonical genre {genre} must NOT be flagged"


def test_notebook_lean_is_canonical_content_genre():
    # Regression guard for the two-organ disagreement (#11764): the cap
    # canonicalized notebook-lean -> lean (CONTENT, correct) while the tag
    # guard rejected it as off-list, labelling legitimate Lean-notebook grains
    # variation-tag-genre-offlist. Both organs must now agree.
    assert "notebook-lean" in gt.GENRES

    import variation_light_cap as vlc  # sys.path already set at module level

    canon = vlc.canonicalize_genre("notebook-lean")
    assert canon == "notebook-lean", (
        f"membership in GENRES must win over compound reduction, got {canon!r}"
    )
    assert canon not in vlc.LIGHT_GENRES, "a Lean notebook is CONTENT, never LIGHT"


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


def test_parse_prev_canonical_with_pr():
    # Canonical form: `prev: <TIER>/<GENRE> #<PR>` -- the guard reads this to
    # keep the adjacency G-VAR-3 evaluable mechanically (#10983).
    r = gt.parse_prev(
        "Grain: MED/tooling -- lane myia-po-2025:CoursIA-2 -- prev: MED/tooling #11021 (c.164)"
    )
    assert r == {"present": True, "exempt": False, "tier": "MED",
                 "genre": "tooling", "pr_number": 11021}


def test_parse_prev_canonical_without_pr():
    # PR reference optional -- the TIER/GENRE pair is what traces adjacency.
    r = gt.parse_prev("Grain: DEEP/lean -- lane myia-po-2025:CoursIA-2 -- prev: DEEP/lean #10912")
    assert r["present"] is True
    assert r["genre"] == "lean"
    assert r["pr_number"] == 10912


def test_parse_prev_absent():
    # A Grain tag without any prev: field -- the exact gap #10983 measures
    # (10 grains merged on one lane without prev:).
    r = gt.parse_prev("Grain: DEEP/lean -- lane myia-po-2025:CoursIA-2")
    assert r == {"present": False, "exempt": False, "tier": None,
                 "genre": None, "pr_number": None}


def test_parse_prev_first_grain_exemption():
    # `prev: none (premier grain)` -- the first-grain exemption: a lane with
    # no predecessor to cite must NOT be flagged as prev-absent.
    r = gt.parse_prev(
        "Grain: DEEP/lean -- lane myia-po-2026:CoursIA -- prev: none (premier grain)"
    )
    assert r["present"] is False
    assert r["exempt"] is True


def test_parse_prev_exemption_noise_tolerant():
    # Bold-wrapped exemption (same noise discipline as parse_grain_tag).
    r = gt.parse_prev(
        "Grain: MED/docs -- lane myia-po-2023:CoursIA -- **prev: none (premier grain)**"
    )
    assert r["exempt"] is True


def test_parse_prev_empty_and_none():
    assert gt.parse_prev(None)["present"] is False
    assert gt.parse_prev(None)["exempt"] is False
    assert gt.parse_prev("")["present"] is False


def test_find_non_closing_refs_see_part_of_refs():
    # The 3 safe-syntax non-closing references (See/Part of/Refs) -- the
    # complement of find_close_keyword_pr_refs. Feeds lane_claim_required's
    # advisory `lane-claim-conflict` label (#10223 Task 4).
    text = "See #1454 -- part of the epic\nPart of #1027\nRefs #3801"
    hits = gt.find_non_closing_refs(text)
    assert sorted(h["number"] for h in hits) == [1027, 1454, 3801]
    # Same hit shape as find_close_keyword_pr_refs (keyword lowercased + span).
    assert all("keyword" in h and "span" in h for h in hits)
    assert {h["keyword"] for h in hits} == {"see", "part of", "refs"}


def test_find_non_closing_refs_excludes_closing_keywords():
    # Closing keywords must NOT be matched by the non-closing scanner (the
    # blocking discriminant stays the closing scanner's job).
    hits = gt.find_non_closing_refs("Closes #10169\nFixes #200\nSee #300")
    assert [h["number"] for h in hits] == [300]


def test_find_non_closing_refs_empty_and_none():
    assert gt.find_non_closing_refs(None) == []
    assert gt.find_non_closing_refs("") == []
    assert gt.find_non_closing_refs("nothing here") == []


def test_grain_word_boundary_graine_heading_does_not_shadow_real_tag():
    # #11771 (mesure 2026-08-19) : le body portait un titre `## Graine / Tag`
    # AVANT sa ligne `Grain:` conforme. Le motif acceptait ZERO separateur apres
    # `Grain`, donc « Graine » matchait comme `Grain` suivi de « e / Tag » et
    # l'extracteur rendait tier="E" / genre="tag" -- deux labels rouges
    # (variation-tag-malformed + variation-tag-genre-offlist) sur une PR dont le
    # tag etait parfaitement conforme. Un separateur est desormais EXIGE.
    body = """## Graine / Tag

Grain: DEEP/notebook-dotnet -- lane myia-po-2026:CoursIA-2
"""
    g = gt.parse_grain_tag(body)
    assert g is not None
    assert g["tier"] == "DEEP"
    assert g["genre"] == "notebook-dotnet"


def test_grain_word_boundary_graine_alone_is_not_a_tag():
    # Controle negatif : « Graine » SEULE ne doit produire aucun tag -- sinon le
    # fix ne ferait que deplacer le faux positif au lieu de le fermer.
    assert gt.parse_grain_tag("## Graine / Tag\n") is None


def test_grain_separator_forms_still_accepted_after_boundary_fix():
    # Non-regression #9485 : les 5 formes tolerees survivent au durcissement
    # (chacune porte au moins un separateur apres `Grain`).
    for body in (
        "Grain: LIGHT/guard -- lane myia-po-2023:CoursIA",
        "**Grain:** LIGHT/guard - lane myia-po-2023:CoursIA",
        "## Grain\n\nLIGHT/guard -- lane myia-po-2023:CoursIA",
        "`Grain` LIGHT/guard -- lane myia-po-2023:CoursIA",
        "**Grain** : LIGHT/guard -- lane myia-po-2023:CoursIA",
    ):
        g = gt.parse_grain_tag(body)
        assert g is not None, body
        assert g["tier"] == "LIGHT", body
        assert g["genre"] == "guard", body

# --- workspace containing spaces (#12145) ----------------------------------
#
# `myia-po-2025:Microsoft VS Code` is a real cluster lane. Truncating it at the
# first blank made it DIFFERENT FROM ITSELF in check_lane_claim: the lane read
# `myia-po-2025:Microsoft` from its own [CLAIMED] comment, compared it to the
# untruncated `--lane`, and reported itself as a blocking lane.
#
# Half of these cases are non-regressions and false-positive guards, not hits.
# A pattern that admits spaces is validated by what it REFUSES to swallow --
# a dash separator, an annotation key, running prose -- far more than by the
# one string it was written for.

def test_lane_workspace_with_spaces():
    g = gt.extract_lane("[CLAIMED] lane myia-po-2025:Microsoft VS Code -- paths: a/**")
    assert g == "myia-po-2025:Microsoft VS Code"


def test_lane_workspace_with_spaces_no_annotation():
    g = gt.extract_lane("[CLAIMED] lane myia-po-2025:Microsoft VS Code")
    assert g == "myia-po-2025:Microsoft VS Code"


def test_lane_workspace_with_spaces_paren_annotation():
    # #12052 form: parenthetical annotation, space then opening paren.
    g = gt.extract_lane("[CLAIMED] lane myia-po-2025:Microsoft VS Code (Phase 2)")
    assert g == "myia-po-2025:Microsoft VS Code"


def test_lane_hyphenated_workspace_unchanged():
    # The non-regression that matters most: the hyphen inside `CoursIA-2` must
    # stay part of the name, never be read as the start of an annotation.
    g = gt.extract_lane("[CLAIMED] lane myia-po-2024:CoursIA-2 -- paths: b/**")
    assert g == "myia-po-2024:CoursIA-2"


def test_lane_stops_at_em_and_en_dash():
    for dash in ("\u2014", "\u2013"):
        g = gt.extract_lane("[CLAIMED] lane myia-x:W %s paths: c/**" % dash)
        assert g == "myia-x:W", dash


def test_lane_stops_at_plain_hyphen_separator():
    # ` - ` is the separator several bodies use instead of an em dash. Admitting
    # spaces must not make the lane eat it (the hyphen IS in the token class).
    body = "Grain: MED/guard - lane myia-ai-01:CoursIA - prev: MED/tooling #12102"
    assert gt.extract_lane(body) == "myia-ai-01:CoursIA"


def test_lane_stops_before_lowercase_annotation_key():
    assert gt.extract_lane("lane myia-ai-01:CoursIA prev: MED/guard #1") == "myia-ai-01:CoursIA"


def test_lane_does_not_swallow_prose():
    # The upper-case-initial constraint on continuation words is what keeps a
    # sentence from becoming part of the lane name. Both languages, because the
    # dashboards carry both.
    assert gt.extract_lane("La lane myia-ai-01:CoursIA a livre trois PRs.") == "myia-ai-01:CoursIA"
    assert gt.extract_lane("lane myia-x:W and it works fine") == "myia-x:W"


def test_lane_fallback_twin_moves_with_the_primary(  ):
    # #10395 fallback (marker line, no literal `lane` keyword). Fixing one half
    # of a duplicated mechanism and not the other leaves the defect whole in the
    # copy -- so the twin carries the same case.
    line = "[CLAIMED] myia-po-2025:Microsoft VS Code -- paths: a/**"
    assert gt.extract_lane("no lane keyword here", marker_line=line) == "myia-po-2025:Microsoft VS Code"


def test_lane_fallback_historical_form_unchanged():
    line = "[CLAIMED] #9764 - myia-po-2025:CoursIA 2026-08-07T00:52Z"
    assert gt.extract_lane("no lane keyword here", marker_line=line) == "myia-po-2025:CoursIA"


# --- #12719: the bare-date phantom lane --------------------------------------
#
# Founder night (5 auto-blockages): a marker writing a bare date where the
# organ expects the lane produced a lane THAT EXISTS NOWHERE, and
# check_lane_claim then blocked the declaring lane on its OWN claim. The five
# real-world forms below are the founder markers (issues #12485 #12484 #12466
# #12518 #12461), verbatim prefixes.
_REAL_FOUNDER_MARKERS_12719 = [
    "[CLAIMED] #12485 — myia-po-2023:CoursIA 2026-08-23 — Medical-Chatbot : amorcage batch",
    "[CLAIMED] #12484 — myia-po-2023:CoursIA 2026-08-23 — Recipe-Maker : terminaison sur livrable",
    "[CLAIMED] #12466 — myia-po-2023:CoursIA 2026-08-23 — MGS-7c/7d : check réflexif corrigé",
    "[CLAIMED] #12518 — myia-po-2023:CoursIA 2026-08-23 — rl_6 : ablation exécutée",
    "[CLAIMED] #12461 — myia-po-2023:CoursIA 2026-08-23 — QC 03-Framework-Composite",
]


def test_lane_bare_date_not_swallowed_founder_markers():
    # Acceptance #12719-1: the five real markers parse to the BARE lane.
    for line in _REAL_FOUNDER_MARKERS_12719:
        assert gt.extract_lane("no lane keyword here", marker_line=line) == "myia-po-2023:CoursIA", line


def test_lane_bare_date_with_keyword_not_swallowed():
    # Same defect via the PRIMARY regex (keyword form).
    line = "[CLAIMED] lane myia-po-2023:CoursIA 2026-08-23 — grain"
    assert gt.extract_lane(line, marker_line=line) == "myia-po-2023:CoursIA"


def test_lane_spaces_workspace_survives_date_guard():
    # Acceptance #12719-2 (explicit): the space-tolerant lane is NOT truncated
    # by the date lookahead -- a legitimate multi-word workspace never starts
    # `NNNN-NN-NN`.
    line = "[CLAIMED] lane myia-po-2025:Microsoft VS Code 2026-08-23"
    assert gt.extract_lane(line, marker_line=line) == "myia-po-2025:Microsoft VS Code"


def test_lane_trailing_period_stripped():
    # Acceptance #12719-3: founder Grain tag of PR #12530.
    body = "- Grain `MED/genai-video` — lane `myia-po-2023:CoursIA`."
    assert gt.extract_lane(body, marker_line=body) == "myia-po-2023:CoursIA"
    # parse_grain_tag strips it too (same single-reader discipline, #9485).
    assert gt.parse_grain_tag(body)["lane"] == "myia-po-2023:CoursIA"


def test_lane_marker_residues_report_malformed_forms():
    # Acceptance #12719-4: a malformed marker is REPORTED, not silently
    # reinterpreted.
    line = _REAL_FOUNDER_MARKERS_12719[0]
    residues = gt.lane_marker_residues(line)
    assert residues == ["bare-date:2026-08-23"]
    # Trailing period is witnessed as well.
    body = "- Grain `MED/genai-video` — lane `myia-po-2023:CoursIA`."
    assert any(r.startswith("trailing-period:") for r in gt.lane_marker_residues(body))
    # A clean marker carries no residue.
    clean = "[CLAIMED] lane myia-po-2023:CoursIA -- paths: foo.py"
    assert gt.lane_marker_residues(clean) == []


# --- #13830: workspace with Latin-1 letters used to truncate ---------------
#
# Founder case: a lane whose workspace carries Latin-1 letters (e.g.
# `myia-ai-01:LivresAgites`) was truncated to `myia-ai-01:LivresAgit` -- the
# first non-ASCII byte was eaten by the `[A-Za-z0-9._-]+` class. The cap
# G-VAR-2 then counted zero grains on the lane that wrote its name correctly.
# The fix widens the workspace class to `[A-Za-zA...-O...-o...-y0-9._-]+` in
# BOTH `_LANE_RE` and `_LANE_FALLBACK_RE` (the twin MUST move or the bug
# re-opens on the fallback only -- the documented founder shape #12145).


def test_lane_latin1_workspace_not_truncated_primary():
    """Primary regex: `lane <machine>:<workspace>` body form.

    Pre-fix returned `myia-ai-01:LivresAgit` (lost `es` after the `e`).
    Post-fix must return the full token with the accented letter intact.
    """
    body = "[CLAIMED] #13286 — lane myia-ai-01:LivresAgités 2026-08-23"
    assert gt.extract_lane(body) == "myia-ai-01:LivresAgités"


def test_lane_latin1_workspace_not_truncated_fallback():
    """Fallback regex: marker-line form, no literal `lane` keyword (#10395).

    The twin regex MUST accept the same shape, otherwise the founder bug
    (#12145) re-opens on the fallback only -- a class of bug the file
    explicitly calls out at the `_LANE_FALLBACK_RE` definition site.
    """
    line = "[CLAIMED] myia-ai-01:LivresAgités 2026-08-23T00:52Z"
    assert gt.extract_lane("no lane keyword here", marker_line=line) == "myia-ai-01:LivresAgités"


def test_lane_latin1_multiple_accented_letters():
    """Multiple Latin-1 letters in the same workspace word."""
    line = "[CLAIMED] myia-ai-01:LivresAgitésÉlégants 2026-08-23T00:52Z"
    assert gt.extract_lane("no lane keyword here", marker_line=line) == "myia-ai-01:LivresAgitésÉlégants"


def test_lane_ascii_workspace_still_truncates_correctly():
    """Non-regression: an ASCII workspace still returns the same token.

    Mandatory control -- without it, a too-permissive class could swallow
    the next prose word and the test would still pass.
    """
    line = "[CLAIMED] myia-ai-01:LivresAgit 2026-08-23T00:52Z"
    assert gt.extract_lane("no lane keyword here", marker_line=line) == "myia-ai-01:LivresAgit"


def test_lane_latin1_does_not_swallow_prose():
    """The Latin-1 widening must not extend the token into the next prose word.

    Pre-fix: the class stopped at the first non-ASCII byte (and dropped
    the rest). Post-fix: the class extends through accented letters but
    still halts at whitespace and punctuation -- prose after the workspace
    stays out of the lane token.
    """
    body = "[CLAIMED] lane myia-ai-01:LivresAgités a livre trois PRs."
    assert gt.extract_lane(body) == "myia-ai-01:LivresAgités"


def test_lane_latin1_hyphenated_workspace_still_works():
    """Non-regression #13830 must NOT re-introduce the `CoursIA-2` bug.

    The original `[A-Za-z0-9._-]+` class let `CoursIA-2` through; the
    fix must keep that path open.
    """
    body = "Grain: MED/guard - lane myia-po-2024:CoursIA-2 - prev: tooling #13862"
    assert gt.extract_lane(body) == "myia-po-2024:CoursIA-2"


def test_lane_latin1_bare_date_still_rejected():
    """Non-regression #12719: a bare date immediately after the workspace
    must NOT be swallowed by the continuation clause. The widening does
    not touch the `(?!\d{4}-\d{2}-\d{2})` negative lookahead, but the
    test pins that down explicitly.
    """
    line = "[CLAIMED] myia-ai-01:LivresAgités 2026-08-23 — Medical-Chatbot : amorcage batch"
    # The lane token is the workspace only; the bare date is reported as a
    # residue but the lane extraction still works.
    assert gt.extract_lane("no lane keyword here", marker_line=line) == "myia-ai-01:LivresAgités"
    residues = gt.lane_marker_residues(line)
    assert any(r.startswith("bare-date:") for r in residues), residues


# --- #13633 : parse_grain_tag rejette un token TIER/GENRE nu en prose ----
#
# Cas fondateur documente par ai-01 le 2026-08-30 (PR #13550 fondateur,
# issue #13631 second cas) : une PR sans cle `Grain:` mais contenant une
# phrase qui DECRIT un autre grain ("le grain MED/tooling suivant, priorite
# P1.") etait parsee avec {tier: MED, genre: tooling} -- un vert confiant
# sur un ZERO tag. Le garde G-VAR-2 recevait alors un tier fantome, le
# garde G-VAR-3 calculait l'adjacence sur une lane attribuee par accident
# (ligne de signature `Lane x:y`), et la garde des orphelines perdait la
# seule PR qui aurait du etre visible.
#
# Le correctif ancre `Grain` au debut de la ligne (apres le strip du
# decoration markdown). Toute phrase ou `Grain` apparait au milieu d'une
# ligne ne matche plus, et le parse rend `None` comme specifie par #9465.


def test_13633_prose_describing_other_grain_returns_none():
    """#13633 -- Cas A fondateur : pas de cle `Grain:`, prose qui parle d'un
    autre grain + ligne de signature. Avant le fix : parse avec tier+lane
    fantome. Apres : None."""
    body = ("le grain MED/tooling suivant, priorite P1.\n"
            "Lane myia-po-2027:CoursIA-2 -- c.1331p250")
    assert gt.parse_grain_tag(body) is None


def test_13633_prose_alone_with_tier_genre_returns_none():
    """#13633 -- Cas B : pas de cle, prose seule avec un token TIER/GENRE."""
    body = "le grain MED/tooling suivant, priorite P1."
    assert gt.parse_grain_tag(body) is None


def test_13633_lane_signature_without_grain_returns_none():
    """#13633 -- Cas C : pas de cle, ligne de signature seule. Avant le fix :
    None (deja -- le declencheur etait le token TIER/GENRE, pas la lane).
    Apres : None (non-regression)."""
    body = "Lane myia-po-2027:CoursIA-2 -- c.1331p250"
    assert gt.parse_grain_tag(body) is None


def test_13633_canonical_grain_tag_still_parses():
    """#13633 -- Cas D (controle positif) : la cle `Grain: TIER/GENRE` reste
    parsee comme avant. Si ce test echoue, le fix a casse la voie nominale
    -- 32/34 PRs mergees le 2026-08-30 portent cette forme en L0."""
    body = "Grain: DEEP/lean - lane myia-ai-01:CoursIA"
    g = gt.parse_grain_tag(body)
    assert g == {"tier": "DEEP", "genre": "lean", "lane": "myia-ai-01:CoursIA"}


def test_13633_empty_body_returns_none():
    """#13633 -- Cas E (controle negatif) : corps vide -> None."""
    assert gt.parse_grain_tag("") is None


def test_13633_tier_genre_in_prose_no_grain_word_returns_none():
    """#13633 -- extension : un token TIER/GENRE isole en prose SANS le mot
    'grain' ne matchait pas avant (le token seul ne suffisait pas, il fallait
    `grain <word>/<word>`). Apres le fix, il NE matche TOUJOURS PAS -- la
    garde est plus stricte mais pas differente sur ce cas."""
    body = "voici les notes : MED/tooling, DEEP/lean, LIGHT/guard, tous OK"
    assert gt.parse_grain_tag(body) is None


def test_13633_double_tag_picks_first():
    """#13633 -- non-regression : un body avec DEUX cles `Grain:` (la premiere
    est le tag, la seconde une prose qui en parle) ne conserve que la
    premiere -- comportement historique preserve."""
    body = ("Grain: DEEP/lean\n\n"
            "et aussi le grain LIGHT/guard en complement")
    g = gt.parse_grain_tag(body)
    assert g == {"tier": "DEEP", "genre": "lean", "lane": None}


def test_13633_grain_on_subsequent_line_still_parses():
    """#13633 -- non-regression : la cle peut apparaitre sur une ligne
    subsequente (apres une courte prose d'introduction) tant qu'elle est en
    debut de ligne. La voie L0 stricte n'est pas imposee."""
    body = ("voici le tag :\n"
            "Grain: MED/tooling - lane myia-po-2026:CoursIA")
    g = gt.parse_grain_tag(body)
    assert g == {"tier": "MED", "genre": "tooling",
                 "lane": "myia-po-2026:CoursIA"}


def test_13633_title_form_hash_grain_next_line_still_parses():
    """#13633 -- non-regression : la forme toleree `## Grain\\n\\nLIGHT/guard`
    reste parsee. Le strip `_strip_title_hashes` retire les `##`, laissant
    `Grain` en debut de ligne -- la nouvelle regex line-anchored matche."""
    body = "## Grain\n\nLIGHT/guard ... lane myia-po-2023:CoursIA"
    g = gt.parse_grain_tag(body)
    assert g == {"tier": "LIGHT", "genre": "guard",
                 "lane": "myia-po-2023:CoursIA"}


def test_13633_list_bullet_grain_still_parses():
    """#13633 -- non-regression : la forme toleree `- Grain `MED/...`` (founder
    tag de PR #12530) reste parsee. Le strip `_strip_title_hashes` retire
    aussi `-` quand il precede un mot-cle reconnu, laissant `Grain` en debut
    de ligne."""
    body = "- Grain `MED/genai-video` — lane `myia-po-2023:CoursIA`."
    g = gt.parse_grain_tag(body)
    assert g == {"tier": "MED", "genre": "genai-video",
                 "lane": "myia-po-2023:CoursIA"}

# --- Latin-1 lane coverage (main #13830/#13899, re-applied post-rebase) ---

def test_lane_workspace_accented():
    # The control case from #13830: a workspace with a single accented letter.
    g = gt.extract_lane("[CLAIMED] lane myia-ai-01:LivresAgités -- paths: a/**")
    assert g == "myia-ai-01:LivresAgités"


def test_lane_workspace_accented_no_annotation():
    g = gt.extract_lane("[CLAIMED] lane myia-ai-01:LivresAgités")
    assert g == "myia-ai-01:LivresAgités"


def test_lane_workspace_accented_continuation_uppercase():
    # Continuation starts with accented uppercase (`Épisode`) -- the upper-class
    # widening (`À-ÖØ-Þ`) lets the case-sensitive initial guard pass without
    # swallowing lowercase running prose ("lane myia-x:W and it works").
    g = gt.extract_lane("[CLAIMED] lane myia-ai-01:LivresAgités Épisode -- paths")
    assert g == "myia-ai-01:LivresAgités Épisode"


def test_lane_workspace_accented_fallback():
    # The same widening must apply to the fallback regex (#10395) -- a marker
    # comment that omits the literal `lane` keyword still carries the
    # `<machine>:<workspace>` token, which the cap counts.
    line = "[CLAIMED] myia-ai-01:LivresAgités -- paths: a/**"
    assert gt.extract_lane("no lane keyword here", marker_line=line) == "myia-ai-01:LivresAgités"


def test_lane_workspace_accented_survives_date_guard():
    # Accented workspace followed by a bare date -- the date lookahead refuses
    # the date, the lane token survives intact. Mirrors
    # `test_lane_spaces_workspace_survives_date_guard` (#12719-2) for accents.
    line = "[CLAIMED] lane myia-ai-01:LivresAgités 2026-08-23"
    assert gt.extract_lane(line, marker_line=line) == "myia-ai-01:LivresAgités"


def test_lane_workspace_accented_does_not_swallow_prose():
    # The accent widening must not lower the prose guard. A lowercase French
    # article after the lane is still rejected (case-sensitive initial).
    assert gt.extract_lane("lane myia-ai-01:LivresAgités et la suite") == "myia-ai-01:LivresAgités"


# --- #13830 V2: union of #13869 (Latin Ext-A `Ā-ſ`) and #13899 (`À-ÖØ-öø-ÿ`)
# Empirical coverage from the comparative table on #13869:
#   LivresAgités    True (Latin-1 é, É)
#   Cours×IA        False (U+00D7 MULTIPLICATION SIGN -- not a letter)
#   Łódź            True (Latin Extended-A U+00B7 ł / U+00F3 ó)
# The union `À-ÖØ-öø-ÿĀ-ſ` admits every Latin-1 + Latin Extended-A letter
# while keeping both × (U+00D7) and ÷ (U+00F7) outside the token.


def test_lane_workspace_latin_extended_a_lodz():
    # Łódź : Ł (U+0141) is in Latin Extended-A, ó (U+00F3) is in Latin-1.
    # The union class admits both, so the workspace token survives intact.
    g = gt.extract_lane("[CLAIMED] lane myia-ai-01:Łódź -- paths: a/**")
    assert g == "myia-ai-01:Łódź"


def test_lane_workspace_rejects_multiplication_sign():
    # U+00D7 (×) is NOT a letter; the union class skips it (U+00D7 sits in
    # the gap between Ö and Ø of `À-ÖØ-öø-ÿ`, before `Ā-ſ`). The token
    # truncates at × as expected.
    g = gt.extract_lane("[CLAIMED] lane myia-x:Cours×IA -- paths: a/**")
    assert g == "myia-x:Cours", "× (U+00D7) must not be admitted as a letter"


def test_lane_workspace_rejects_division_sign():
    # U+00F7 (÷) is NOT a letter; the union class skips it (U+00F7 sits in
    # the gap between ö and ø of `à-öø-ÿ`, before `Ā-ſ`). The token
    # truncates at ÷ as expected.
    g = gt.extract_lane("[CLAIMED] lane myia-x:A÷B -- paths: a/**")
    assert g == "myia-x:A", "÷ (U+00F7) must not be admitted as a letter"


def test_lane_fallback_latin_extended_a_lodz():
    # Twin test for `_LANE_FALLBACK_RE` (no `lane` keyword in the comment).
    line = "[CLAIMED] myia-ai-01:Łódź -- paths: a/**"
    assert gt.extract_lane("no lane keyword here", marker_line=line) == "myia-ai-01:Łódź"


def test_lane_ascii_control_unchanged():
    # Non-regression: ASCII control case from the founder test suite.
    g = gt.extract_lane("[CLAIMED] lane myia-po-2026:CoursIA -- paths: a/**")
    assert g == "myia-po-2026:CoursIA"


