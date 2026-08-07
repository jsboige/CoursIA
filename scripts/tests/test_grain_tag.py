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
