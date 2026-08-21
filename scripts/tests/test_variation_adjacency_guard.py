#!/usr/bin/env python3
"""Unit tests for variation_adjacency_guard.py -- the G-VAR-3 organ (#11170).

G-VAR-3 (variation-protocol.md §2) bans two consecutive grains of the same
LIGHT genre for a lane. The acceptance cases come straight from the issue:
#11136 (`LIGHT/docs -- prev: LIGHT/docs 11134`) was MERGED on the night of
2026-08-15/16 with no gate tripping, #11165 (`LIGHT/docs -- prev:
MED/notebook-python`) is the legitimately-different counter-example, and the
first-grain exemption (`prev: none (premier grain)`) must never be flagged.

Run:
    python -m pytest scripts/tests/test_variation_adjacency_guard.py
"""
import sys
from pathlib import Path

# Insert `scripts/` (for grain_tag + variation_light_cap) and `scripts/ci/`
# (for the script under test).
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import variation_adjacency_guard as vag  # noqa: E402

# The two night-of-2026-08-15/16 cases, verbatim tags from issue #11170.
CASE_11136 = "Grain: LIGHT/docs -- lane myia-po-2023:CoursIA -- prev: LIGHT/docs 11134"
CASE_11165 = "Grain: LIGHT/docs -- lane myia-po-2023:CoursIA -- prev: MED/notebook-python"


def test_11136_replay_blocks():
    # The merged-without-question case: same LIGHT genre twice -> BLOCK.
    v = vag.check(CASE_11136)
    assert v["guard_pass"] is False
    assert v["blocking"] is True
    assert v["adjacent"] is True
    assert v["genre"] == "docs"
    assert v["prev_genre"] == "docs"


def test_11165_replay_passes():
    # The legitimately-different case: docs then notebook-python -> PASS.
    v = vag.check(CASE_11165)
    assert v["guard_pass"] is True
    assert v["blocking"] is False
    assert v["adjacent"] is False


def test_blocking_reason_names_genres_and_lane():
    # The issue demands the error message cite BOTH genres and the lane, so
    # the failure is debuggable from the job log alone.
    v = vag.check(CASE_11136)
    assert "docs" in v["reason"]
    assert "myia-po-2023:CoursIA" in v["reason"]
    assert "UN AUTRE genre" in v["reason"]


def test_first_grain_exemption():
    # `prev: none (premier grain)` -> PASS, no predecessor to compare.
    v = vag.check(
        "Grain: LIGHT/docs -- lane myia-po-2023:CoursIA -- prev: none (premier grain)"
    )
    assert v["guard_pass"] is True
    assert v["adjacent"] is False


def test_prev_absent_is_not_reflagged():
    # A missing prev: is covered by the variation-tag-prev-absent label and
    # the tag-required job -- this organ must not double-flag it.
    v = vag.check("Grain: LIGHT/docs -- lane myia-po-2023:CoursIA")
    assert v["guard_pass"] is True
    assert v["adjacent"] is False


def test_no_tag_is_not_reflagged():
    # Missing Grain tag -> covered by check-variation-tag-required.
    v = vag.check("Some body with no Grain tag at all.")
    assert v["guard_pass"] is True
    assert v["adjacent"] is False


def test_different_genres_pass():
    v = vag.check(
        "Grain: MED/genai -- lane myia-po-2023:CoursIA -- prev: MED/guard #11200"
    )
    assert v["guard_pass"] is True
    assert v["adjacent"] is False


def test_deep_med_adjacency_is_advisory():
    # Same DEEP/MED domain-core genre twice: §2 allows it "si chacun est une
    # substance genument distincte" -- label, never block.
    v = vag.check(
        "Grain: DEEP/lean -- lane myia-po-2026:CoursIA -- prev: DEEP/lean #9999"
    )
    assert v["guard_pass"] is True
    assert v["blocking"] is False
    assert v["adjacent"] is True
    assert "advisory" in v["reason"]


def test_every_light_genre_blocks():
    # The full LIGHT set {guard, ledger, docs, readme, test} bans adjacency.
    for genre in ("guard", "ledger", "docs", "readme", "test"):
        v = vag.check(f"Grain: LIGHT/{genre} -- lane x:y -- prev: LIGHT/{genre} #1")
        assert v["guard_pass"] is False, f"{genre} adjacency must block"
        assert v["blocking"] is True


def test_aliases_normalised_before_comparison():
    # `docs-translation` folds to `docs` via the alias table: two grains of
    # the same work under invented labels must still trip the ban (§1).
    v = vag.check(
        "Grain: LIGHT/docs -- lane myia-po-2025:CoursIA-2 -- prev: LIGHT/docs-translation #100"
    )
    assert v["guard_pass"] is False
    assert v["prev_genre"] == "docs"


def test_tier_of_prev_does_not_matter():
    # The ban compares GENRES, not tiers: LIGHT/docs after MED/docs is the
    # same violation (the MED/readme defect case of #10020).
    v = vag.check(
        "Grain: LIGHT/docs -- lane myia-po-2023:CoursIA -- prev: MED/docs #200"
    )
    assert v["guard_pass"] is False
    assert v["blocking"] is True


def test_empty_inputs_pass():
    assert vag.check(None)["guard_pass"] is True
    assert vag.check("")["guard_pass"] is True


# --- G-VAR-3 override, clause 24h (#11708) --------------------------------
#
# variation-protocol section 3 grants the coordinator a decision -- "Passe
# 24 h : merger, ou fermer en nommant le remplacant" -- that the gate could
# not hear, so a correctly-blocked PR aged forever. These cases pin BOTH
# directions: the override must work, and it must not become a silent waiver.

_BLOCKED = ("Grain: LIGHT/guard -- lane myia-po-2026:CoursIA -- "
            "prev: LIGHT/guard #11675")


def _ov(author, body):
    return vag.parse_override([{"author": author, "body": body}])


def test_override_absent_still_blocks():
    # POSITIVE CONTROL. A gate whose whole lot passes is indistinguishable
    # from a gate that is unplugged: without a marker, the real adjacency
    # must still fail. This is the case that proves the other six mean
    # something.
    v = vag.check(_BLOCKED, override=None)
    assert v["guard_pass"] is False
    assert v["blocking"] is True
    # and the message must name the way out, not just the ban
    assert "G-VAR-3 OVERRIDE" in v["reason"]


def test_override_by_coordinator_lifts_with_named_replacement():
    v = vag.check(_BLOCKED, override=_ov(
        "myia-ai-01",
        "[G-VAR-3 OVERRIDE] lane myia-po-2026:CoursIA -- next: lean"))
    assert v["guard_pass"] is True
    assert v["overridden"] is True
    assert v["override_next"] == "lean"
    assert v["adjacent"] is True  # the adjacency was REAL; it is waived, not denied


def test_override_by_worker_is_ignored():
    # A lane cannot self-exempt -- the whole point of writing the arbitration
    # down (#10223 precedent on lane claims).
    v = vag.check(_BLOCKED, override=_ov(
        "myia-po-2026",
        "[G-VAR-3 OVERRIDE] lane myia-po-2026:CoursIA -- next: lean"))
    assert v["guard_pass"] is False


def test_override_without_replacement_is_ignored():
    # "HOLD sans remplacement = echec coordinateur" (section 3): a marker
    # naming no successor is not a decision, it is an abdication.
    v = vag.check(_BLOCKED, override=_ov(
        "myia-ai-01", "[G-VAR-3 OVERRIDE] lane myia-po-2026:CoursIA"))
    assert v["guard_pass"] is False


def test_override_naming_the_blocking_genre_is_vacuous():
    # A waiver that promises to replay the same adjacency is not a waiver.
    v = vag.check(_BLOCKED, override=_ov(
        "myia-ai-01",
        "[G-VAR-3 OVERRIDE] lane myia-po-2026:CoursIA -- next: guard"))
    assert v["guard_pass"] is False
    assert "n'en est pas une" in v["reason"]


def test_override_replacement_goes_through_the_alias_table():
    # Same normalisation as the genre comparison itself: `slidev` folds to
    # `slides`, so a coordinator writing either names the same successor.
    v = vag.check(_BLOCKED, override=_ov(
        "myia-ai-01",
        "[G-VAR-3 OVERRIDE] lane myia-po-2026:CoursIA -- next: slidev"))
    assert v["guard_pass"] is True
    assert v["override_next"] == "slides"


def test_override_genre_outside_the_enum_passes_through():
    # variation-protocol section 1: a genre outside the list is an alias the
    # merge-gate normalises, "pas une violation" -- so an unrecognised
    # successor is kept verbatim rather than dropping the marker. It still
    # lifts, because what makes an override non-vacuous is that it DIFFERS
    # from the blocking genre, not that it sits in the enum.
    v = vag.check(_BLOCKED, override=_ov(
        "myia-ai-01",
        "[G-VAR-3 OVERRIDE] lane myia-po-2026:CoursIA -- next: documentation"))
    assert v["guard_pass"] is True
    assert v["override_next"] == "documentation"


def test_last_coordinator_marker_wins():
    ov = vag.parse_override([
        {"author": "myia-po-2026", "body": "[G-VAR-3 OVERRIDE] next: lean"},
        {"author": "jsboige", "body": "[G-VAR-3 OVERRIDE] next: qc"},
    ])
    assert ov is not None and ov["next_genre"] == "qc"
    assert vag.check(_BLOCKED, override=ov)["guard_pass"] is True


def test_override_does_not_touch_the_advisory_branch():
    # DEEP/MED adjacency was never blocking; the override must not turn it
    # into something else.
    v = vag.check(
        "Grain: DEEP/lean -- lane myia-po-2026:CoursIA -- prev: DEEP/lean #11600",
        override=_ov("myia-ai-01", "[G-VAR-3 OVERRIDE] next: qc"))
    assert v["guard_pass"] is True
    assert v["adjacent"] is True
    assert v.get("overridden") is not True


def test_parse_override_tolerates_gh_author_object():
    # `gh pr view --json comments` nests the login; accept both shapes.
    ov = vag.parse_override([{"author": {"login": "myia-ai-01"},
                              "body": "[G-VAR-3 OVERRIDE] next: lean"}])
    assert ov is not None and ov["author"] == "myia-ai-01"


def test_parse_override_empty_and_malformed():
    assert vag.parse_override(None) is None
    assert vag.parse_override([]) is None
    assert vag.parse_override(
        [{"author": "myia-ai-01", "body": "rien a voir"}]) is None


# --- Malformed override is ANNOUNCED, never confusable with absent (#12096) --
#
# #11963: the coordinator posted `[G-VAR-3 OVERRIDE] lane <...>` with the
# marker ending at the lane echo -- `next:` never came. parse_override
# returned None, the SAME value as "no comment of the coordinator at all",
# the gate re-blocked mute, and the coordinator read the silence as the guard
# ignoring the arbitration. "Rejete" and "absent" must never share a return
# value. A helper returning only the negative control proves nothing: an
# unplugged organ produces the same output -- these tests pin the WORDS.

def test_malformed_override_missing_next_is_announced():
    # Acceptance negative A of #12096: coordinator marker WITHOUT `next:`.
    # The gate must block AND the verdict must name the rejected marker,
    # its author, and the reason -- this is the #11963 shape verbatim.
    v = vag.check(_BLOCKED, override=_ov(
        "myia-ai-01", "[G-VAR-3 OVERRIDE] lane myia-po-2026:CoursIA"))
    assert v["guard_pass"] is False
    assert v["blocking"] is True
    assert v["overridden"] is False
    assert "lu et rejete" in v["reason"]
    assert "myia-ai-01" in v["reason"]
    assert "`next:` manquant" in v["reason"]
    assert "Forme attendue" in v["reason"]


def test_malformed_override_next_off_line_is_announced():
    # Acceptance negative B of #12096: `next:` on the LINE FOLLOWING the
    # marker -- the exact form that failed in #11963 (the regex is
    # single-line by design, CommonMark-style; the remedy is feedback, not
    # multiline parsing).
    v = vag.check(_BLOCKED, override=_ov(
        "myia-ai-01",
        "[G-VAR-3 OVERRIDE] lane myia-po-2026:CoursIA\nnext: lean"))
    assert v["guard_pass"] is False
    assert "pas sur la meme ligne" in v["reason"]
    assert "lu et rejete" in v["reason"]


def test_malformed_override_bad_genre_shape_is_announced():
    # `next:` whose value is not a genre shape (digit-first, punctuation):
    # the third malformed clause of #12096. Distinct from out-of-enum
    # genres, which pass through verbatim (section 1 -- see
    # test_override_genre_outside_the_enum_passes_through).
    v = vag.check(_BLOCKED, override=_ov(
        "myia-ai-01", "[G-VAR-3 OVERRIDE] next: 123"))
    assert v["guard_pass"] is False
    assert "n'est pas un genre" in v["reason"]
    assert v["override_rejected"]["author"] == "myia-ai-01"


def test_override_rejected_field_is_named_and_absence_means_unread():
    # Acceptance 5 of #12096: the added verdict field is NAMED so a future
    # reader of the verdict knows its absence means "no coordinator marker
    # read", never "not looked".
    v_bad = vag.check(_BLOCKED, override=_ov(
        "myia-ai-01", "[G-VAR-3 OVERRIDE] sans next"))
    assert v_bad["override_rejected"]["reason"]  # named, carries the reason
    v_clean = vag.check(_BLOCKED, override=None)
    assert "override_rejected" not in v_clean  # absent = nothing was read
    # the vacuous next:-names-the-blocked-genre case carries the field too
    v_vacuous = vag.check(_BLOCKED, override=_ov(
        "myia-ai-01", "[G-VAR-3 OVERRIDE] next: guard"))
    assert v_vacuous["override_rejected"]["author"] == "myia-ai-01"


def test_malformed_override_by_worker_stays_invisible():
    # Acceptance negative C of #12096, documented choice: a WORKER-authored
    # malformed marker remains indistinguishable from absent (a lane cannot
    # self-exempt, and a worker's marker carries no arbitration to reject).
    # It blocks, and announces nothing -- same as a well-formed worker marker.
    ov = vag.parse_override([{"author": "myia-po-2026",
                              "body": "[G-VAR-3 OVERRIDE] sans next"}])
    assert ov is None
    v = vag.check(_BLOCKED, override=ov)
    assert v["guard_pass"] is False
    assert "override_rejected" not in v


def test_well_formed_override_still_lifts_after_12096():
    # POSITIVE CONTROL of the #12096 batch: the three-state parse did not
    # break the path it exists to serve. Same shape as
    # test_override_by_coordinator_lifts_with_named_replacement, kept here
    # so the malformed cases above are provably not passing by accident of
    # a disconnected helper.
    v = vag.check(_BLOCKED, override=_ov(
        "jsboige", "[G-VAR-3 OVERRIDE] lane myia-po-2026:CoursIA -- next: qc"))
    assert v["guard_pass"] is True
    assert v["overridden"] is True
    assert v["override_next"] == "qc"


def test_parse_override_malformed_reasons_distinct():
    # The three malformed clauses produce three DISTINCT reasons -- a single
    # generic "malformed" message would put the diagnosis burden back on the
    # coordinator (#12096: "avec la raison et la forme attendue").
    r_missing = vag.parse_override([{"author": "jsboige",
                                     "body": "[G-VAR-3 OVERRIDE] lane x:y"}])
    r_offline = vag.parse_override([{"author": "jsboige",
                                     "body": "[G-VAR-3 OVERRIDE] lane x:y\nnext: lean"}])
    r_shape = vag.parse_override([{"author": "jsboige",
                                   "body": "[G-VAR-3 OVERRIDE] next: 7days"}])
    assert "manquant" in r_missing["malformed"]
    assert "meme ligne" in r_offline["malformed"]
    assert "n'est pas un genre" in r_shape["malformed"]
