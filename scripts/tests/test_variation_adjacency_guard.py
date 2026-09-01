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
    # (#13475 note: the historical example word `documentation` now resolves
    # to `docs` through the alias table -- replaced with a word that is
    # still genuinely outside the enum, which is what this test pins.)
    v = vag.check(_BLOCKED, override=_ov(
        "myia-ai-01",
        "[G-VAR-3 OVERRIDE] lane myia-po-2026:CoursIA -- next: fictioninedit"))
    assert v["guard_pass"] is True
    assert v["override_next"] == "fictioninedit"


def test_last_coordinator_marker_wins():
    ov = vag.parse_override([
        {"author": "myia-po-2026", "body": "[G-VAR-3 OVERRIDE] next: lean"},
        {"author": "myia-ai-01", "body": "[G-VAR-3 OVERRIDE] next: qc"},
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
        "myia-ai-01", "[G-VAR-3 OVERRIDE] lane myia-po-2026:CoursIA -- next: qc"))
    assert v["guard_pass"] is True
    assert v["overridden"] is True
    assert v["override_next"] == "qc"


def test_13730_jsboige_is_NOT_a_coordinator_login():
    # #13730 mirror of #13316: `jsboige` is the shared push identity of
    # every lane, not a coordinator. A well-formed override authored by
    # `jsboige` is therefore INVISIBLE to parse_override (worker cannot
    # self-exempt by section 1 + choice C of #12096), and the gate stays
    # down. This pins the post-#13316 hardening at the adjacency organ.
    ov = vag.parse_override([
        {"author": "jsboige", "body": "[G-VAR-3 OVERRIDE] lane myia-po-2026:CoursIA -- next: qc"},
    ])
    assert ov is None  # invisible: shared-identity author is not a coordinator
    v = vag.check(_BLOCKED, override=ov)
    assert v["guard_pass"] is False
    assert v["blocking"] is True
    assert v["overridden"] is False


def test_parse_override_malformed_reasons_distinct():
    # The three malformed clauses produce three DISTINCT reasons -- a single
    # generic "malformed" message would put the diagnosis burden back on the
    # coordinator (#12096: "avec la raison et la forme attendue").
    r_missing = vag.parse_override([{"author": "myia-ai-01",
                                     "body": "[G-VAR-3 OVERRIDE] lane x:y"}])
    r_offline = vag.parse_override([{"author": "myia-ai-01",
                                     "body": "[G-VAR-3 OVERRIDE] lane x:y\nnext: lean"}])
    r_shape = vag.parse_override([{"author": "myia-ai-01",
                                   "body": "[G-VAR-3 OVERRIDE] next: 7days"}])
    assert "manquant" in r_missing["malformed"]
    assert "meme ligne" in r_offline["malformed"]
    assert "n'est pas un genre" in r_shape["malformed"]


# --- A prose MENTION must not revoke a valid earlier override (#13261) -------
#
# #13234, run 33111721678: the gate went red 62 s after a coordinator review
# comment that merely QUOTED the marker between backticks to explain a
# check_unaddressed_nits false positive. parse_override scanned the thread
# newest-first and RETURNED on the malformed branch, so the later mention
# masked the valid override posted 3h49 earlier. Two fixes, tested here
# together and separately: (a) the malformed verdict becomes a FALLBACK --
# the scan continues and only concludes "malformed" when no well-formed
# marker exists; (b) code spans/blocks are stripped before matching, so
# discussing the marker in backticks arms nothing.

_OVERRIDE_13261_OK = ("[G-VAR-3 OVERRIDE] lane myia-po-2026:CoursIA -- "
                      "next: lean")
_MENTION_BACKTICK = ("Le faux positif de check_unaddressed_nits : ce n'est "
                     "pas un `[G-VAR-3 OVERRIDE]` manquant, la lane est "
                     "conforme.")
_MENTION_PLAIN = ("Pour rappel le marqueur [G-VAR-3 OVERRIDE] exige un "
                  "remplacant nomme apres la mention next, sur la meme "
                  "ligne que le marqueur.")


def test_13261_case_C_backtick_mention_after_override_keeps_it():
    # Route (b): the quoted marker is stripped, the mention comment carries
    # no marker at all, the valid override below it survives.
    ov = vag.parse_override([
        {"author": "myia-ai-01", "body": _OVERRIDE_13261_OK},
        {"author": "myia-ai-01", "body": _MENTION_BACKTICK},
    ])
    assert ov is not None and "malformed" not in ov
    assert ov["next_genre"] == "lean"


def test_13261_case_C_plain_mention_after_override_keeps_it():
    # Route (a): a plain-text marker (no backticks, no next:) IS read as
    # malformed -- but only as fallback: the scan continues to the older
    # comment and finds the valid override.
    ov = vag.parse_override([
        {"author": "myia-ai-01", "body": _OVERRIDE_13261_OK},
        {"author": "myia-ai-01", "body": _MENTION_PLAIN},
    ])
    assert ov is not None and "malformed" not in ov
    assert ov["next_genre"] == "lean"


def test_13261_case_D_controls_stay_held():
    # NEGATIVE CONTROL, same invocation: D must stay rejected in BOTH forms.
    # A fix that would let prose grant an override would be worse than the
    # defect (auto-exemption by simply talking about the marker).
    ov_plain = vag.parse_override([{"author": "myia-ai-01",
                                    "body": _MENTION_PLAIN}])
    assert ov_plain is not None and "malformed" in ov_plain
    # backticked mention alone: stripped to nothing -> "absent", the
    # nothing-granted-nothing-rejected contract of fix (b).
    ov_code = vag.parse_override([{"author": "myia-ai-01",
                                   "body": _MENTION_BACKTICK}])
    assert ov_code is None


def test_13261_case_B_third_party_comment_after_override_keeps_it():
    # Control B of the issue matrix, unchanged by the fix.
    ov = vag.parse_override([
        {"author": "myia-ai-01", "body": _OVERRIDE_13261_OK},
        {"author": "myia-po-2025", "body": _MENTION_PLAIN},
    ])
    assert ov is not None and ov["next_genre"] == "lean"


def test_13261_marker_in_fenced_block_grants_and_rejects_nothing():
    # Fix (b), fenced form: a marker fully inside a code block is
    # discussion -- neither an override nor a malformed rejection.
    ov = vag.parse_override([
        {"author": "myia-ai-01",
         "body": "```\n[G-VAR-3 OVERRIDE] lane x:y -- next: lean\n```"}])
    assert ov is None
    # and it must not MASK a real override posted later in the thread either
    ov2 = vag.parse_override([
        {"author": "myia-ai-01", "body": _OVERRIDE_13261_OK},
        {"author": "myia-ai-01",
         "body": "exemple : ```[G-VAR-3 OVERRIDE] next: qc```"},
    ])
    assert ov2 is not None and "malformed" not in ov2
    assert ov2["next_genre"] == "lean"


def test_13261_malformed_fallback_is_the_MOST_RECENT_rejection():
    # When no valid override exists, the fallback keeps the pre-fix
    # newest-first semantics: the MOST RECENT coordinator rejection is the
    # announced one (its reason is the actionable one).
    ov = vag.parse_override([
        {"author": "myia-ai-01", "body": "[G-VAR-3 OVERRIDE] lane x:y"},
        {"author": "myia-ai-01", "body": "[G-VAR-3 OVERRIDE] next: 7days"},
    ])
    assert ov is not None and "malformed" in ov
    assert "n'est pas un genre" in ov["malformed"]  # the newer, not "manquant"


# --- The stripper must follow GitHub's RENDERING of code (#13273) -----------
#
# Found in review of #13263 (which fixed #13261): two deviations of opposite
# polarity, same root -- what the stripper calls "code" is not what GitHub
# renders as code.
#
#   sous-match (fail-closed): OVERRIDE_EXPECTED_FORM DISPLAYS the marker
#   between backticks, so a coordinator recopying the recommended form posts
#   a span-wrapped marker that stripping erased -> silent None. Remedy taken:
#   option 2 of the issue -- a span whose ENTIRE content is a well-formed
#   override is UNWRAPPED, not erased (this also future-proofs copy-paste
#   from any doc that puts the marker in code).
#
#   sur-match (fail-open): an UNCLOSED fence matched only up to the next ```
#   (or never), so a marker after a dangling ``` stayed live text while
#   GitHub renders it as code. Remedy: an unclosed fence extends to the end
#   of the body.

_SPAN_FULL_MARKER = ("`[G-VAR-3 OVERRIDE] lane myia-ai-01:CoursIA -- "
                     "next: qc`")


def test_13273_case_B_help_text_recopy_unwraps_full_marker_span():
    # The exact entry the tool recommends, posted the way it displays it:
    # the span's ENTIRE content is a well-formed override -> unwrapped and
    # read as a live decision.
    ov = vag.parse_override([
        {"author": "myia-ai-01", "body": _SPAN_FULL_MARKER}])
    assert ov is not None and "malformed" not in ov
    assert ov["next_genre"] == "qc"


def test_13273_partial_or_trailing_span_stays_inert():
    # Only a span whose content is the marker AND NOTHING ELSE is unwrapped.
    # Marker without next: (partial) and marker with trailing words inside
    # the span both render as code on GitHub and stay inert.
    ov_partial = vag.parse_override([
        {"author": "myia-ai-01",
         "body": "`[G-VAR-3 OVERRIDE] lane x:y`"}])
    assert ov_partial is None
    ov_trailing = vag.parse_override([
        {"author": "myia-ai-01",
         "body": "`[G-VAR-3 OVERRIDE] lane x:y -- next: lean voici pourquoi`"}])
    assert ov_trailing is None


def test_13273_marker_in_unclosed_fence_grants_nothing():
    # Positive control from the issue: a fence never closed swallows the
    # marker -- GitHub renders it as code, so it grants nothing.
    body = ("voici la forme:\n```\n"
            "[G-VAR-3 OVERRIDE] lane myia-ai-01:CoursIA -- next: lean\n")
    ov = vag.parse_override([{"author": "myia-ai-01", "body": body}])
    assert ov is None


def test_13273_span_full_marker_inside_unclosed_fence_grants_nothing():
    # The unwrap must not resurrect a span sitting INSIDE an unclosed fence:
    # the fence pass runs first and erases to end of body.
    body = "exemple :\n```\n" + _SPAN_FULL_MARKER + "\n"
    ov = vag.parse_override([{"author": "myia-ai-01", "body": body}])
    assert ov is None


def test_13273_unwrapped_marker_is_a_full_fledged_newest_decision():
    # An unwrapped marker is not merely tolerated: newest-first, it beats an
    # older nude override -- the span-recopy is the coordinator's LAST word.
    ov = vag.parse_override([
        {"author": "myia-ai-01", "body": _OVERRIDE_13261_OK},
        {"author": "myia-ai-01", "body": _SPAN_FULL_MARKER},
    ])
    assert ov is not None and "malformed" not in ov
    assert ov["next_genre"] == "qc"


# --- merged-sequence predecessor (#12095) ----------------------------------
#
# G-VAR-3 adjacency is a property of the MERGED sequence, which moves while a
# PR sits open. The `prev:` field is frozen at open time, so a PR acquires a
# false violation purely by aging. These cases pin BOTH directions from issue
# #11963 -- the false positive (declared guard, real predecessor
# notebook-python -> pass) and the symmetric false negative (declared
# notebook-python, real predecessor guard -> still blocks) -- plus the
# no-merged-PR fallback and the other-lane isolation.

_MERGED_LANE = "myia-po-2024:CoursIA-2"

# The #11963 shape: `prev: MED/guard #11841` was exact at redaction
# (2026-08-20T08:27Z), but the lane merged four grains since, the last being
# notebook-python. The declared field says `guard`, the real predecessor is
# `notebook-python` -- the gate must not block a PR the rule never aimed at.
_MERGED_11963 = [
    {"number": 12025, "mergedAt": "2026-08-20T23:30:00Z",
     "body": "Grain: DEEP/notebook-python -- lane myia-po-2024:CoursIA-2 -- prev: MED/tooling #1"},
    {"number": 12022, "mergedAt": "2026-08-21T03:16:00Z",
     "body": "Grain: DEEP/notebook-python -- lane myia-po-2024:CoursIA-2 -- prev: MED/tooling #2"},
    {"number": 12059, "mergedAt": "2026-08-21T03:17:00Z",
     "body": "Grain: DEEP/notebook-python -- lane myia-po-2024:CoursIA-2 -- prev: MED/tooling #3"},
    {"number": 12063, "mergedAt": "2026-08-21T04:25:00Z",
     "body": "Grain: LIGHT/notebook-python -- lane myia-po-2024:CoursIA-2 -- prev: MED/tooling #4"},
]


def test_resolve_merged_prev_genre_picks_last_lane_pr():
    mp = vag.resolve_merged_prev_genre(_MERGED_11963, _MERGED_LANE)
    assert mp == ("notebook-python", 12063)


def test_resolve_skips_other_lanes_and_untagged():
    merged = _MERGED_11963 + [
        {"number": 12100, "mergedAt": "2026-08-21T05:00:00Z",
         "body": "Grain: LIGHT/guard -- lane myia-po-2023:CoursIA -- prev: MED/tooling #5"},
        {"number": 12101, "mergedAt": "2026-08-21T05:30:00Z",
         "body": "No Grain tag here."},
    ]
    mp = vag.resolve_merged_prev_genre(merged, _MERGED_LANE)
    assert mp == ("notebook-python", 12063)


def test_11963_declared_guard_merged_notebook_python_passes():
    # The issue's measured case: the declared `prev: MED/guard #11841` was
    # exact at redaction, but the real predecessor from the merged sequence is
    # notebook-python. The gate must PASS -- this is the false positive #12095
    # fixes (a PR blocked by the passage of time, not by its own genre).
    body = ("Grain: MED/guard -- lane myia-po-2024:CoursIA-2 -- "
            "prev: MED/guard #11841")
    v = vag.check(body, merged_prev=vag.resolve_merged_prev_genre(
        _MERGED_11963, _MERGED_LANE))
    assert v["guard_pass"] is True
    assert v["blocking"] is False
    assert v["prev_genre"] == "notebook-python"
    assert v["prev_source"] == "merged-sequence"
    assert v["prev_pr"] == 12063
    assert v["declared_prev_genre"] == "guard"


def test_symmetric_false_negative_still_blocks():
    # Positive control (same invocation): the lane REALLY merged a guard last.
    # Even if the declared prev announces a different genre, the gate must
    # still block -- the symmetric false negative the issue names.
    body = ("Grain: MED/guard -- lane myia-po-2024:CoursIA-2 -- "
            "prev: MED/notebook-python #12063")
    merged = [
        {"number": 12025, "mergedAt": "2026-08-20T23:30:00Z",
         "body": "Grain: DEEP/notebook-python -- lane myia-po-2024:CoursIA-2 -- prev: MED/tooling #1"},
        {"number": 12063, "mergedAt": "2026-08-21T04:25:00Z",
         "body": "Grain: LIGHT/guard -- lane myia-po-2024:CoursIA-2 -- prev: MED/tooling #2"},
    ]
    v = vag.check(body, merged_prev=vag.resolve_merged_prev_genre(merged, _MERGED_LANE))
    assert v["guard_pass"] is False
    assert v["blocking"] is True
    assert v["prev_genre"] == "guard"
    assert v["prev_source"] == "merged-sequence"


def test_no_merged_pr_falls_back_to_declared():
    # A lane with no merged grain has no merged sequence to consult: the gate
    # falls back to the declared `prev:` (the pre-#12095 behaviour), no crash,
    # and the verdict is honest about the source.
    v = vag.check(_BLOCKED, merged_prev=vag.resolve_merged_prev_genre([], "myia-po-2026:CoursIA"))
    assert v["guard_pass"] is False
    assert v["blocking"] is True
    assert v["prev_source"] == "declared"
    # A declaring-different-genre case passes too, same fallback.
    v2 = vag.check(
        "Grain: LIGHT/guard -- lane myia-po-2026:CoursIA -- prev: MED/tooling #12063",
        merged_prev=vag.resolve_merged_prev_genre(None, "myia-po-2026:CoursIA"))
    assert v2["guard_pass"] is True
    assert v2["prev_source"] == "declared"


def test_merged_sequence_other_lane_ignored():
    # A merged PR from ANOTHER lane must not become this lane's predecessor.
    merged = [
        {"number": 12025, "mergedAt": "2026-08-20T23:30:00Z",
         "body": "Grain: LIGHT/guard -- lane myia-po-2023:CoursIA -- prev: MED/tooling #1"},
    ]
    mp = vag.resolve_merged_prev_genre(merged, "myia-po-2026:CoursIA")
    assert mp == (None, None)


# --- #13475 : BLOCK fail-CLOSED sur genre inconnu ----------------------------
#
# Le trou G-VAR-3 : deux grains declares avec le MEME mot invente comparaient
# egaux mais echappaient au test d'appartenance a LIGHT_GENRES -- le verdict
# tombait ADVISORY (autorise), jamais BLOCK. Le remede : le predicat partage
# `genre_counts_light` (fail-CLOSED -- un genre non resolu compte LIGHT), et
# la raison nomme GENRE-UNKNOWN pour que l'auteur sache qu'il retague, pas
# qu'il dispute une adjacence.


def test_repeated_invented_genre_blocks():
    # Controle positif : avant #13475 ce cas rendait adjacent=True,
    # blocking=False (advisory). Le ban doit s'appliquer aussi aux mots
    # inventes -- sinon G-VAR-3 reste contournable par choix de mot.
    v = vag.check(
        "Grain: LIGHT/zzz-inexistant -- lane myia-po-2023:CoursIA-2 -- prev: LIGHT/zzz-inexistant #1"
    )
    assert v["guard_pass"] is False
    assert v["blocking"] is True
    assert v["adjacent"] is True
    # La raison nomme le hors-table : l'action attendue est le retag, pas la
    # dispute d'adjacence.
    assert "GENRE-UNKNOWN" in v["reason"]


def test_repeated_prose_now_blocks_through_the_alias():
    # `prose` -> docs (alignement table/texte de regle, #13475) : deux grains
    # LIGHT/prose consecutifs = adjacence docs/docs = ban absolu. Avant,
    # prose restait verbatim hors LIGHT_GENRES -> advisory seulement.
    v = vag.check(
        "Grain: LIGHT/prose -- lane myia-po-2023:CoursIA-2 -- prev: LIGHT/prose #1"
    )
    assert v["guard_pass"] is False
    assert v["blocking"] is True
    assert v["genre"] == "docs"
    assert v["prev_genre"] == "docs"


def test_single_unknown_genre_after_different_prev_still_passes():
    # Le fail-closed ne transforme pas tout en BLOCK : genres differents ->
    # pas d'adjacence, PASS (le cas G-VAR-2, cap comptable, attrapera le
    # mot inconnu de son cote).
    v = vag.check(
        "Grain: LIGHT/zzz-inexistant -- lane myia-po-2023:CoursIA-2 -- prev: MED/tooling #1"
    )
    assert v["guard_pass"] is True
    assert v["blocking"] is False
    assert v["adjacent"] is False


def test_med_unknown_genre_same_prev_is_advisory_not_blocking():
    # Reserve ai-01 sur #13585 (demande 2) : un grain MED declare dont le mot
    # de genre est hors-table, consecutif au MEME mot hors-table, ne declenche
    # PAS le ban G-VAR-3 -- le tier MED declare se lit sans ambiguite, le
    # retag est demande par le ledger GENRE-UNKNOWN, pas par une requalification
    # en LIGHT. Le cas LIGHT reste bloquant (fail-CLOSED d'origine #13475).
    body_med = "Grain: MED/secrets -- lane myia-po-2026:CoursIA -- prev: MED/secrets 13540"
    v = vag.check(body_med)
    assert v["guard_pass"] is True
    assert v["blocking"] is False
    assert v["adjacent"] is True
    assert "advisory" in v["reason"]
    body_light = "Grain: LIGHT/secrets -- lane myia-po-2026:CoursIA -- prev: LIGHT/secrets 13540"
    v2 = vag.check(body_light)
    assert v2["guard_pass"] is False
    assert v2["blocking"] is True
