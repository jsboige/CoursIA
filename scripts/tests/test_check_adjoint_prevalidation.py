"""Causal tests for the adjoint prevalidation entry gate (#16442)."""

import importlib.util
import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_adjoint_prevalidation.py"
spec = importlib.util.spec_from_file_location("check_adjoint_prevalidation", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_adjoint_prevalidation"] = mod
spec.loader.exec_module(mod)

HEAD = "0123456789abcdef0123456789abcdef01234567"


def _comment(body: str, login: str = "jsboige") -> dict:
    return {"author": {"login": login}, "body": body}


# The carrying lane of the default fixture. It must differ from the `lane` of
# `_body()` (the adjoint), or every nominal case would be a self-attestation.
# It is a real tag because an absent one is now a refusal: a dossier can only be
# trusted when the gate can see WHO carries the pull request (#16928).
CARRIER = "myia-po-2026:CoursIA"


def _base_snapshot() -> dict:
    return {
        "number": 123,
        "body": f"Grain: MED/harnais -- lane {CARRIER} -- prev: MED\n\nPR body",
        "headRefOid": HEAD,
        "state": "OPEN",
        "title": "PR title",
        "isDraft": False,
        "baseRefName": "main",
        "comments": [_comment("ordinary earlier comment")],
        "reviews": [{"state": "COMMENTED"}, {"state": "APPROVED"}],
        "threads": [{"isResolved": True}],
        "checkRuns": [
            {
                "id": 1,
                "name": "PR gate",
                "status": "completed",
                "conclusion": "success",
                "started_at": "2026-09-20T10:00:00Z",
                "output": {"title": "PR gate -- all green"},
            }
        ],
        "changedFiles": 3,
        "additions": 42,
        "deletions": 7,
    }


def _body(**changes: str) -> str:
    fields = {
        "schema": "1",
        "lane": "myia-po-2025:CoursIA-2",
        "pr": "123",
        "head": HEAD,
        "complete": "true",
        "body": "read",
        "comments-reviewed": "1",
        "reviews-reviewed": "2",
        "threads-reviewed": "1",
        "threads-unresolved": "0",
        "surfaces-sha256": mod.surfaces_fingerprint(_base_snapshot()),
        "diff-files": "3",
        "diff-additions": "42",
        "diff-deletions": "7",
        "checks": "latest-wins-green",
        "b0": "clear",
        "scope": "pass",
        "domain": "pass",
        "verdict": "READY",
        # #18933 : un READY est le rendu de l'organe -- provenance par defaut.
        "organ": "check_adjoint_prevalidation.py",
        "organ-command": (
            "python scripts/check_adjoint_prevalidation.py --derive-verdict 123"
        ),
        "organ-rc": "0",
    }
    fields.update(changes)
    lines = [mod.START, *(f"{key}: {value}" for key, value in fields.items()), mod.END]
    return "\n".join(lines)


def _snapshot(dossier: str | None = None) -> dict:
    snapshot = _base_snapshot()
    if dossier is not None:
        snapshot["comments"].append(_comment(dossier))
    return snapshot


def _snapshot_with_body(pr_body: str, **dossier_changes: str) -> dict:
    """Snapshot whose PR body is `pr_body`, attested by a dossier over THAT body.

    `surfaces-sha256` covers the body (see `surfaces_fingerprint`), so the
    fingerprint is taken AFTER the body is set. Mutating the body afterwards
    would perime the dossier and mask the check under test.
    """
    snapshot = _base_snapshot()
    snapshot["body"] = pr_body
    fields = dict(dossier_changes)
    fields["surfaces-sha256"] = mod.surfaces_fingerprint(snapshot)
    snapshot["comments"].append(_comment(_body(**fields)))
    return snapshot


def _errors(snapshot: dict) -> list[str]:
    """Assert the snapshot yields NO trustworthy dossier, and return why."""
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == ""
    return errors


def test_exact_head_complete_ready_dossier_passes():
    ready, errors = mod.evaluate(_snapshot(_body()))
    assert ready
    assert errors == []


def test_missing_dossier_fails_closed():
    assert "no [ADJOINT PREFLIGHT]" in " ".join(_errors(_snapshot()))


def test_stale_head_fails_closed():
    errors = _errors(_snapshot(_body(head="f" * 40)))
    assert any("head is stale" in error for error in errors)


def test_closed_draft_retargeted_or_retitled_pr_fails_closed():
    for field, value in (
        ("state", "MERGED"),
        ("isDraft", True),
        ("baseRefName", "release"),
        ("title", "retitled after preflight"),
    ):
        snapshot = _snapshot(_body())
        snapshot[field] = value
        errors = _errors(snapshot)
        assert errors, field


def test_incomplete_surface_attestation_fails_closed():
    body = _body().replace("reviews-reviewed: 2\n", "")
    errors = _errors(_snapshot(body))
    assert any("reviews-reviewed" in error for error in errors)


def test_each_live_surface_count_is_checked():
    cases = {
        "comments-reviewed": {"comments-reviewed": "0"},
        "reviews-reviewed": {"reviews-reviewed": "1"},
        "threads-reviewed": {"threads-reviewed": "0"},
        "diff-files": {"diff-files": "2"},
        "diff-additions": {"diff-additions": "41"},
        "diff-deletions": {"diff-deletions": "6"},
    }
    for field, change in cases.items():
        errors = _errors(_snapshot(_body(**change)))
        assert any(error.startswith(f"{field} is stale") for error in errors), field


def test_checks_and_b0_require_canonical_complete_verdicts():
    for field, value in (
        ("checks", "pending"),
        ("b0", "blocked"),
        ("scope", "fail"),
        ("domain", "fail"),
        ("complete", "false"),
        ("body", "not-read"),
    ):
        errors = _errors(_snapshot(_body(**{field: value})))
        assert any(error.startswith(f"{field} must") for error in errors), field


def test_unknown_lane_cannot_satisfy_gate():
    """A lane outside the cluster set fails closed, as does a malformed string."""
    for lane in ("not-a-lane", "myia-po-9999:CoursIA", ""):
        errors = _errors(_snapshot(_body(lane=lane)))
        assert any(error.startswith("lane must") for error in errors), lane


def test_qualifying_third_party_lane_satisfies_gate():
    """Any cluster lane may attest a pull request it does not carry (#16904).

    The binding constraint is third-party review, not one named lane. Before
    this, `ADJOINT_LANE` made a single lane's throughput the merge throughput of
    the whole repository.
    """
    for lane in ("myia-po-2027:CoursIA", "myia-po-2023:CoursIA", "myia-ai-01:CoursIA"):
        ready, errors = mod.evaluate(_snapshot(_body(lane=lane)))
        assert ready, (lane, errors)
        assert errors == [], lane


def test_secretary_lane_can_attest_although_it_carries_nothing():
    """The secretary lane emits dossiers and carries no pull request.

    That asymmetry is exactly why its absence from `QUALIFYING_LANES` was
    invisible: a carrying lane left out of the set still shows up as a stalled
    author, while a pure emitter left out simply produces nothing, and the
    fleet reads the silence as "no dossier was prepared". Measured 2026-09-21:
    `myia-po-2026:CoursIA-3` had written its dashboard one minute earlier,
    carried 0 of the last 60 pull requests, and appeared in 0 files under
    `scripts/` -- while the repository held 0 dossiers and 307 open PRs.

    `myia-po-2023:CoursIA-2` is the mirror case: it carries #16259 but could
    not attest for anyone.
    """
    for lane in ("myia-po-2026:CoursIA-3", "myia-po-2023:CoursIA-2"):
        ready, errors = mod.evaluate(_snapshot(_body(lane=lane)))
        assert ready, (lane, errors)
        assert errors == [], lane


def test_every_qualifying_lane_is_accepted_end_to_end():
    """No entry of the set may be accepted by name yet rejected in practice.

    Guards against a lane added to the frozenset while some other check keeps
    refusing it -- the set would claim a capability the gate does not grant.
    The fixture's own carrying lane is excluded and asserted refused instead:
    that refusal is the self-attestation guard doing its job, not a gap.
    """
    carrier = "myia-po-2026:CoursIA"
    assert carrier in mod.QUALIFYING_LANES
    for lane in sorted(mod.QUALIFYING_LANES - {carrier}):
        ready, errors = mod.evaluate(_snapshot(_body(lane=lane)))
        assert ready, (lane, errors)
    _, errors = mod.evaluate(_snapshot(_body(lane=carrier)))
    assert any(e.startswith("self-prevalidation refused") for e in errors), errors


def test_lane_carrying_the_pr_cannot_prevalidate_itself():
    """Self-attestation is refused: the `Grain:` tag names the carrying lane."""
    carrier = "myia-po-2027:CoursIA"
    snapshot = _snapshot_with_body(
        "Grain: DEEP/notebook-python -- lane %s -- prev: MED" % carrier, lane=carrier
    )
    errors = _errors(snapshot)
    assert any(error.startswith("self-prevalidation refused") for error in errors)
    # Le refus est le SEUL motif : sans cette assertion, une empreinte perimee
    # ferait passer le test pour la mauvaise raison.
    assert not any(error.startswith("discussion surfaces") for error in errors), errors


def test_third_party_lane_passes_when_carrier_is_declared():
    """A declared carrier does not block a dossier from a different lane."""
    snapshot = _snapshot_with_body(
        "Grain: DEEP/lean -- lane myia-po-2027:CoursIA -- prev: MED",
        lane="myia-po-2025:CoursIA-2",
    )
    ready, errors = mod.evaluate(snapshot)
    assert ready, errors
    assert errors == []


def test_absent_grain_tag_is_not_an_authorization():
    """No readable tag means the self-check CANNOT run -- so the dossier fails.

    The first version of this test passed `lane="not-a-lane"`, so the refusal
    came from the allowlist and the missing tag was never exercised at all: the
    test carried the right name and proved something else, while the code let a
    qualifying lane carrying an untagged PR file its own dossier. A QUALIFYING
    lane is what makes the absent tag the only thing left to refuse on -- hence
    the second assertion, which fails if the allowlist starts doing the work
    again.
    """
    snapshot = _snapshot_with_body(
        "pas de tag Grain ici", lane="myia-po-2023:CoursIA"
    )
    errors = _errors(snapshot)
    assert any(
        error.startswith("carrying lane cannot be established") for error in errors
    )
    assert not any(error.startswith("lane must") for error in errors)


def test_non_shared_github_author_cannot_satisfy_gate():
    snapshot = _snapshot(None)
    snapshot["comments"].append(_comment(_body(), login="worker-bot"))
    errors = _errors(snapshot)
    # #17437 -- the message no longer asserts a single login: it names the
    # observed one and the accepted set (shared login + fleet App identities).
    # Naming `worker-bot` in the assertion keeps it proving THIS refusal rather
    # than any refusal that happens to share a prefix.
    assert any(
        "is not an accepted dossier author" in error and "worker-bot" in error
        for error in errors
    )


def test_fleet_app_identity_is_an_accepted_dossier_author():
    """#17437: a lane signing its dossier under its GitHub App identity passes.

    The migration to per-lane Apps is half done -- the Apps exist and are
    installed (2026-10-06), the lanes still sign under the shared login. On the
    day a lane switches, a gate comparing the author to the shared login alone
    would refuse every dossier it files. The loop walks the whole frozen lane
    table, so adding a lane to the organ without this gate following is caught
    here rather than in production.
    """
    for lane in mod.gh_identity.APP_DOSSIER_LANES:
        login = f"{mod.gh_identity.APP_LOGIN_PREFIX}{lane}[bot]"
        snapshot = _snapshot(None)
        snapshot["comments"].append(_comment(_body(), login=login))
        verdict, errors = mod.evaluate(snapshot)
        assert verdict == mod.VERDICT_READY, f"{login}: {errors}"
        assert errors == [], f"{login}: {errors}"


def test_app_shaped_login_outside_the_frozen_lanes_is_refused():
    """The accepted set is CLOSED: a login that only LOOKS like a fleet App is out.

    Accepting by shape (``coursia-lane-*[bot]``) would let any GitHub App whose
    name merely starts with the prefix sign a dossier -- the check would stop
    proving anything about who attested. Each entry below is a near-miss that a
    substring or prefix match would let through.
    """
    impostors = (
        "coursia-lane-po-2099[bot]",   # unknown lane
        "coursia-lane-web2[bot]",      # plausible, never provisioned
        "coursia-lane-po-2024",        # right lane, no App suffix
        "coursia-lane-po-202[bot]",    # prefix of a real lane
        "coursia-lane-po-2024[bot]x",  # real login plus a trailing character
    )
    for login in impostors:
        snapshot = _snapshot(None)
        snapshot["comments"].append(_comment(_body(), login=login))
        errors = _errors(snapshot)
        assert any(
            "is not an accepted dossier author" in error for error in errors
        ), f"{login}: {errors}"


# --- #17791 : PR hors flotte (session cloud du mainteneur) -------------------
#
# Miroir de l'exemption `tag_required` (#17713/#17715, variation_tag_required.py) :
# branche `claude/*` ET marqueur « Hors flotte » dans le body. Une telle PR n'est
# porte par AUCUNE lane de la flotte, donc tout dossier d'une lane qualifiante
# est tiers par construction -- le refus « carrying lane cannot be established »
# y est une impasse structurelle, pas une garantie.


def test_out_of_fleet_pr_accepts_qualifying_dossier_without_grain_tag():
    """claude/* + « Hors flotte » : un dossier de lane qualifiante est tiers."""
    snapshot = _snapshot_with_body(
        "Session cloud du mainteneur. **Hors flotte**", lane="myia-po-2023:CoursIA"
    )
    snapshot["headRefName"] = "claude/affectionate-mccarthy-6dvuea"
    ready, errors = mod.evaluate(snapshot)
    assert ready, errors
    assert errors == []


def test_claude_branch_without_marker_is_still_refused():
    """Le prefixe seul n'exempte pas : sans le marqueur, le refus est intact."""
    snapshot = _snapshot_with_body(
        "Session cloud du mainteneur.", lane="myia-po-2023:CoursIA"
    )
    snapshot["headRefName"] = "claude/affectionate-mccarthy-6dvuea"
    errors = _errors(snapshot)
    assert any(
        error.startswith("carrying lane cannot be established") for error in errors
    )


def test_fleet_branch_with_marker_is_still_refused():
    """Recopier le marqueur sur une branche de flotte ne sort pas de la regle."""
    snapshot = _snapshot_with_body(
        "Session cloud du mainteneur. **Hors flotte**", lane="myia-po-2023:CoursIA"
    )
    snapshot["headRefName"] = "feature/renamed-to-escape"
    errors = _errors(snapshot)
    assert any(
        error.startswith("carrying lane cannot be established") for error in errors
    )


def test_self_prevalidation_refusal_survives_the_exemption_next_door():
    """Une PR de flotte taguee reste refusee en self-attestation : l'exemption
    hors flotte n'ouvre aucune echappatoire a cote."""
    carrier = "myia-po-2023:CoursIA"
    snapshot = _snapshot_with_body(
        "Grain: DEEP/lean -- lane %s -- prev: MED" % carrier, lane=carrier
    )
    snapshot["headRefName"] = "feature/ordinary-fleet-branch"
    errors = _errors(snapshot)
    assert any(error.startswith("self-prevalidation refused") for error in errors)


def test_blocked_preflight_is_a_valid_dossier_but_never_ready():
    """An honest BLOCKED dossier must be distinguishable from an absent one.

    Requiring verdict:READY for exit 0 made the right to READ depend on the state
    of MERGEABILITY, so the coordinator could only open pull requests that were
    already fine -- never the oldest ones, which are old precisely because they
    are blocked. It also pushed the adjoint to write READY just to be visible,
    which measurably produced a false `b0: clear` on a PR with three open HIGH
    findings (#16160). See #16800.
    """
    verdict, errors = mod.evaluate(_snapshot(_body(verdict="BLOCKED", b0="blocked")))
    assert verdict == mod.VERDICT_BLOCKED
    assert errors == []


def test_blocked_dossier_still_requires_full_structural_integrity():
    """exit 3 is NOT a softer gate: the fingerprint stays mandatory.

    The bad `lane` must be one that is genuinely DISQUALIFYING. This case read
    `myia-po-2023:CoursIA` while a single lane could attest; #16906 makes that a
    qualifying lane, so it would silently stop testing anything. The assertion
    survives by naming a lane outside `QUALIFYING_LANES`, not by narrowing the
    set back.
    """
    for field, value in (
        ("surfaces-sha256", "0" * 64),
        ("head", "f" * 40),
        ("lane", "myia-po-9999:CoursIA"),
        ("complete", "false"),
        ("schema", "2"),
    ):
        errors = _errors(_snapshot(_body(verdict="BLOCKED", **{field: value})))
        assert errors, f"a BLOCKED dossier with a bad {field} must not be trusted"


def test_blocked_dossier_tolerates_the_very_facts_that_block_it():
    """Unresolved threads and a red B.0 refute READY, not BLOCKED.

    Built in the right order on purpose: the unresolved thread is placed BEFORE
    the fingerprint is taken, because the fingerprint covers threads. Computing
    it first and mutating after produces a mismatch -- which is the gate working,
    not a tolerance to test.
    """
    live = _base_snapshot()
    live["threads"] = [{"isResolved": False}]
    dossier = _body(
        verdict="BLOCKED", b0="blocked", checks="BLOCKED", scope="fail",
        domain="fail",
        **{"threads-unresolved": "1",
           "surfaces-sha256": mod.surfaces_fingerprint(live)},
    )
    live["comments"].append(_comment(dossier))
    verdict, errors = mod.evaluate(live)
    assert verdict == mod.VERDICT_BLOCKED, errors


def test_noncanonical_verdict_is_not_a_dossier():
    for bogus in ("ready", "PREFLIGHT_HOLD", "RIPE", ""):
        errors = _errors(_snapshot(_body(verdict=bogus)))
        assert any(error.startswith("verdict must be one of") for error in errors)


def test_unresolved_thread_cannot_be_ready():
    snapshot = _snapshot(_body(**{"threads-unresolved": "1"}))
    snapshot["threads"] = [{"isResolved": False}]
    errors = _errors(snapshot)
    assert "READY requires zero unresolved threads" in errors


def test_empty_diff_cannot_be_ready():
    """A PR changing zero files has nothing to squash -- READY is refuted.

    Positive control, taken from the measured instance: #16975 and #16976 each
    carried an INTACT dossier declaring `diff-files: 0` with `verdict: READY`,
    so the gate returned 0 and authorised merging a pull request that delivered
    nothing. The dossier is self-consistent with the live PR -- every count
    matches -- which is why no staleness check could catch it.
    """
    live = _base_snapshot()
    live["changedFiles"] = 0
    live["additions"] = 0
    live["deletions"] = 0
    dossier = _body(
        **{"diff-files": "0", "diff-additions": "0", "diff-deletions": "0"}
    )
    live["comments"].append(_comment(dossier))
    verdict, errors = mod.evaluate(live)
    assert "READY requires a non-empty diff: 0 files changed" in errors
    assert verdict == "", errors


def test_blocked_dossier_tolerates_an_empty_diff():
    """An empty diff refutes READY, never BLOCKED.

    Same asymmetry as the draft and unresolved-thread legs: an empty diff is a
    reason a PR is NOT mergeable, and attesting it is precisely a BLOCKED
    dossier's job. Refusing it there would deny the coordinator the attested
    motive it dispatches from.
    """
    live = _base_snapshot()
    live["changedFiles"] = 0
    live["additions"] = 0
    live["deletions"] = 0
    dossier = _body(
        verdict="BLOCKED", b0="blocked", checks="BLOCKED", scope="fail",
        domain="fail",
        **{"diff-files": "0", "diff-additions": "0", "diff-deletions": "0"},
    )
    live["comments"].append(_comment(dossier))
    verdict, errors = mod.evaluate(live)
    assert verdict == mod.VERDICT_BLOCKED, errors


def test_two_line_fix_is_still_ready():
    """Negative control: the #15740 counter-example must keep passing.

    « une correction de 2 lignes d'un bug critique serait acceptable » -- the
    new leg measures absence, not smallness. A one-file, two-line diff is as
    READY as a large one.
    """
    live = _base_snapshot()
    live["changedFiles"] = 1
    live["additions"] = 1
    live["deletions"] = 1
    dossier = _body(
        **{"diff-files": "1", "diff-additions": "1", "diff-deletions": "1"}
    )
    live["comments"].append(_comment(dossier))
    verdict, errors = mod.evaluate(live)
    assert verdict == mod.VERDICT_READY, errors


def test_absent_diff_stat_never_reads_as_an_empty_diff():
    """Missing data must not decide (#14849) -- and here it already cannot.

    The new leg tests equality with 0, so `None` does not trip it. But the
    state is unreachable anyway: `validate_dossier` indexes `changedFiles`
    directly, and `main` catches `KeyError` among the fail-closed exceptions,
    reporting UNKNOWN (rc=2). Absent stats therefore become "I could not
    measure", never "the diff is empty" -- which is the distinction that
    matters, because rc=2 refuses while a fabricated `empty` would accuse.
    """
    live = _base_snapshot()
    live.pop("changedFiles")
    live["comments"].append(_comment(_body()))
    with pytest.raises(KeyError):
        mod.evaluate(live)


def test_comment_after_dossier_invalidates_it():
    snapshot = _snapshot(_body())
    snapshot["comments"].append(_comment("new concern after preflight"))
    errors = _errors(snapshot)
    assert any("discussion changed after dossier" in error for error in errors)


def test_same_count_surface_mutation_invalidates_fingerprint():
    # "checks" is deliberately absent: check-runs are no longer a hashed
    # surface (#16957). A conclusion change is caught by the claim
    # verification instead -- see test_red_check_refuses_ready_naming_the_check.
    for surface, mutate in (
        ("body", lambda snapshot: snapshot.__setitem__("body", "edited body")),
        (
            "review",
            lambda snapshot: snapshot["reviews"][0].__setitem__(
                "state", "CHANGES_REQUESTED"
            ),
        ),
        (
            "thread",
            lambda snapshot: snapshot["threads"][0].__setitem__(
                "isResolved", False
            ),
        ),
    ):
        snapshot = _snapshot(_body())
        mutate(snapshot)
        errors = _errors(snapshot)
        assert any("discussion surfaces changed" in error for error in errors), surface


def test_latest_dossier_wins_and_stale_latest_cannot_fall_back():
    snapshot = _snapshot(_body())
    snapshot["comments"].append(_comment(_body(head="e" * 40, **{"comments-reviewed": "2"})))
    errors = _errors(snapshot)
    assert any("head is stale" in error for error in errors)


def test_marker_inside_prose_or_quote_is_not_a_dossier():
    snapshot = _snapshot(None)
    snapshot["comments"] = [_comment("Quoted example:\n[ADJOINT PREFLIGHT]\nverdict: READY")]
    assert "no [ADJOINT PREFLIGHT]" in " ".join(_errors(snapshot))


def test_unknown_and_duplicate_fields_fail_closed():
    unknown = _body().replace(mod.END, "extra-proof: yes\n" + mod.END)
    assert any("unknown fields" in error for error in _errors(_snapshot(unknown)))

    duplicate = _body().replace("schema: 1", "schema: 1\nschema: 1")
    assert any("duplicate field" in error for error in _errors(_snapshot(duplicate)))


def test_truncated_dossier_is_reported_as_malformed():
    """An unclosed block stays refused: its extent is undefined."""
    truncated = _body().replace("\n" + mod.END, "")
    assert "missing closing marker" in _errors(_snapshot(truncated))


def test_prose_after_the_closing_marker_is_ignored_not_refused():
    """The contract is the delimited block; what follows is for a human.

    Refusing it discarded four dossiers in a single cycle whose machine-readable
    block was complete and whose firsthand evidence -- `check_unaddressed_nits`
    rc, comment counts, exact head -- was written below the marker so a reader
    could see it (#16928).
    """
    trailed = _body() + "\n\n### Verifications firsthand\n- B.0 : rc=0, 6 commentaires lus."
    verdict, errors = mod.evaluate(_snapshot(trailed))
    assert verdict == mod.VERDICT_READY, errors
    assert errors == []


def test_trailing_prose_cannot_smuggle_a_contract_field():
    """What the old refusal actually had to protect -- and still does.

    `content` stops at the closing marker, so a field written after it is never
    parsed. Tolerating prose is therefore not tolerating a second, contradicting
    contract: the BLOCKED verdict inside the block wins over the READY written
    below it.
    """
    smuggled = _body(verdict="BLOCKED", b0="blocked") + "\nverdict: READY\nb0: clear\nchecks: latest-wins-green"
    verdict, _ = mod.evaluate(_snapshot(smuggled))
    assert verdict == mod.VERDICT_BLOCKED



def test_noncanonical_integer_and_pr_mismatch_fail_closed():
    errors = _errors(_snapshot(_body(**{"diff-additions": "+42"})))
    assert any("canonical non-negative integer" in error for error in errors)

    errors = _errors(_snapshot(_body(pr="124")))
    assert any(error.startswith("pr is stale") for error in errors)


def test_template_populates_mechanical_fields_but_not_verdicts():
    template = mod.render_template(_base_snapshot())
    assert f"head: {HEAD}" in template
    assert "comments-reviewed: 1" in template
    assert "reviews-reviewed: 2" in template
    assert "threads-reviewed: 1" in template
    assert "surfaces-sha256: " + mod.surfaces_fingerprint(_base_snapshot()) in template
    assert "verdict: REPLACE_WITH_READY_OR_BLOCKED" in template
    assert "verdict: READY" not in template


def test_restamp_warning_is_silent_without_an_existing_dossier():
    assert mod.restamp_warning(_base_snapshot()) is None


def test_restamp_warning_names_the_new_comment_gesture():
    warning = mod.restamp_warning(_snapshot(_body()))
    assert warning is not None
    assert "comment 2 of 2" in warning
    assert "NEW" in warning and "never PATCH" in warning


def _filled(template: str) -> str:
    verdicts = {
        "complete": "true", "body": "read", "checks": "latest-wins-green",
        "b0": "clear", "scope": "pass", "domain": "pass", "verdict": "READY",
        "organ": "check_adjoint_prevalidation.py",
        "organ-command": (
            "python scripts/check_adjoint_prevalidation.py --derive-verdict 123"
        ),
        "organ-rc": "0",
    }
    lines = []
    for line in template.splitlines():
        key = line.split(":", 1)[0]
        lines.append(f"{key}: {verdicts[key]}" if key in verdicts else line)
    return "\n".join(lines)


def test_patched_restamp_can_never_match_but_a_new_comment_does():
    """#18072/#17985/#18134: the template counts the dossier it would replace."""
    snapshot = _snapshot(_body())
    stamped = _filled(mod.render_template(snapshot))

    patched = _base_snapshot()
    patched["comments"].append(_comment(stamped))
    assert any(
        error.startswith("comments-reviewed is stale") for error in _errors(patched)
    )

    posted = _snapshot(_body())
    posted["comments"].append(_comment(stamped))
    ready, errors = mod.evaluate(posted)
    assert errors == []
    assert ready


def test_metadata_identity_is_exact():
    """#17315: the rollup is out of the snapshot, so the identity is a plain
    canonical rendering -- equal dicts match, any field move diverges."""
    first = {"number": 123, "updatedAt": "2026-09-16T19:00:00Z"}
    assert mod._metadata_identity(first) == mod._metadata_identity(dict(first))

    changed = dict(first)
    changed["updatedAt"] = "2026-09-16T19:00:01Z"
    assert mod._metadata_identity(first) != mod._metadata_identity(changed)


def _bracket_reads(monkeypatch, first, second=None):
    """Stub every network read `load_snapshot` performs, and count them.

    `load_snapshot` reads the PR metadata twice -- before and after the
    surfaces -- and refuses the snapshot when the two disagree. `first` and
    `second` are payload FACTORIES (one callable per read) so a test steers
    the second read without aliasing the first.

    The stubbed check runs also pin the source of truth (#16957): the
    snapshot's `checkRuns` come from `commits/<head>/check-runs`, keyed on the
    exact head commit, never from the rollup.
    """
    calls = {"metadata": 0, "check_runs_head": None}
    runs = [
        {
            "id": 1,
            "name": "PR gate",
            "status": "completed",
            "conclusion": "success",
            "started_at": "2026-09-28T10:00:00Z",
        }
    ]

    def fake_pr_metadata(pr):
        calls["metadata"] += 1
        factory = first if calls["metadata"] == 1 else (second or first)
        return factory()

    def fake_head_check_runs(head_sha):
        calls["check_runs_head"] = head_sha
        return list(runs)

    monkeypatch.setattr(mod, "_pr_metadata", fake_pr_metadata)
    monkeypatch.setattr(mod, "_head_check_runs", fake_head_check_runs)
    monkeypatch.setattr(mod, "_issue_comments", lambda pr: [{"id": 1}])
    monkeypatch.setattr(mod, "_reviews", lambda pr: [{"id": 2}])
    monkeypatch.setattr(mod, "review_threads", lambda pr: [{"thread": 1}])
    return calls, runs


def _metadata_payload(**changes):
    """The shape `_pr_metadata` renders -- what the stability identity hashes."""
    payload = _base_snapshot()
    payload["updatedAt"] = "2026-09-28T12:00:00Z"
    payload["headRefName"] = "feature/bracket"
    payload.update(changes)
    return payload


def test_load_snapshot_reads_metadata_twice_and_takes_checks_from_rest(monkeypatch):
    calls, runs = _bracket_reads(monkeypatch, _metadata_payload)

    snapshot = mod.load_snapshot(123)

    assert calls["metadata"] == 2
    assert calls["check_runs_head"] == HEAD
    assert snapshot["checkRuns"] == runs
    assert snapshot["comments"] == [{"id": 1}]
    assert snapshot["reviews"] == [{"id": 2}]
    assert snapshot["threads"] == [{"thread": 1}]


def test_load_snapshot_aborts_when_the_head_moves_during_the_read(monkeypatch):
    """#17390 acceptance 2, re-based on the REST bracket (#17315).

    The check-runs are keyed on `headRefOid` and fetched inside the bracket, so
    a push landing between the two metadata reads must abort: accepting the
    snapshot would pair the OLD head's check-runs with the NEW head, and the
    claim verification would then read a state that never existed together.
    """
    first = _metadata_payload(headRefOid=HEAD)
    pushed = _metadata_payload(headRefOid="f" * 40)
    calls, _runs = _bracket_reads(monkeypatch, lambda: first, lambda: pushed)

    with pytest.raises(RuntimeError, match="changed while prevalidation snapshot was read"):
        mod.load_snapshot(123)
    # The check-runs were fetched for the head read BEFORE the push -- which is
    # exactly why the mismatch is refused instead of silently accepted.
    assert calls["check_runs_head"] == HEAD


def test_load_snapshot_aborts_when_any_surface_moves_during_the_read(monkeypatch):
    first = _metadata_payload()
    moved = _metadata_payload(updatedAt="2026-09-28T12:00:05Z")
    _bracket_reads(monkeypatch, lambda: first, lambda: moved)

    with pytest.raises(RuntimeError, match="changed while prevalidation snapshot was read"):
        mod.load_snapshot(123)


def test_ready_dossier_is_evidence_not_merge_authorization():
    ready, _ = mod.evaluate(_snapshot(_body()))
    assert ready
    # The result intentionally has no merge/approve decision or mutation API.
    assert not hasattr(mod, "merge")
    assert not hasattr(mod, "approve")


# --- The coordinator's own later acts do not expire the dossier (#16800) ------
#
# Measured trap this closes: the gate returned exit 0 on #16072, the coordinator
# read it as authorised, lifted its OWN CHANGES_REQUESTED -- and that very review
# made `reviews-reviewed` stale, so the gate then refused the merge. The act the
# gate authorised invalidated the dossier the gate required. Without this, a PR
# whose only blocker is a coordinator reserve can never be merged without a full
# adjoint round-trip.

T0 = "2026-09-19T00:00:00Z"
T1 = "2026-09-19T01:00:00Z"


def _stamped_snapshot(dossier_body: str) -> dict:
    snapshot = _base_snapshot()
    for row in snapshot["comments"]:
        row.setdefault("createdAt", T0)
    for row in snapshot["reviews"]:
        row.setdefault("submittedAt", T0)
        row.setdefault("author", {"login": "clusterManager-Myia"})
    comment = _comment(dossier_body)
    comment["createdAt"] = T0
    snapshot["comments"].append(comment)
    return snapshot


def _dossier_for(snapshot: dict, **changes: str) -> str:
    """Body whose fingerprint and counts match `snapshot` as it stands."""
    return _body(
        **{
            "surfaces-sha256": mod.surfaces_fingerprint(snapshot),
            "comments-reviewed": str(len(snapshot["comments"])),
            "reviews-reviewed": str(len(snapshot["reviews"])),
            **changes,
        }
    )


def test_coordinator_own_later_review_does_not_expire_the_dossier():
    """#17039 acceptance CN1 : un commentaire de LEVEE pure (sans marqueur
    de reserve) du coordinateur post-dossier NE perime PAS le dossier.

    Le contrat : la review leve une reserve tierce (Hermes / ai-01) sans
    poser de reserve neuve. _is_own_later_act(row, ..., row_kind="review")
    neutralise la row -- le dossier reste integre et le verdict READY tient.
    """
    base = _stamped_snapshot("")
    base["comments"].pop()
    snapshot = _stamped_snapshot(_dossier_for(base))
    snapshot["reviews"].append(
        {
            "state": "APPROVED",
            "author": {"login": mod.COORDINATOR_LOGIN},
            "submittedAt": T1,
            "body": "OVERRIDE -- je leve la reserve Hermes sur le head exact.",
        }
    )
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_coordinator_review_with_reserve_marker_still_expires():
    """#17039 acceptance CN2 (refactor #17693) : une review du coordinateur
    qui POSE une reserve vivante perime le dossier, meme si elle contient
    aussi un mot de levee en narration.

    Le contrat : un reviewer (humain ou bot) qui EMET un verdict formel
    SUIVI d'une mention concrete cree une surface nouvelle que l'adjoint
    n'a pas lue. La neutralisation par _is_own_later_act ne s'applique pas,
    le dossier perime. Le predicat de "verdict vivant" est maintenant
    delegue a ``check_unaddressed_nits.classify`` (meme semantique que
    B.0, encagement inclus), au lieu d'une liste de tokens en dur.

    Cas choisis : un verdict formel precede d'une mention concrete
    ("trouve corrige", "trou", "nit serre") qui resiste a l'encagement du
    narrateur de levee autour. Ces phrases illustrent le cas mixte de
    l'acceptance 2 -- l'EMISSION d'un verdict nu survit a la narration
    d'une levee AVANT ou APRES.
    """
    # Chaque corps : un verdict formel precede d'une mention concrete.
    # La narration de levee QUI SUIT ne neutralise pas l'emission (test
    # fondateur #17693 -- le predicat n'absorbe pas une reserve emise en
    # amont, meme si le reviewer dit "je leve plus tard").
    cases = [
        ("**CHANGES_REQUESTED** : trouver corrigé puis je leve.", "CHANGES_REQUESTED"),
        ("**BLOCKED** par vérif head ne passe pas, lever sera quand corrigé.", "**BLOCKED**"),
        ("🟡 nit serré sur la sortie, plus de reserve.", "🟡"),
        ("🔴 run red, je laisse pour plus tard.", "🔴"),
        ("COMMENT_WITH_CONCERNS je vois un soucis.", "COMMENT_WITH_CONCERNS"),
    ]
    for body, marker_label in cases:
        base = _stamped_snapshot("")
        base["comments"].pop()
        snapshot = _stamped_snapshot(_dossier_for(base))
        snapshot["reviews"].append(
            {
                "state": "COMMENTED",
                "author": {"login": mod.COORDINATOR_LOGIN},
                "submittedAt": T1,
                "body": body,
            }
        )
        # Le marqueur de reserve emis par le coordinateur post-dossier doit
        # perimer le dossier : _is_own_later_act refuse la neutralisation
        # (row_kind="review" + _review_body_has_reserve_marker -> True).
        errors = _errors(snapshot)
        assert any("discussion surfaces changed" in e for e in errors), (marker_label, body, errors)


def test_caged_verdict_stays_neutral_but_naked_verdict_expires():
    """Test de controle demande par ai-01 (revue #5309199712 sur #17693) :
    la MEME phrase, encagee vs nue, change la decision.

    Cas fondateur : le commentaire de levee de ai-01 sur #17693 nommait
    `COMMENT_WITH_CONCERNS` encage (forme sure prescrite par
    ``pr-review-discipline.md`` -- "repondre a une reserve"). L'ancien
    predicat (recherche `in` sur tokens en dur) perimait le dossier sur
    cette forme : le geste qui DEBLOQUE la PR cree un nit de plus a son
    propre nom, regime absorbant #17071.

    La centralisation via ``classify`` ferme la boucle : verdict encage =
    neutre, token nu = dossier perime. Meme phrase, deux issues.
    """
    # Meme phrase, encagee (neutre, le dossier survit) et nue (BOT-CONCERN,
    # dossier perime). On utilise un cas qui n'a pas d'ouverture "leve"/"override"
    # au cas ou B.0 neutraliserait trop vite.
    pairs = [
        # Cas Hermes CHANGES_REQUESTED
        ("Sur le head frais, `CHANGES_REQUESTED` se confirme : raise exception capturee.",
         "Sur le head frais, CHANGES_REQUESTED se confirme : raise exception capturee."),
        # Cas REQUEST_CHANGES
        ("Le preflight `REQUEST_CHANGES` est valide au head.",
         "Le preflight REQUEST_CHANGES est valide au head."),
        # Cas glyphe (encage vs nu -- le glyphe est un caractere unicode,
        # l'encagement revient aux backticks autour du token si texte)
        ("Constat : `🟡` puis levee plus tard.",
         "Constat : 🟡 puis levee plus tard."),
    ]
    for caged, naked in pairs:
        # ---- Variante encagee : NE perime PAS ----
        base = _stamped_snapshot("")
        base["comments"].pop()
        snapshot = _stamped_snapshot(_dossier_for(base))
        snapshot["reviews"].append({
            "state": "COMMENTED",
            "author": {"login": mod.COORDINATOR_LOGIN},
            "submittedAt": T1,
            "body": caged,
        })
        verdict, errors = mod.evaluate(snapshot)
        assert verdict == mod.VERDICT_READY, ("caged should be neutral", caged, errors)

        # ---- Variante nue (meme phrase, sans les backticks) : PERIME ----
        base = _stamped_snapshot("")
        base["comments"].pop()
        snapshot = _stamped_snapshot(_dossier_for(base))
        snapshot["reviews"].append({
            "state": "COMMENTED",
            "author": {"login": mod.COORDINATOR_LOGIN},
            "submittedAt": T1,
            "body": naked,
        })
        errors = _errors(snapshot)
        assert any("discussion surfaces changed" in e for e in errors), ("naked should expire", naked, errors)


def test_coordinator_review_with_pure_lift_does_not_expire():
    """#17039 acceptance CN3 (refactor #17693) : une review de LEVEE pure
    ne perime pas, et le predicat reste coherente avec B.0.

    C'est le scenario fondateur du fix : ai-01 leve une reserve Hermes
    via une review sans poser de reserve neuve, et le dossier reste
    integre pour permettre le merge dans la meme passe. Le predicat est
    maintenant ``check_unaddressed_nits.classify`` : chaque cas ci-dessous
    est verifie NEUTRE par classify avant l'integration au test (les
    phrases qui ne le sont pas en sont exclues -- "plus de blocage" tout
    seul est lu comme un constat de blocage par classify et reste
    correctement hors de CN3).
    """
    for body in (
        "[OVERRIDE] lane myia-ai-01:CoursIA -- Je leve la reserve Hermes.",
        "Override : reserve levee au head exact.",
        "Re-mesure au head frais, la reserve Hermes est levee.",
        "Au head frais verifie je leve la reserve.",
        "Approuve : la reserve est levee au head exact.",
        "LGTM au head exact.",
    ):
        base = _stamped_snapshot("")
        base["comments"].pop()
        snapshot = _stamped_snapshot(_dossier_for(base))
        snapshot["reviews"].append(
            {
                "state": "APPROVED",
                "author": {"login": mod.COORDINATOR_LOGIN},
                "submittedAt": T1,
                "body": body,
            }
        )
        verdict, errors = mod.evaluate(snapshot)
        assert verdict == mod.VERDICT_READY, (body, errors)


def test_coordinator_own_later_comment_does_not_expire_the_dossier():
    base = _stamped_snapshot("")
    base["comments"].pop()
    snapshot = _stamped_snapshot(_dossier_for(base))
    own = _comment("Lifting the stale PREFLIGHT_HOLD.", login=mod.COORDINATOR_LOGIN)
    own["createdAt"] = T1
    snapshot["comments"].append(own)
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_any_other_author_still_expires_the_dossier():
    """The negative control: neutrality is for the coordinator ALONE.

    Since #16883 the coordinator voice is recognised under BOTH
    ``COORDINATOR_LOGIN`` (``myia-ai-01``) and ``SHARED_GITHUB_LOGIN``
    (``jsboige``) -- the merged-account mandate means every coordinator
    action reaches the API under ``jsboige``. A genuinely foreign author
    (a worker lane that did NOT carry the dossier, or a bot) must still
    expire the dossier.
    """
    for login in ("clusterManager-Myia", "lcetinsoy", "myia-po-2024", "dependabot"):
        base = _stamped_snapshot("")
        base["comments"].pop()
        snapshot = _stamped_snapshot(_dossier_for(base))
        foreign = _comment("a new concern", login=login)
        foreign["createdAt"] = T1
        snapshot["comments"].append(foreign)
        errors = _errors(snapshot)
        assert any("discussion changed after dossier" in e for e in errors), login


# --- #17818 : premiere pose d'un commentaire consultatif de bot marker-garde --


def test_first_pose_of_bot_advisory_comment_does_not_expire_the_dossier():
    """#17818 acceptance (positive control) : un dossier integre, puis la
    premiere pose du commentaire consultatif PR-PATH-COLLISION par
    ``github-actions[bot]`` -- le verdict reste lisible. Mesure fondatrice :
    les dossiers de #17781 et #17797 perimes a 13:02Z par cette seule pose,
    l'arrivee d'une PR voisine sur les memes READMEs declenchant l'organe.
    """
    for marker in (
        "<!-- PR-PATH-COLLISION:START -->\n## Path-collision (organ #1)\npaire: X / Y",
        "<!-- variation-genre-signals -->\ngenre: lean",
        "<!-- gvar2-light-cap -->\ncap: 1/1",
        "<!-- trivial-diff-15740 -->\ntrivial: yes",
    ):
        base = _stamped_snapshot("")
        base["comments"].pop()
        snapshot = _stamped_snapshot(_dossier_for(base))
        pose = _comment(marker, login="github-actions[bot]")
        pose["createdAt"] = T1
        snapshot["comments"].append(pose)
        verdict, errors = mod.evaluate(snapshot)
        assert verdict == mod.VERDICT_READY, (marker.splitlines()[0], errors)


def test_human_comment_after_dossier_still_expires_it():
    """#17818 acceptance (negative control) : un commentaire humain posterieur
    perime toujours le dossier -- la neutralisation ne s'elargit pas aux tiers.
    """
    base = _stamped_snapshot("")
    base["comments"].pop()
    snapshot = _stamped_snapshot(_dossier_for(base))
    human = _comment("une remarque de fond sur le scope", login="clusterManager-Myia")
    human["createdAt"] = T1
    snapshot["comments"].append(human)
    errors = _errors(snapshot)
    assert any("discussion changed after dossier" in e for e in errors)


def test_copied_marker_by_other_author_still_expires_the_dossier():
    """#17818 acceptance (negative control) : l'AUTEUR compte, pas le texte
    seul. Un tiers qui recopie le marqueur PR-PATH-COLLISION en tete de son
    commentaire perime le dossier -- le suffixe ``[bot]`` est reserve aux
    comptes d'app GitHub, un humain ne peut pas le porter.
    """
    for login in ("myia-po-2023", "jsboige-bot-impersonator", "clusterManager-Myia"):
        base = _stamped_snapshot("")
        base["comments"].pop()
        snapshot = _stamped_snapshot(_dossier_for(base))
        copied = _comment(
            "<!-- PR-PATH-COLLISION:START -->\ncorps recopie par un tiers",
            login=login,
        )
        copied["createdAt"] = T1
        snapshot["comments"].append(copied)
        errors = _errors(snapshot)
        assert any("discussion changed after dossier" in e for e in errors), login


def test_shared_login_lift_does_not_expire_dossier():
    """#16883 CN4-bis: a coordinator lift posted under SHARED_GITHUB_LOGIN
    (the merged-account mandate, every lane signs ``jsboige``) is
    recognised as the coordinator's voice. The dossier stays intact and
    its READY verdict still passes the gate.
    """
    base = _stamped_snapshot("")
    base["comments"].pop()
    snapshot = _stamped_snapshot(_dossier_for(base))
    own = _comment("Lifting the stale PREFLIGHT_HOLD.", login=mod.SHARED_GITHUB_LOGIN)
    own["createdAt"] = T1
    snapshot["comments"].append(own)
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_shared_login_anterior_comment_does_not_neutralise():
    """#16883 CN2-bis: a SHARED_GITHUB_LOGIN comment written BEFORE the
    dossier is part of the surfaces the dossier attested. The adjoint
    already saw it; the dossier stays intact. (The neutrality only fires
    on later rows, never on attested ones.)
    """
    snapshot = _base_snapshot()
    anterior = _comment("pre-dossier coordinator remark", login=mod.SHARED_GITHUB_LOGIN)
    anterior["createdAt"] = T0
    snapshot["comments"].insert(0, anterior)
    dossier_body = _dossier_for(snapshot)
    dossier = _comment(dossier_body)
    dossier["createdAt"] = T0
    snapshot["comments"].append(dossier)
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_fingerprint_includes_lift_surface():
    """The fingerprint (#16957) covers every comment -- coordinator or not.
    A lift that lands between the dossier and the gate re-evaluation
    changes the hash; that is the dossier attesting the new surface.
    Neutralisation is only at evaluate time, never at stamp time.
    """
    base = _stamped_snapshot("")
    base["comments"].pop()
    snapshot_at_stamp = _stamped_snapshot(_dossier_for(base))
    fp_at_stamp = mod.surfaces_fingerprint(snapshot_at_stamp)

    snapshot_after_lift = json.loads(json.dumps(snapshot_at_stamp))
    lift = _comment("LIFT -- shared login", login=mod.SHARED_GITHUB_LOGIN)
    lift["createdAt"] = T1
    snapshot_after_lift["comments"].append(lift)

    fp_after_lift = mod.surfaces_fingerprint(snapshot_after_lift)
    assert fp_after_lift != fp_at_stamp


def test_coordinator_review_BEFORE_the_dossier_must_still_be_attested():
    """Neutrality is bounded by time, not by identity alone.

    A coordinator reserve posted before the dossier is exactly what the adjoint
    must have read; neutralising it by author would let a dossier ignore a live
    CHANGES_REQUESTED.
    """
    base = _stamped_snapshot("")
    base["comments"].pop()
    stale_body = _dossier_for(base)
    snapshot = _stamped_snapshot(stale_body)
    snapshot["reviews"].append(
        {"state": "CHANGES_REQUESTED", "author": {"login": mod.COORDINATOR_LOGIN},
         "submittedAt": "2026-09-18T00:00:00Z", "body": "reserve posee AVANT le dossier"}
    )
    assert _errors(snapshot)


# --- Checks are re-verified, not hashed (#16957) --------------------------------
#
# Measured trap this closes: `perimeter review guard (#11268)` starts on a
# review, the adjoint posts the dossier while the guard is in flight, the
# guard concludes SUCCESS -- and the stamp expired on a check nobody wrote.
# 7 of the 54 dossiers at exact head died of this, 4 of them on the same
# guard within three seconds of each other. Hashing the check state both
# guaranteed that race and certified nothing about the `checks:` claim.


def test_check_completing_green_after_dossier_does_not_expire_it():
    """Positive control: a green conclusion after the stamp must not kill it."""
    snapshot = _snapshot(_body())
    snapshot["checkRuns"].append(
        {"id": 2, "name": "perimeter review guard (#11268)",
         "status": "completed", "conclusion": "success",
         "started_at": "2026-09-20T11:14:54Z",
         "output": {"title": "perimeter review guard -- pass"}}
    )
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_green_check_landing_after_the_stamp_keeps_ready():
    """Only the per-name latest-wins verdicts of the head's check-runs matter:
    a green run appearing after the stamp neither expires the dossier nor
    contradicts its `latest-wins-green` claim."""
    snapshot = _snapshot(_body())
    snapshot["checkRuns"].append(
        {"id": 2, "name": "perimeter review guard (#11268)",
         "status": "completed", "conclusion": "success",
         "started_at": "2026-09-20T11:14:54Z", "output": {}}
    )
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_red_check_refuses_ready_naming_the_check():
    """A red conclusion after the stamp is caught BY NAME, not by hash drift."""
    snapshot = _snapshot(_body())
    snapshot["checkRuns"] = [
        {"id": 3, "name": "PR gate", "status": "completed",
         "conclusion": "failure", "started_at": "2026-09-20T12:00:00Z",
         "output": {"title": "FAIL -- failing checks: notebook-validate"}}
    ]
    errors = _errors(snapshot)
    assert any(
        "checks claim 'latest-wins-green' is contradicted by live check "
        "'PR gate' (failure; FAIL -- failing checks: notebook-validate)" in error
        for error in errors
    )


def test_lying_dossier_claiming_green_over_a_red_head_is_refused():
    """Decisive negative control: the claim itself is verified.

    Pre-#16957 the hash certified the check STATE at stamp time but never that
    `checks: latest-wins-green` matched it: a dossier could claim green on a
    red head and pass, as long as nobody posted after it. Built with the
    fingerprint computed over the red live state, so ONLY the claim
    verification can refuse it.
    """
    live = _base_snapshot()
    live["checkRuns"] = [
        {"id": 1, "name": "notebook-validate", "status": "completed",
         "conclusion": "failure", "started_at": "2026-09-20T10:00:00Z",
         "output": {}}
    ]
    dossier = _body(**{"surfaces-sha256": mod.surfaces_fingerprint(live)})
    live["comments"].append(_comment(dossier))
    errors = _errors(live)
    assert any(
        "contradicted by live check 'notebook-validate' (failure)" in error
        for error in errors
    )


def test_latest_wins_picks_the_most_recent_completed_run_per_name():
    """The rollup-twin trap: a cancelled older run must not paint the head red."""
    snapshot = _snapshot(_body())
    snapshot["checkRuns"] = [
        {"id": 1, "name": "PR gate", "status": "completed",
         "conclusion": "cancelled", "started_at": "2026-09-20T10:00:00Z"},
        {"id": 2, "name": "PR gate", "status": "completed",
         "conclusion": "success", "started_at": "2026-09-20T10:05:00Z"},
    ]
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_latest_wins_red_older_run_loses_to_newer_green():
    snapshot = _snapshot(_body())
    snapshot["checkRuns"] = [
        {"id": 1, "name": "PR gate", "status": "completed",
         "conclusion": "failure", "started_at": "2026-09-20T10:00:00Z"},
        {"id": 2, "name": "PR gate", "status": "completed",
         "conclusion": "success", "started_at": "2026-09-20T10:05:00Z"},
    ]
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_skipped_and_neutral_conclusions_are_not_red():
    snapshot = _snapshot(_body())
    snapshot["checkRuns"] = [
        {"id": 1, "name": "codeql", "status": "completed",
         "conclusion": "skipped", "started_at": "2026-09-20T10:00:00Z"},
        {"id": 2, "name": "coverage", "status": "completed",
         "conclusion": "neutral", "started_at": "2026-09-20T10:01:00Z"},
        {"id": 3, "name": "PR gate", "status": "completed",
         "conclusion": "success", "started_at": "2026-09-20T10:02:00Z"},
    ]
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


_CODEQL_ONLY = [
    {"id": i, "name": name, "status": "completed", "conclusion": "success",
     "started_at": "2026-09-30T04:30:40Z"}
    for i, name in enumerate(
        ["Analyze (actions)", "Analyze (csharp)", "Analyze (python)", "CodeQL"],
        start=1,
    )
]
_ABSENT_PR_GATE = (
    "checks claim 'latest-wins-green' is contradicted by the absence of "
    "required check 'PR gate' on the head"
)


def test_head_without_pr_gate_run_is_not_green_by_vacuity():
    """#18579 founding case (#18527, #18500): the pull_request workflows never
    fired on the head, only the CodeQL legs ran. Every present check is green,
    so pre-#18579 nothing contradicted the claim and the dossier read READY."""
    snapshot = _snapshot(_body())
    snapshot["checkRuns"] = list(_CODEQL_ONLY)
    errors = _errors(snapshot)
    assert any(_ABSENT_PR_GATE in error for error in errors), errors


def test_head_with_no_check_run_at_all_is_not_green():
    snapshot = _snapshot(_body())
    snapshot["checkRuns"] = []
    errors = _errors(snapshot)
    assert any(_ABSENT_PR_GATE in error for error in errors), errors


def test_pr_gate_in_flight_without_completed_run_is_not_green():
    """In flight has no verdict yet: with no earlier completed run on the head,
    the required check has said nothing and cannot be claimed green."""
    snapshot = _snapshot(_body())
    snapshot["checkRuns"] = list(_CODEQL_ONLY) + [
        {"id": 9, "name": "PR gate", "status": "in_progress",
         "conclusion": None, "started_at": "2026-09-30T10:20:00Z"}
    ]
    errors = _errors(snapshot)
    assert any(_ABSENT_PR_GATE in error for error in errors), errors


def test_pr_gate_rerun_in_flight_keeps_the_last_completed_green():
    """Positive control: a rerun in flight falls back to the last completed
    run of the same head, which is green -- the presence rule adds nothing."""
    snapshot = _snapshot(_body())
    snapshot["checkRuns"] = list(_CODEQL_ONLY) + [
        {"id": 8, "name": "PR gate", "status": "completed",
         "conclusion": "success", "started_at": "2026-09-30T10:00:00Z"},
        {"id": 9, "name": "PR gate", "status": "in_progress",
         "conclusion": None, "started_at": "2026-09-30T10:20:00Z"},
    ]
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_blocked_dossier_is_not_refused_for_an_absent_pr_gate():
    """The presence rule refutes a READY claim only: a BLOCKED dossier on a
    head without CI stays readable (exit 3), it is the reason it is blocked."""
    assert mod.check_claim_contradictions("BLOCKED", []) == []


def test_in_flight_rerun_has_no_verdict_and_hides_nothing():
    """A rerun still in flight cannot veto; the last completed verdict stands --
    green stays ready, red stays refused."""
    green = _snapshot(_body())
    green["checkRuns"].append(
        {"id": 9, "name": "PR gate", "status": "in_progress",
         "conclusion": None, "started_at": "2026-09-20T13:00:00Z"}
    )
    verdict, errors = mod.evaluate(green)
    assert verdict == mod.VERDICT_READY, errors

    red = _snapshot(_body())
    red["checkRuns"] = [
        {"id": 1, "name": "PR gate", "status": "completed",
         "conclusion": "failure", "started_at": "2026-09-20T10:00:00Z"},
        {"id": 2, "name": "PR gate", "status": "in_progress",
         "conclusion": None, "started_at": "2026-09-20T13:00:00Z"},
    ]
    assert any("'PR gate'" in error for error in _errors(red))


def test_blocked_dossier_is_not_refuted_by_a_red_check():
    """Claim verification targets the READY claim; a BLOCKED dossier attesting a
    red head is honest and stays a valid dossier (exit 3 semantics, #16800)."""
    live = _base_snapshot()
    live["checkRuns"] = [
        {"id": 1, "name": "PR gate", "status": "completed",
         "conclusion": "failure", "started_at": "2026-09-20T10:00:00Z",
         "output": {"title": "DWELL -- leve au premier balayage"}}
    ]
    dossier = _body(
        verdict="BLOCKED", b0="blocked", checks="BLOCKED", scope="pass",
        domain="not-applicable",
        **{"surfaces-sha256": mod.surfaces_fingerprint(live)},
    )
    live["comments"].append(_comment(dossier))
    verdict, errors = mod.evaluate(live)
    assert verdict == mod.VERDICT_BLOCKED, errors


def test_retired_legacy_stamp_needs_a_mechanical_restamp():
    """#17315: the pre-#16957 fingerprint is retired with its last carrier.

    Both carriers merged (#16950/#16891), so a dossier still stamped with it
    matches neither live digest. The organ fails CLOSED and names the single
    recovery: a mechanical `--template` re-stamp.
    """
    assert not hasattr(mod, "legacy_surfaces_fingerprint")
    # A stamp matching neither accepted digest is the shape of a retired-legacy
    # dossier: fail CLOSED, with the one gesture that can recover it named.
    snapshot = _snapshot(_body(**{"surfaces-sha256": "a" * 64}))
    errors = _errors(snapshot)
    assert any(
        "discussion surfaces changed" in error and "--template re-stamp" in error
        for error in errors
    )


def test_surfaces_fingerprint_is_insensitive_to_check_state():
    """The live digest must not move when only checks move -- that is the race
    being closed. Nothing else in the module hashes check state either."""
    base = _base_snapshot()
    moved = _base_snapshot()
    moved["checkRuns"][0]["conclusion"] = "failure"
    assert mod.surfaces_fingerprint(base) == mod.surfaces_fingerprint(moved)
    assert mod.pre18637_surfaces_fingerprint(base) == mod.pre18637_surfaces_fingerprint(moved)


def test_template_renders_the_emitting_lane_not_a_borrowed_name():
    """A lane renders its OWN name, or the self-attestation refusal is defeated.

    A template hardcoding one lane hands every other lane a dossier declaring a
    name that is not its own. The carrying lane could then prevalidate itself
    under a borrowed name and `validate_dossier` would see two different lanes.
    """
    for lane in ("myia-po-2027:CoursIA", "myia-po-2023:CoursIA"):
        template = mod.render_template(_base_snapshot(), lane)
        assert f"lane: {lane}" in template, lane


def test_template_lane_defaults_to_the_adjoint():
    """The adjoint stays the canonical emitter: the default is unchanged."""
    assert f"lane: {mod.ADJOINT_LANE}" in mod.render_template(_base_snapshot())


# ------------------------------------------- the attested reason, exposed (#17290)
#
# On exit 3 the dossier is INTACT -- that is what the code means -- so `errors`
# is [] by construction. The rule then tells the coordinator to "dispatch from
# the dossier's stated reason" while publishing none of it, and re-parsing the
# dossier comment by hand is the only way out. Measured cost: 13 PRs at rc=3 in
# one cycle, 6 of them with a reason that was already dead.
#
# Exposing it must not weaken the gate: a REFUSED dossier is not a fainter
# dossier, and must publish nothing at all.


def test_blocking_fields_name_checks_on_a_checks_blocked_dossier():
    """Controle positif 1 : `checks: BLOCKED`, `b0: clear` -> ["checks"]."""
    snapshot = _snapshot(_body(verdict="BLOCKED", checks="BLOCKED"))
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    assert (verdict, errors) == (mod.VERDICT_BLOCKED, [])
    assert mod.blocking_fields(dossier) == ["checks"]


def test_blocking_fields_name_b0_on_a_b0_blocked_dossier():
    """Controle positif 2 : `b0: blocked`, `checks: latest-wins-green` -> ["b0"].

    The two reasons send the work to DIFFERENT places -- a dead `checks` goes to
    the adjoint for a `--template`, a real `b0` goes to the carrying lane for a
    lift sentence. Telling them apart is the whole point of the exposure.
    """
    snapshot = _snapshot(_body(verdict="BLOCKED", b0="blocked"))
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    assert (verdict, errors) == (mod.VERDICT_BLOCKED, [])
    assert mod.blocking_fields(dossier) == ["b0"]


def test_blocking_fields_are_listed_in_the_contract_order():
    """A dossier blocked on every field orders them the way the contract does."""
    snapshot = _snapshot(
        _body(verdict="BLOCKED", checks="BLOCKED", b0="blocked", scope="fail",
              domain="fail")
    )
    _, _, dossier = mod.evaluate_with_dossier(snapshot)
    assert mod.blocking_fields(dossier) == ["checks", "b0", "scope", "domain"]


def test_a_blocked_dossier_naming_no_blocking_field_is_refused():
    """#17887 : un BLOCKED a champs tous verts n'est plus un dossier.

    Le contrat l'autorisait (motif en prose, `blocking_fields == []`). Mesure sur
    #17743 @bf7a086e : il etait inerte, ai-01 ne pouvait ni merger ni dispatcher
    depuis lui. Le gate le refuse desormais (exit 1) et dit quoi faire : pas de
    dossier, HOLD a la lane porteuse.
    """
    snapshot = _snapshot(_body(verdict="BLOCKED"))
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    assert verdict == "" and dossier is None
    assert any("names no blocking field" in e and "#17887" in e for e in errors), errors


def test_a_blocked_dossier_naming_one_field_stays_exit_3():
    """Controle negatif de #17887 : nommer un seul champ bloquant suffit."""
    for field, value in (("checks", "BLOCKED"), ("b0", "blocked"),
                         ("scope", "fail"), ("domain", "fail")):
        snapshot = _snapshot(_body(verdict="BLOCKED", **{field: value}))
        verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
        assert (verdict, errors) == (mod.VERDICT_BLOCKED, []), (field, errors)
        assert mod.blocking_fields(dossier) == [field]


def test_ready_result_publishes_the_dossier_with_no_blocker():
    """Acceptance: rc=0 carries the same block, with `blocking_fields: []`."""
    snapshot = _snapshot(_body())
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    result = mod.build_result(123, snapshot, verdict, errors, dossier)
    assert result["verdict"] == mod.VERDICT_READY
    assert result["ready"] is True
    assert result["blocking_fields"] == []
    assert result["dossier"]["checks"] == "latest-wins-green"


def test_blocked_result_publishes_the_dossier_and_its_blocker():
    """Acceptance: rc=3 exposes the parsed dossier and a non-empty blocker."""
    snapshot = _snapshot(_body(verdict="BLOCKED", checks="BLOCKED"))
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    result = mod.build_result(123, snapshot, verdict, errors, dossier)
    assert result["verdict"] == mod.VERDICT_BLOCKED
    assert result["blocking_fields"] == ["checks"]
    assert result["dossier"]["lane"] == "myia-po-2025:CoursIA-2"
    assert result["dossier"]["head"] == HEAD
    assert result["dossier"]["comment_index"] == 1


def test_a_refused_dossier_is_not_published_at_all():
    """Controle NEGATIF -- the exposure must not launder a refused dossier.

    A dossier whose fingerprint no longer covers the live surfaces is refused
    (rc=1). If the payload published its parsed fields anyway, a referee reading
    the JSON would see a lane, a head and a verdict for a PR the gate just
    rejected -- exactly the confusion the refusal exists to prevent.
    """
    snapshot = _snapshot(_body())
    snapshot["title"] = "mutated after the stamp"
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    assert verdict == "" and dossier is None
    assert errors, "a perimed fingerprint must still be refused"
    result = mod.build_result(123, snapshot, verdict, errors, dossier)
    assert result["verdict"] == "NO_DOSSIER"
    assert "dossier" not in result
    assert "blocking_fields" not in result


def test_dossier_payload_publishes_every_read_field():
    """Acceptance: "tous les champs lus" -- the whole contract, not a subset.

    Publishing a curated handful would leave the next consumer re-parsing the
    comment for the field that was left out, which is the defect itself.
    """
    dossier, parse_errors = mod.parse_dossier(_body(), 1, "jsboige", T0)
    assert parse_errors == []
    payload = mod.dossier_payload(dossier)
    assert mod.REQUIRED_FIELDS <= set(payload)
    assert payload["author"] == "jsboige"
    assert payload["created_at"] == T0


def test_result_is_json_serializable():
    """`--json` must actually serialize: a Dossier is not a dict."""
    snapshot = _snapshot(_body(verdict="BLOCKED", b0="blocked"))
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    result = mod.build_result(123, snapshot, verdict, errors, dossier)
    decoded = json.loads(json.dumps(result, ensure_ascii=False))
    assert decoded["dossier"]["b0"] == "blocked"


def test_evaluate_keeps_its_two_tuple_shape():
    """The gate's historical view is unchanged: no caller moves under it."""
    verdict, errors = mod.evaluate(_snapshot(_body()))
    assert (verdict, errors) == (mod.VERDICT_READY, [])

# --- #16931 : reecriture en place d'un bot marker-garde = fingerprint STABLE --


def test_marker_guarded_bot_rewrite_keeps_the_fingerprint():
    """Un bot qui re-edite son commentaire en place ne perime plus le dossier.

    Mesure fondatrice (2026-09-20) : le dossier de #16907 a ete perime 26 min
    apres sa pose par une reecriture `PR-PATH-COLLISION` du bot -- le compte
    de commentaires etait exact, seul le hash bougeait. Le corps d'un
    commentaire dont la premiere ligne est un marqueur HTML connu est hache
    sur ce marqueur SEUL : la presence du commentaire compte, sa
    re-implementation interne non.
    """
    base = _base_snapshot()
    v1 = dict(base)
    v1["comments"] = [_comment("<!-- PR-PATH-COLLISION:START -->\n"
                               "paires fortes: #123/#456 (chevauchent)",
                               "github-actions[bot]")]
    v2 = dict(base)
    v2["comments"] = [_comment("<!-- PR-PATH-COLLISION:START -->\n"
                               "paires fortes: #123/#789 (re-scan apres push)",
                               "github-actions[bot]")]
    assert mod.surfaces_fingerprint(v1) == mod.surfaces_fingerprint(v2)


def test_marker_guarded_variation_signals_and_cap_also_stable():
    """Les 3 marqueurs mesures sont neutralises, pas seulement le fondateur."""
    base = _base_snapshot()
    for marker in ("<!-- variation-genre-signals -->",
                   "<!-- gvar2-light-cap -->",
                   "<!-- trivial-diff-15740 -->"):
        a = dict(base, comments=[_comment(marker + "\ncontenu v1", "github-actions[bot]")])
        b = dict(base, comments=[_comment(marker + "\ncontenu v2 totalement different",
                                          "github-actions[bot]")])
        assert mod.surfaces_fingerprint(a) == mod.surfaces_fingerprint(b), marker


def test_marker_guarded_bot_comment_presence_still_counts():
    """Ajouter ou retirer le commentaire garde change toujours le hash."""
    base = _base_snapshot()
    with_bot = dict(base, comments=list(base["comments"]) + [
        _comment("<!-- PR-PATH-COLLISION:START -->\npaires: aucune",
                 "github-actions[bot]")])
    assert mod.surfaces_fingerprint(base) != mod.surfaces_fingerprint(with_bot)


def test_human_edit_of_the_same_body_still_changes_the_fingerprint():
    """Fail-closed symetrique : un contenu qui n'est PAS un bot garde change.

    Le refus « discussion surfaces changed » reste le verdict nominal quand un
    commentaire humain est edite : l'allowlist ne couvre que les corps qui
    COMMENCENT par le marqueur, et le marqueur seul est hache -- tout le
    contenu humain, partout ailleurs, continue de perimer le dossier.
    """
    base = _base_snapshot()
    v1 = dict(base, comments=[_comment("reserve: verifier le diff", "jsboige")])
    v2 = dict(base, comments=[_comment("reserve: verifier le diff, corrige", "jsboige")])
    assert mod.surfaces_fingerprint(v1) != mod.surfaces_fingerprint(v2)
    # Marqueur non plus a l'offset 0 = edition humaine d'un corps de bot :
    v3 = dict(base, comments=[_comment("edit: <!-- PR-PATH-COLLISION:START -->\n...",
                                       "jsboige")])
    v4 = dict(base, comments=[_comment("edit2: <!-- PR-PATH-COLLISION:START -->\n...",
                                       "jsboige")])
    assert mod.surfaces_fingerprint(v3) != mod.surfaces_fingerprint(v4)


def test_fingerprint_refusal_names_the_live_surface_landscape():
    """Le refus d'empreinte est exploitable : il nomme OU chercher (#16931 defaut 3).

    Deux hachages opaques forcent une re-fabrication en aveugle. Le refus doit
    reporter le PAYSAGE des surfaces live (compte + dernier commentaire/review
    + threads non resolus), pour que la lane identifie la divergence sans
    refaire toute la lecture B.0. L'empreinte divergente reste un REFUS
    (fail-closed preserve) — seul le diagnostic est ajoute.
    """
    base = _base_snapshot()
    # Snapshot dont la fingerprint ne reproduit pas celle du dossier
    # (un commentaire humain edite, cf test precedent).
    live = dict(base)
    live["comments"] = [
        {"author": {"login": "jsboige"}, "createdAt": "2026-09-19T20:00:00Z",
         "body": "un commentaire edite apres le dossier"}
    ]
    live["threads"] = [{"isResolved": True}, {"isResolved": False}]
    # Dossier calcule sur le snapshot de base, compare au live divergent.
    dossier_fields = {
        "schema": "1", "lane": mod.ADJOINT_LANE, "pr": "123", "head": HEAD,
        "complete": "true", "body": "read", "comments-reviewed": "1",
        "reviews-reviewed": "2", "threads-reviewed": "1",
        "threads-unresolved": "0",
        "surfaces-sha256": mod.surfaces_fingerprint(base, 1, None),
        "diff-files": "3", "diff-additions": "42", "diff-deletions": "7",
        "checks": "latest-wins-green", "b0": "clear", "scope": "pass",
        "domain": "pass", "verdict": "READY",
    }
    dossier = mod.Dossier(dossier_fields, 1, mod.SHARED_GITHUB_LOGIN, "2026-09-19T19:00:00Z")
    errors = mod.validate_dossier(dossier, live)
    fingerprint_errors = [e for e in errors if "discussion surfaces changed" in e]
    assert fingerprint_errors, f"no fingerprint error in: {errors}"
    msg = fingerprint_errors[0]
    # Nomme le paysage live : dernier commentaire et sa date, threads, checks.
    assert "dernier commentaire: jsboige 2026-09-19T20:00:00Z" in msg
    assert "threads=2 (1 non resolus)" in msg
    assert "checks=1" in msg
    assert "reviews=2" in msg


# --- Campagnes gelees par veto user (#17040) ----------------------------------

# Titres reels (2026-09-23/24) : le second repare les degats d'une campagne
# gelee et cite le parapluie dans son body -- l'exemption se lit sur le
# titre seul (module partage frozen_campaigns). #13410 ROUVERT le 2026-10-07 :
# le gel se mesure sur #11601, seul parapluie gele en vie.
FROZEN_TITLE = "enrich(qc,#11601): densite QC-Py-06b"
REDRESSEMENT_TITLE = (
    "fix(semanticweb,#17066): redressement critique de SW-4-CSharp-SPARQL "
    "-- reference de campagne"
)


def _snapshot_with(
    title: str | None = None,
    pr_body: str | None = None,
    head_ref: str | None = None,
    **dossier_changes: str,
) -> dict:
    """Snapshot a titre/body/branche libres, atteste par un dossier SUR CES
    surfaces-là : ``surfaces-sha256`` couvre titre et body, la fingerprint se
    prend donc APRES mutation (head_ref n'est pas hashe, cf test ci-dessous).
    """
    snapshot = _base_snapshot()
    if title is not None:
        snapshot["title"] = title
    if pr_body is not None:
        snapshot["body"] = pr_body
    if head_ref is not None:
        snapshot["headRefName"] = head_ref
    fields = dict(dossier_changes)
    fields["surfaces-sha256"] = mod.surfaces_fingerprint(snapshot)
    snapshot["comments"].append(_comment(_body(**fields)))
    return snapshot


def _run_main(monkeypatch, snapshot: dict, *extra_args: str) -> int:
    """``main()`` sur un snapshot fige : argv patche, ``GH_TOKEN`` pose
    (``pin_gh_token`` ne touche alors pas au reseau), snapshot substitue."""
    monkeypatch.setattr(
        sys, "argv", ["check_adjoint_prevalidation.py", "123", *extra_args]
    )
    monkeypatch.setattr(mod, "load_snapshot", lambda pr: snapshot)
    # Depuis #17698 le gate re-mesure un `b0: clear` contre l'organe B.0 :
    # ces tests portent sur le gel, l'organe est donc fige d'accord.
    monkeypatch.setattr(mod, "probe_b0", lambda pr: {"blocked": False, "blocking": []})
    monkeypatch.setenv("GH_TOKEN", "tok-fake-gate-test")
    return mod.main()


def test_ready_dossier_on_frozen_campaign_returns_rc3(monkeypatch, capsys):
    """Un dossier READY n'autorise pas a merger une PR gelee (#17021).

    Le veto ne vit sur aucune surface que le dossier couvre : le gate le lit
    au verdict et rend rc=3 -- l'action documentee (ne pas merger, dispatcher
    a la lane auteure), pas un rc inedit.
    """
    snapshot = _snapshot_with(title=FROZEN_TITLE, head_ref="feature/densite-13")
    rc = _run_main(monkeypatch, snapshot)
    assert rc == mod.EXIT_BLOCKED_WITH_SUBSTANCE
    out = capsys.readouterr().out
    assert out.startswith(
        "FROZEN -- PR #123 belongs to a frozen campaign "
        "(frozen:#11601(veto #17040)); do not merge, dispatch to the lane author."
    )


def test_ready_dossier_frozen_json_payload(monkeypatch, capsys):
    """Mode --json : ready faux, verdict FROZEN, raison nommee -- et le
    dossier reste publie (le gate refuse le MERGE, pas la lecture)."""
    snapshot = _snapshot_with(title=FROZEN_TITLE)
    rc = _run_main(monkeypatch, snapshot, "--json")
    assert rc == mod.EXIT_BLOCKED_WITH_SUBSTANCE
    payload = json.loads(capsys.readouterr().out)
    assert payload["ready"] is False
    assert payload["verdict"] == "FROZEN"
    assert payload["frozen"] == "frozen:#11601(veto #17040)"
    assert payload["dossier"]["verdict"] == "READY"


def test_ready_redressement_citing_the_umbrella_stays_rc0(monkeypatch, capsys):
    """Redressement : le titre exempte du gel, meme quand le body cite
    #11601 -- sinon la PR qui REPARE les degats ne serait plus mergeable."""
    snapshot = _snapshot_with(
        title=REDRESSEMENT_TITLE,
        pr_body=_base_snapshot()["body"] + "\n\nSee #11601 (densite QC).",
    )
    rc = _run_main(monkeypatch, snapshot)
    assert rc == mod.EXIT_READY
    assert capsys.readouterr().out.startswith("READY -- PR #123")


def test_ready_dossier_on_wt_vibe_branch_after_reopening(monkeypatch, capsys):
    """Reouverture user de #13410 (2026-10-07) : les relais wt/vibe-* ne
    gelent plus -- un dossier READY sur ces branches redevient READY. Le
    mecanisme de gel par prefixe reste prouve par test_frozen_campaigns
    (donnees injectees)."""
    snapshot = _snapshot_with(head_ref="wt/vibe-g77-search-26")
    rc = _run_main(monkeypatch, snapshot)
    assert rc == mod.EXIT_READY
    assert capsys.readouterr().out.startswith("READY -- PR #123")


def test_blocked_dossier_on_frozen_campaign_keeps_its_own_message(
    monkeypatch, capsys
):
    """Le gel ne re-ecrit pas un verdict BLOCKED : deja non mergeable, il
    garde son message propre (l'exemption READY-only du check). Le dossier
    porte un second motif (checks) : le re-jeu B.0 de #19093 ne l'expire pas,
    on teste bien le gel sur un BLOCKED intact."""
    snapshot = _snapshot_with(
        title=FROZEN_TITLE,
        verdict="BLOCKED",
        b0="blocked",
        checks="BLOCKED:gate rouge",
    )
    rc = _run_main(monkeypatch, snapshot)
    assert rc == mod.EXIT_BLOCKED_WITH_SUBSTANCE
    assert capsys.readouterr().out.startswith("BLOCKED-WITH-SUBSTANCE")


def test_no_dossier_on_frozen_campaign_keeps_rc1(monkeypatch, capsys):
    """Sans dossier digne de confiance : rc=1 inchange, le gel n'y ajoute
    rien (la PR est deja non mergeable par absence de dossier)."""
    snapshot = _base_snapshot()
    snapshot["title"] = FROZEN_TITLE
    snapshot["headRefName"] = "feature/densite-13"
    rc = _run_main(monkeypatch, snapshot)
    assert rc == mod.EXIT_NO_DOSSIER
    assert capsys.readouterr().out.startswith("NO-DOSSIER")


def test_headrefname_does_not_change_the_fingerprint():
    """headRefName est lu pour le gel mais PAS hashe : un dossier stampe
    avant l'ajout du champ reste valide (surfaces-sha256 inchangee)."""
    snapshot = _snapshot_with(title=FROZEN_TITLE)
    before = mod.surfaces_fingerprint(snapshot)
    snapshot["headRefName"] = "wt/vibe-g77-search-26"
    assert mod.surfaces_fingerprint(snapshot) == before
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY


# --- b0 claim re-verified against the live B.0 organ -------------------------
# Measured 2026-09-24: READY dossiers on #16955 and #16987 declared `b0: clear`
# while check_unaddressed_nits.py exited 1. The gate answered exit 0 on both.


def _ready_dossier(**changes: str):
    snapshot = _snapshot(_body(**changes))
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    assert verdict == mod.VERDICT_READY, errors
    return verdict, dossier


def _organ(blocked: bool, blocking: list | None = None):
    calls = []

    def probe(pr):
        calls.append(pr)
        return {"blocked": blocked, "blocking": blocking or []}

    return probe, calls


def test_b0_clear_refuted_by_organ_demotes_ready_and_names_the_remark():
    verdict, dossier = _ready_dossier()
    probe, calls = _organ(
        True,
        [{"kind": "concern", "author": "jsboige", "src": "review 2026-09-22"}],
    )
    verdict, errors, dossier = mod.refute_ready_b0(123, verdict, dossier, probe)
    assert calls == [123]
    assert verdict == "" and dossier is None
    assert len(errors) == 1
    assert "b0 claim 'clear' is contradicted" in errors[0]
    assert "concern by jsboige via review 2026-09-22" in errors[0]


def test_b0_clear_confirmed_by_organ_keeps_ready():
    verdict, dossier = _ready_dossier()
    probe, calls = _organ(False)
    out = mod.refute_ready_b0(123, verdict, dossier, probe)
    assert calls == [123]
    assert out == (mod.VERDICT_READY, [], dossier)


def test_b0_probe_not_paid_for_blocked_or_absent_dossier():
    probe, calls = _organ(True, [{"kind": "k", "author": "a", "src": "s"}])
    assert mod.refute_ready_b0(123, mod.VERDICT_BLOCKED, None, probe)[0] == mod.VERDICT_BLOCKED
    assert mod.refute_ready_b0(123, "", None, probe) == ("", [], None)
    assert calls == []


def test_b0_contradictions_ignore_a_non_clear_claim_and_cap_the_list():
    rows = [{"kind": f"k{i}", "author": "a", "src": "s"} for i in range(7)]
    assert mod.b0_claim_contradictions("blocked", {"blocked": True, "blocking": rows}) == []
    assert mod.b0_claim_contradictions("clear", None) == []
    [error] = mod.b0_claim_contradictions("clear", {"blocked": True, "blocking": rows})
    assert "7 unlifted remark(s)" in error and "(+2 more)" in error


def test_b0_probe_failure_is_fail_closed(monkeypatch):
    class Broken:
        @staticmethod
        def analyse_pr(pr):
            raise ValueError("network down")

    monkeypatch.setitem(sys.modules, "check_unaddressed_nits", Broken)
    with pytest.raises(RuntimeError, match="B.0 organ could not measure PR #123"):
        mod.probe_b0(123)



def test_b0_probe_import_failure_is_fail_closed(monkeypatch):
    """An organ that cannot even be imported is 'not measured' (UNKNOWN), not a traceback."""
    import builtins

    real_import = builtins.__import__

    def refuse(name, *args, **kwargs):
        if name == "check_unaddressed_nits":
            raise ImportError("organ missing")
        return real_import(name, *args, **kwargs)

    monkeypatch.delitem(sys.modules, "check_unaddressed_nits", raising=False)
    monkeypatch.setattr(builtins, "__import__", refuse)
    with pytest.raises(RuntimeError, match="B.0 organ could not measure PR #123"):
        mod.probe_b0(123)


def test_main_exits_unknown_when_organ_cannot_be_imported(monkeypatch, capsys):
    snapshot = _snapshot(_body())
    monkeypatch.setattr(mod, "load_snapshot", lambda pr: snapshot)
    monkeypatch.setattr(mod.gh_identity, "pin_gh_token", lambda: None)

    def unmeasured(pr):
        raise RuntimeError(f"B.0 organ could not measure PR #{pr}: organ missing")

    monkeypatch.setattr(mod, "probe_b0", unmeasured)
    monkeypatch.setattr(sys, "argv", ["check_adjoint_prevalidation.py", "123"])
    assert mod.main() == mod.EXIT_UNKNOWN
    assert "UNKNOWN" in capsys.readouterr().out

def test_main_exits_no_dossier_when_organ_refutes_b0(monkeypatch, capsys):
    snapshot = _snapshot(_body())
    monkeypatch.setattr(mod, "load_snapshot", lambda pr: snapshot)
    monkeypatch.setattr(mod.gh_identity, "pin_gh_token", lambda: None)
    monkeypatch.setattr(
        mod,
        "probe_b0",
        lambda pr: {"blocked": True, "blocking": [{"kind": "nit", "author": "u", "src": "c"}]},
    )
    monkeypatch.setattr(sys, "argv", ["check_adjoint_prevalidation.py", "123"])
    assert mod.main() == mod.EXIT_NO_DOSSIER
    out = capsys.readouterr().out
    assert "NO-DOSSIER" in out and "b0 claim 'clear' is contradicted" in out


def test_main_exits_ready_when_organ_agrees(monkeypatch, capsys):
    snapshot = _snapshot(_body())
    monkeypatch.setattr(mod, "load_snapshot", lambda pr: snapshot)
    monkeypatch.setattr(mod.gh_identity, "pin_gh_token", lambda: None)
    monkeypatch.setattr(mod, "probe_b0", lambda pr: {"blocked": False, "blocking": []})
    monkeypatch.setattr(sys, "argv", ["check_adjoint_prevalidation.py", "123"])
    assert mod.main() == mod.EXIT_READY


# --- #19093 : un dossier BLOCKED dont le seul motif b0 est eteint expire ------
# Mesure fondatrice (2026-10-04, #19012) : dossier BLOCKED 02:49Z pour une
# reserve de review, APPROVE coordinateur 06:13Z sur la meme tete, le gate
# repondait toujours rc=3 a 10:24Z -- la PR a dormi 4 h. La fingerprint
# neutralise les reviews posterieures du coordinateur (_is_own_later_act),
# donc sa levee n'expire pas le tampon : c'est le re-jeu de l'organe B.0 qui
# tranche, symetriquement au re-jeu des claims `b0: clear` (#17698).


def _blocked_b0_snapshot(**changes: str):
    """Dossier BLOCKED dont b0 est le SEUL champ bloquant (acceptance #19093)."""
    fields = {"verdict": "BLOCKED", "b0": "blocked:reserve vivante"}
    fields.update(changes)
    return _snapshot_with(**fields)


def test_blocked_b0_only_expired_when_organ_no_longer_blocks(monkeypatch, capsys):
    """Acceptance 1 : organ rc=0 -> le gate ne rend PAS 3 et nomme le re-tampon."""
    snapshot = _blocked_b0_snapshot()
    monkeypatch.setattr(mod, "load_snapshot", lambda pr: snapshot)
    monkeypatch.setattr(mod.gh_identity, "pin_gh_token", lambda: None)
    monkeypatch.setattr(mod, "probe_b0", lambda pr: {"blocked": False, "blocking": []})
    monkeypatch.setattr(sys, "argv", ["check_adjoint_prevalidation.py", "123"])
    assert mod.main() == mod.EXIT_NO_DOSSIER
    out = capsys.readouterr().out
    assert "NO-DOSSIER" in out
    assert "no longer blocks PR #123" in out
    assert "re-stamp" in out and "third-party lane" in out


def test_blocked_b0_only_stands_when_organ_still_blocks(monkeypatch, capsys):
    """Acceptance 2 (temoin negatif) : organ rc=1 -> le gate rend toujours 3."""
    snapshot = _blocked_b0_snapshot()
    monkeypatch.setattr(mod, "load_snapshot", lambda pr: snapshot)
    monkeypatch.setattr(mod.gh_identity, "pin_gh_token", lambda: None)
    monkeypatch.setattr(
        mod,
        "probe_b0",
        lambda pr: {"blocked": True, "blocking": [{"kind": "nit", "author": "u", "src": "c"}]},
    )
    monkeypatch.setattr(sys, "argv", ["check_adjoint_prevalidation.py", "123"])
    assert mod.main() == mod.EXIT_BLOCKED_WITH_SUBSTANCE
    assert capsys.readouterr().out.startswith("BLOCKED-WITH-SUBSTANCE")


def test_blocked_with_other_motif_not_touched_by_the_recheck(monkeypatch, capsys):
    """Acceptance 3 : un autre motif bloquant (checks) garde son dossier,
    meme quand l'organe B.0 ne bloque plus -- sa raison peut tenir encore."""
    snapshot = _blocked_b0_snapshot(checks="BLOCKED:gate rouge")
    monkeypatch.setattr(mod, "load_snapshot", lambda pr: snapshot)
    monkeypatch.setattr(mod.gh_identity, "pin_gh_token", lambda: None)
    monkeypatch.setattr(mod, "probe_b0", lambda pr: {"blocked": False, "blocking": []})
    monkeypatch.setattr(sys, "argv", ["check_adjoint_prevalidation.py", "123"])
    assert mod.main() == mod.EXIT_BLOCKED_WITH_SUBSTANCE
    assert capsys.readouterr().out.startswith("BLOCKED-WITH-SUBSTANCE")


def test_recheck_blocked_b0_never_probes_a_non_blocked_verdict():
    """Le probe n'est paye que pour un dossier BLOCKED existant : ni READY,
    ni dossier absent (symetrique de test_b0_probe_not_paid_...)."""
    probe, calls = _organ(False)
    verdict, dossier = _ready_dossier()
    assert mod.recheck_blocked_b0(123, verdict, dossier, probe) == (verdict, [], dossier)
    assert mod.recheck_blocked_b0(123, "", None, probe) == ("", [], None)
    assert calls == []


# --- #18637 : advisories sticky (marqueur en FIN de corps) et resumes de bot --

_STICKY_STALE = (
    "✅ No unanchored measurement claim detected in the notebooks this PR changed.\n\n"
    "Scope = notebooks CHANGED in this PR.\n"
    "<!-- Sticky Pull Request Commentstale-claim-advisory -->"
)


def test_sticky_advisory_pose_does_not_expire_the_dossier():
    """#18637 acceptance (positive control) : la pose d'un advisory sticky par
    ``github-actions[bot]`` apres le dossier laisse le verdict lisible. Mesure
    fondatrice (2026-09-30) : 19 dossiers sur 22 perimes par ces seules poses
    et reecritures de bot.
    """
    for body in (
        _STICKY_STALE,
        "⚠️ Factual-mislabel review needed.\n<!-- Sticky Pull Request Commentfactual-mislabel-advisory -->",
        "<!-- REVIEW-COVERAGE:START -->\nseuil depasse\n<!-- REVIEW-COVERAGE:END -->",
        "## Golden-Set Execution (H.7 P3)\n\n✅ **3/3** notebooks passed",
        "## Notebook PR Validation: PASS\n\n| nb | ok |",
        "## Notebook outputs-required (H.4 schema): **PASS** (every code cell carries an `outputs: list`)",
    ):
        base = _stamped_snapshot("")
        base["comments"].pop()
        snapshot = _stamped_snapshot(_dossier_for(base))
        pose = _comment(body, login="github-actions[bot]")
        pose["createdAt"] = T1
        snapshot["comments"].append(pose)
        verdict, errors = mod.evaluate(snapshot)
        assert verdict == mod.VERDICT_READY, (body.splitlines()[0], errors)


def test_sticky_advisory_rewrite_keeps_the_fingerprint():
    """#18637 : la reecriture en place d'un advisory sticky ne change pas le hash,
    sa presence le change toujours."""
    base = _base_snapshot()
    v1 = dict(base, comments=[_comment(_STICKY_STALE, "github-actions[bot]")])
    v2 = dict(base, comments=[_comment(
        "⚠️ Stale-claim review needed: contenu different.\n"
        "<!-- Sticky Pull Request Commentstale-claim-advisory -->",
        "github-actions[bot]")])
    assert mod.surfaces_fingerprint(v1) == mod.surfaces_fingerprint(v2)
    assert mod.surfaces_fingerprint(base) != mod.surfaces_fingerprint(v1)


def test_sticky_forms_require_the_bot_author_and_a_listed_header():
    """#18637 (negative controls) : un tiers qui recopie la forme perime le
    dossier ; un en-tete sticky non liste (non consultatif) aussi ; un marqueur
    sticky qui n'est pas en fin de corps aussi."""
    cases = (
        (_STICKY_STALE, "clusterManager-Myia"),
        ("## Golden-Set Execution (H.7 P3)\ncopie", "myia-po-2023"),
        ("## Notebook outputs-required (H.4 schema): **PASS** copie", "myia-po-2023"),
        ("rapport\n<!-- Sticky Pull Request Commentsome-blocking-guard -->", "github-actions[bot]"),
        ("<!-- Sticky Pull Request Commentstale-claim-advisory -->\nsuite ajoutee", "github-actions[bot]"),
    )
    for body, login in cases:
        base = _stamped_snapshot("")
        base["comments"].pop()
        snapshot = _stamped_snapshot(_dossier_for(base))
        row = _comment(body, login=login)
        row["createdAt"] = T1
        snapshot["comments"].append(row)
        errors = _errors(snapshot)
        assert any("discussion changed after dossier" in e for e in errors), (login, body[:40])


def test_pre18637_stamp_stays_verifiable():
    """#18637 transition : un dossier tamponne AVANT le correctif (empreinte
    qui hache le corps entier du sticky) reste accepte tant que les surfaces
    n'ont pas bouge -- le merge du correctif ne tue pas les dossiers intacts."""
    base = _base_snapshot()
    snap = dict(base, comments=[_comment(_STICKY_STALE, "github-actions[bot]")])
    old = mod.pre18637_surfaces_fingerprint(snap)
    new = mod.surfaces_fingerprint(snap)
    assert old != new
    rewritten = dict(base, comments=[_comment(
        "⚠️ autre texte\n<!-- Sticky Pull Request Commentstale-claim-advisory -->",
        "github-actions[bot]")])
    # l'ancienne empreinte, elle, bouge avec le corps : elle ne protege que
    # l'etat exact qu'elle a tamponne.
    assert mod.pre18637_surfaces_fingerprint(rewritten) != old


# --- #18933 : un READY est le rendu d'un organe, pas une appreciation --------
# Invariant B de #17020. Incident fondateur 2026-09-20 : 5 dossiers Haiku
# READY par defaut. Trois mecanismes : (1) provenance REQUIRED sur READY,
# (2) derive_verdict = l'organe rederive le verdict des mesures vivantes,
# (3) render_emitted_dossier = l'emetteur rend un dossier dont le verdict et
# la provenance viennent de l'organe. Un dossier BLOCKED n'a pas de
# provenance a porter : les champs restent OPTIONNELS hors READY.


def _no_provenance() -> dict:
    return {"organ": "", "organ-command": "", "organ-rc": ""}


def _fill_reading_acts(block: str) -> str:
    """Le geste de la lane emettrice : remplir les actes de lecture du --emit."""
    fill = {
        "complete: REPLACE_WITH_true": "complete: true",
        "body: REPLACE_WITH_read": "body: read",
        "checks: REPLACE_WITH_latest-wins-green_OR_BLOCKED": "checks: latest-wins-green",
        "b0: REPLACE_WITH_clear_OR_blocked": "b0: clear",
        "scope: REPLACE_WITH_pass_OR_fail": "scope: pass",
        "domain: REPLACE_WITH_pass_OR_not-applicable_OR_fail": "domain: pass",
    }
    for old, new in fill.items():
        assert old in block, old
        block = block.replace(old, new, 1)
    assert "REPLACE_WITH" not in block
    return block


def test_ready_without_provenance_is_refused():
    """Un READY sans organ/organ-command/organ-rc = une appreciation."""
    snapshot = _snapshot(_body(**_no_provenance()))
    verdict, errors = mod.evaluate(snapshot)
    assert verdict != mod.VERDICT_READY
    assert any("organ is required when verdict is READY" in e for e in errors)
    assert any("organ-command is required when verdict is READY" in e for e in errors)
    assert any("organ-rc is required when verdict is READY" in e for e in errors)


def test_ready_with_wrong_organ_name_is_refused():
    snapshot = _snapshot(_body(organ="haiku_opinion.py"))
    verdict, errors = mod.evaluate(snapshot)
    assert verdict != mod.VERDICT_READY
    assert any("organ must be 'check_adjoint_prevalidation.py'" in e for e in errors)


def test_ready_with_wrong_organ_command_is_refused():
    snapshot = _snapshot(
        _body(**{"organ-command": "python scripts/check_adjoint_prevalidation.py 123"})
    )
    verdict, errors = mod.evaluate(snapshot)
    assert verdict != mod.VERDICT_READY
    assert any(
        "organ-command must invoke 'check_adjoint_prevalidation.py"
        " --derive-verdict 123'" in e
        for e in errors
    )


def test_ready_with_wrong_pr_in_command_is_refused():
    snapshot = _snapshot(
        _body(**{"organ-command": (
            "python scripts/check_adjoint_prevalidation.py --derive-verdict 999"
        )})
    )
    verdict, errors = mod.evaluate(snapshot)
    assert verdict != mod.VERDICT_READY
    assert any("--derive-verdict 123" in e for e in errors)


def test_ready_with_nonzero_organ_rc_is_refused():
    snapshot = _snapshot(_body(**{"organ-rc": "3"}))
    verdict, errors = mod.evaluate(snapshot)
    assert verdict != mod.VERDICT_READY
    assert any("organ-rc must be '0'" in e for e in errors)


def test_blocked_dossier_needs_no_provenance():
    """BLOCKED ne coute rien a prouver : les champs restent optionnels."""
    changes = {"verdict": "BLOCKED", "b0": "blocked"}
    changes.update(_no_provenance())
    snapshot = _snapshot(_body(**changes))
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_BLOCKED
    assert not any("organ" in e for e in errors)


def test_derive_verdict_ready_when_all_green():
    verdict, reasons = mod.derive_verdict(
        _base_snapshot(), lambda pr: {"blocked": False, "blocking": []}
    )
    assert verdict == mod.VERDICT_READY and reasons == []


def test_derive_verdict_names_each_blocking_measurement():
    """Chaque mesure bloquante est nommee : check rouge, draft, thread, B.0."""
    snapshot = _base_snapshot()
    snapshot["checkRuns"][0]["conclusion"] = "failure"
    snapshot["isDraft"] = True
    snapshot["threads"].append({"isResolved": False})
    probe = lambda pr: {  # noqa: E731
        "blocked": True,
        "blocking": [{"kind": "nit", "author": "u", "src": "c"}],
    }
    verdict, reasons = mod.derive_verdict(snapshot, probe)
    assert verdict == mod.VERDICT_BLOCKED
    assert any("PR gate" in r or "latest-wins" in r for r in reasons), reasons
    assert any("draft" in r for r in reasons)
    assert any("unresolved review thread" in r for r in reasons)
    assert any("unlifted remark" in r for r in reasons)


def test_derive_verdict_blocked_when_merged():
    """#18984 -- une PR MERGED ne peut pas etre READY (constat adjoint 04/10).

    validate_dossier exigeait deja state OPEN ; la derivation l'omettait :
    sur un snapshot MERGED aux checks verts, derive_verdict rendait READY.
    """
    snapshot = _base_snapshot()
    snapshot["state"] = "MERGED"
    verdict, reasons = mod.derive_verdict(
        snapshot, lambda pr: {"blocked": False, "blocking": []}
    )
    assert verdict == mod.VERDICT_BLOCKED
    assert any("state must be OPEN" in r for r in reasons), reasons


def test_derive_verdict_blocked_when_empty_diff():
    """#18984 -- un diff vide n'a rien a squasher, READY impossible."""
    snapshot = _base_snapshot()
    snapshot["changedFiles"] = 0
    verdict, reasons = mod.derive_verdict(
        snapshot, lambda pr: {"blocked": False, "blocking": []}
    )
    assert verdict == mod.VERDICT_BLOCKED
    assert any("non-empty diff" in r for r in reasons), reasons


def test_derive_verdict_probes_b0_by_default(monkeypatch):
    probe, calls = _organ(False)
    monkeypatch.setattr(mod, "probe_b0", probe)
    mod.derive_verdict(_base_snapshot())
    assert calls == [123]


def test_refute_ready_verdict_demotes_when_organ_no_longer_derives():
    """Dossier READY, mais la tete a tourne : check rouge au snapshot."""
    snapshot = _snapshot(_body())
    snapshot["checkRuns"][0]["conclusion"] = "failure"
    verdict, dossier = _ready_dossier()
    verdict, errors, dossier = mod.refute_ready_verdict(
        snapshot, verdict, [], dossier,
        lambda pr: {"blocked": False, "blocking": []},
    )
    assert verdict == "" and dossier is None
    assert len(errors) == 1
    assert "no longer derived by the organ" in errors[0]
    assert "check_adjoint_prevalidation.py --derive-verdict" in errors[0]


def test_refute_ready_verdict_keeps_ready_when_derived():
    verdict, dossier = _ready_dossier()
    out = mod.refute_ready_verdict(
        _base_snapshot(), verdict, [], dossier,
        lambda pr: {"blocked": False, "blocking": []},
    )
    assert out == (mod.VERDICT_READY, [], dossier)


def test_refute_ready_verdict_preserves_b0_errors_and_skips_probe():
    """Regression #18933 : les erreurs du refute b0 ne sont plus ecrasees,
    et le probe n'est pas paye quand le verdict n'est plus READY."""
    probe, calls = _organ(True, [{"kind": "nit", "author": "u", "src": "c"}])
    verdict, errors, dossier = mod.refute_ready_verdict(
        _base_snapshot(), "", ["b0 claim 'clear' is contradicted by ..."], None, probe
    )
    assert verdict == "" and dossier is None
    assert errors == ["b0 claim 'clear' is contradicted by ..."]
    assert calls == []


def test_refute_ready_verdict_appends_its_error_after_b0_errors():
    """b0 leve ET la tete a tourne : les deux raisons survivent ensemble."""
    snapshot = _base_snapshot()
    snapshot["checkRuns"][0]["conclusion"] = "failure"
    b0_errors = ["b0 claim 'clear' is contradicted by ..."]
    ready_verdict, ready_dossier = _ready_dossier()
    verdict, errors, dossier = mod.refute_ready_verdict(
        snapshot, ready_verdict, b0_errors, ready_dossier,
        lambda pr: {"blocked": False, "blocking": []},
    )
    assert verdict == "" and dossier is None
    assert errors[0] == b0_errors[0]
    assert "no longer derived by the organ" in errors[1]


def test_render_emitted_dossier_ready_round_trips_through_the_gate():
    """L'emission verifiable : le dossier rendu par --emit, ses actes de
    lecture remplis, PASSE le gate (provenance comprise)."""
    snapshot = _snapshot()  # pre-dossier : c'est l'emetteur qui part du template
    probe = lambda pr: {"blocked": False, "blocking": []}  # noqa: E731
    block, verdict, reasons = mod.render_emitted_dossier(snapshot, probe=probe)
    assert verdict == mod.VERDICT_READY and reasons == []
    assert "verdict: READY" in block
    assert block.count("organ:") == 1  # in-place, pas de cle dupliquee
    assert "organ: check_adjoint_prevalidation.py" in block
    assert (
        "organ-command: python scripts/check_adjoint_prevalidation.py"
        " --derive-verdict 123" in block
    )
    assert "organ-rc: 0" in block
    # round-trip : la lane remplit les actes de lecture, poste, le gate valide.
    carrying = _snapshot(_body())
    carrying["comments"][-1]["body"] = _fill_reading_acts(block)
    verdict, errors = mod.evaluate(carrying)
    assert verdict == mod.VERDICT_READY, errors


def test_render_emitted_dossier_blocked_carries_rc3():
    snapshot = _base_snapshot()
    snapshot["checkRuns"][0]["conclusion"] = "failure"
    probe = lambda pr: {"blocked": False, "blocking": []}  # noqa: E731
    block, verdict, reasons = mod.render_emitted_dossier(snapshot, probe=probe)
    assert verdict == mod.VERDICT_BLOCKED
    assert any("PR gate" in r or "latest-wins" in r for r in reasons)
    assert "verdict: BLOCKED" in block
    assert "organ-rc: 3" in block
    assert block.count("organ:") == 1


def test_main_derive_verdict_mode_is_organ_only(monkeypatch, capsys):
    """--derive-verdict : l'organe imprime le verdict, rc 0/3, pas de gate."""
    snapshot = _base_snapshot()
    monkeypatch.setattr(mod, "load_snapshot", lambda pr: snapshot)
    monkeypatch.setattr(mod.gh_identity, "pin_gh_token", lambda: None)
    monkeypatch.setattr(mod, "probe_b0", lambda pr: {"blocked": False, "blocking": []})
    monkeypatch.setattr(
        sys, "argv", ["check_adjoint_prevalidation.py", "--derive-verdict", "123"]
    )
    assert mod.main() == mod.EXIT_READY
    assert capsys.readouterr().out.strip() == "READY"


def test_main_derive_verdict_mode_blocked_rc3(monkeypatch, capsys):
    snapshot = _base_snapshot()
    snapshot["checkRuns"][0]["conclusion"] = "failure"
    monkeypatch.setattr(mod, "load_snapshot", lambda pr: snapshot)
    monkeypatch.setattr(mod.gh_identity, "pin_gh_token", lambda: None)
    monkeypatch.setattr(mod, "probe_b0", lambda pr: {"blocked": False, "blocking": []})
    monkeypatch.setattr(
        sys, "argv", ["check_adjoint_prevalidation.py", "--derive-verdict", "123"]
    )
    assert mod.main() == mod.EXIT_BLOCKED_WITH_SUBSTANCE
    assert capsys.readouterr().out.strip() == "BLOCKED"


def test_main_emit_mode_prints_a_dossier_that_passes(monkeypatch, capsys):
    snapshot = _snapshot()
    monkeypatch.setattr(mod, "load_snapshot", lambda pr: snapshot)
    monkeypatch.setattr(mod.gh_identity, "pin_gh_token", lambda: None)
    monkeypatch.setattr(mod, "probe_b0", lambda pr: {"blocked": False, "blocking": []})
    monkeypatch.setattr(
        sys, "argv", ["check_adjoint_prevalidation.py", "--emit", "123"]
    )
    assert mod.main() == mod.EXIT_READY
    block = capsys.readouterr().out
    assert "verdict: READY" in block and "organ-rc: 0" in block
    carrying = _snapshot(_body())
    carrying["comments"][-1]["body"] = _fill_reading_acts(block)
    assert mod.evaluate(carrying)[0] == mod.VERDICT_READY


# --- #18934 : un READY qui recouvre un BLOCKED le refute par son nom ---------
# Invariant C de #17020. Incident fondateur 2026-09-20 : le masquage d'un
# dossier valide par un dossier posterieur moins rigoureux etait intra-login
# -- le defaut vit dans la RELATION entre dossiers successifs, pas dans
# l'identite de l'emetteur. A tete constante, un READY doit citer l'ancien
# BLOCKED (supersedes) et nommer ce qu'il refute (supersedes-why).


OTHER_HEAD = "f" * 40


def _stacked_dossiers(first: dict, second: dict) -> dict:
    """Snapshot a deux dossiers sur la MEME tete : BLOCKED (index 1) puis
    second (index 2). Chaque dossier temoigne des commentaires qui le
    precedent (comments-reviewed == comment_index, surfaces-sha256 sur le
    prefixe) -- sinon l'evaluation echouerait pour la mauvaise raison.
    """
    snapshot = _base_snapshot()
    first_fields = {"verdict": "BLOCKED", "b0": "blocked", "comments-reviewed": "1"}
    first_fields.update(first)
    first_fields["surfaces-sha256"] = mod.surfaces_fingerprint(snapshot, 1)
    snapshot["comments"].append(_comment(_body(**first_fields)))

    second_fields = {"comments-reviewed": "2"}
    second_fields.update(second)
    second_fields["surfaces-sha256"] = mod.surfaces_fingerprint(snapshot, 2)
    snapshot["comments"].append(_comment(_body(**second_fields)))
    return snapshot


def test_mute_contradiction_is_refused_and_names_the_covered_dossier():
    """READY muet sur BLOCKED meme tete : refus rc 1, l'ancien est nomme."""
    snapshot = _stacked_dossiers({}, {})
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == ""
    assert len(errors) == 1
    error = errors[0]
    assert "mute contradiction (#18934)" in error
    assert "comment 2 of 3" in error  # l'ancien BLOCKED, pas le READY
    assert "supersedes: 2" in error


def test_ready_with_supersedes_and_why_stands():
    """La refutation nommee debloque : citation exacte + raison non vide."""
    snapshot = _stacked_dossiers(
        {},
        {"supersedes": "2", "supersedes-why": "B.0 levered: nit lifted in c3"},
    )
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_supersedes_citing_the_wrong_comment_is_refused():
    snapshot = _stacked_dossiers({}, {"supersedes": "1", "supersedes-why": "x"})
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == ""
    assert any("supersedes: 2" in e for e in errors)


def test_supersedes_without_why_is_refused():
    snapshot = _stacked_dossiers({}, {"supersedes": "2", "supersedes-why": "  "})
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == ""
    assert any("supersedes-why is empty" in e for e in errors)


def test_changed_head_means_nothing_to_refute():
    """A tete changee l'ancien est deja perime par exact-head : pas de
    contradiction, le READY n'a rien a citer."""
    snapshot = _stacked_dossiers({"head": OTHER_HEAD}, {})
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_blocked_over_ready_needs_no_refutation():
    """La direction conservatrice serre, elle ne debloque pas : rien a exiger."""
    snapshot = _stacked_dossiers(
        {"verdict": "READY", "b0": "clear"},
        {"verdict": "BLOCKED", "b0": "blocked"},
    )
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_BLOCKED
    assert errors == []


def test_stray_supersedes_on_a_lone_ready_is_tolerated():
    """Champs optionnels hors contradiction : un dossier sans aine sur la
    meme tete ne peut pas etre refuse pour les porter."""
    snapshot = _snapshot(_body(supersedes="7", **{"supersedes-why": "nostalgia"}))
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_main_refuses_mute_contradiction_with_rc1(monkeypatch, capsys):
    snapshot = _stacked_dossiers({}, {})
    monkeypatch.setattr(mod, "load_snapshot", lambda pr: snapshot)
    monkeypatch.setattr(mod.gh_identity, "pin_gh_token", lambda: None)
    monkeypatch.setattr(mod, "probe_b0", lambda pr: {"blocked": False, "blocking": []})
    monkeypatch.setattr(sys, "argv", ["check_adjoint_prevalidation.py", "123"])
    assert mod.main() == mod.EXIT_NO_DOSSIER
    out = capsys.readouterr().out
    assert "NO-DOSSIER" in out and "mute contradiction (#18934)" in out
# --- #19002 : la base doit etre `main` pour READY -------------------------
# Mesure du 2026-10-03 : 4 PRs a base != main dans le pool ouvert, dont
# #18819 (base squash-mergee) et #18993 (base fermee sans merge). Avant
# #19002, le gate rendait rc=0 READY sur ces PRs, et merge_ready fusionnait
# dans la branche morte. La regle : un dossier READY exige une base
# `main` ; sinon, refus. Trois tests : un temoin positif (base main, le
# chemin nominal inchange), un temoin negatif sur une base de feature
# encore ouverte (#18985/#18967), un temoin negatif sur une base dont la
# PR porteuse est fermee ou mergee (#18819/#18993).


def test_base_main_does_not_change_a_ready_dossier():
    """Temooin positif : une PR a base main, dossier READY canonique,
    verdict READY inchange. Le chemin nominal n'est pas casse par #19002."""
    snapshot = _snapshot(_body())
    assert snapshot["baseRefName"] == "main"
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    assert verdict == mod.VERDICT_READY, errors
    assert not errors


def test_base_feature_open_refuses_ready_and_names_the_base():
    """Temooin negatif : PR empilee sur une branche de feature encore
    ouverte (#18985 / #18967). Le gate refuse READY et nomme la base
    pour que la lane sache ou retargeter."""
    snapshot = _snapshot(_body())
    snapshot["baseRefName"] = "docs/qc-book-inventory-reconciliation"
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    assert verdict == "", verdict
    assert dossier is None, dossier
    assert any("baseRefName must be 'main'" in e for e in errors), errors
    # Le message nomme la base fautive -- la lane en a besoin pour le
    # retarget, et la regle sans le nom forcerait a rouvrir le PR.
    assert any(
        "docs/qc-book-inventory-reconciliation" in e for e in errors
    ), errors


def test_base_dead_refuses_ready_and_names_the_base():
    """Temooin negatif : PR empilee sur une branche dont la PR porteuse
    est fermee ou squash-mergee (#18819 / #18993). Meme verdict que la
    base de feature, avec un nom different -- le gate refuse dans les
    deux cas parce que son contrat ne sait pas dire 'cette base est
    morte' (et n'a pas besoin de le dire : retarget sur main)."""
    snapshot = _snapshot(_body())
    snapshot["baseRefName"] = "renum/17063-complexity-05b"  # #18819
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    assert verdict == "", verdict
    assert dossier is None, dossier
    assert any("baseRefName must be 'main'" in e for e in errors), errors
    assert any("renum/17063-complexity-05b" in e for e in errors), errors


# #19869 -- `--emit` doit pre-renseigner `supersedes` / `supersedes-why`
# quand un dossier BLOCKED anterieur existe a la meme tete, sinon le
# gate (`mute_contradictions` l.1307) refuse le dossier pose avec
# NO-DOSSIER. Les tests suivants couvrent la detection
# (`find_previous_blocked_same_head`) et l'injection dans
# `render_emitted_dossier`.


def test_find_previous_blocked_same_head_returns_blocked_at_same_head():
    """BLOCKED anterieur a la meme tete : renvoie sa position 1-based."""
    snapshot = _stacked_dossiers({}, {})
    found = mod.find_previous_blocked_same_head(snapshot, HEAD)
    assert found is not None
    position, dossier = found
    # Premier dossier (index 1, l'ordinary earlier) + le BLOCKED (index 2).
    # Le READY futur (index 3 si pose) aurait position 3 ; mais on cherche
    # un BLOCKED anterieur = le 2e commentaire pose = position 2.
    assert position == 2
    assert dossier.fields.get("verdict") == mod.VERDICT_BLOCKED


def test_find_previous_blocked_same_head_returns_none_on_changed_head():
    """Tete differente : rien a refuter, retour None (exact-head peremption)."""
    snapshot = _stacked_dossiers({"head": OTHER_HEAD}, {})
    found = mod.find_previous_blocked_same_head(snapshot, HEAD)
    assert found is None


def test_find_previous_blocked_same_head_picks_most_recent_blocked():
    """Quand plusieurs BLOCKED sur la meme tete : le plus recent gagne
    (celui qu'il faut refuter, pas un anterieur deja recouvert)."""
    snapshot = _base_snapshot()
    # Premier BLOCKED (index 1)
    first = {"verdict": "BLOCKED", "b0": "blocked", "comments-reviewed": "1"}
    first["surfaces-sha256"] = mod.surfaces_fingerprint(snapshot, 1)
    snapshot["comments"].append(_comment(_body(**first)))
    # Deuxieme BLOCKED a la meme tete (index 2)
    second = {
        "verdict": "BLOCKED",
        "b0": "blocked",
        "comments-reviewed": "2",
        "head": HEAD,
    }
    second["surfaces-sha256"] = mod.surfaces_fingerprint(snapshot, 2)
    snapshot["comments"].append(_comment(_body(**second)))
    found = mod.find_previous_blocked_same_head(snapshot, HEAD)
    assert found is not None
    position, _dossier = found
    assert position == 3  # 1 (ordinary) + 2 BLOCKED = 3 commentaires, le dernier est position 3


def test_find_previous_blocked_same_head_ignores_ready_predecessors():
    """Un READY anterieur n'est pas un BLOCKED a recouvrir : None."""
    snapshot = _stacked_dossiers(
        {"verdict": "READY", "b0": "clear"},
        {"verdict": "BLOCKED", "b0": "blocked"},
    )
    found = mod.find_previous_blocked_same_head(snapshot, HEAD)
    assert found is not None
    position, dossier = found
    # Le seul BLOCKED est le 3e (l'ordinary=1, le READY=2, le BLOCKED=3).
    assert position == 3
    assert dossier.fields.get("verdict") == mod.VERDICT_BLOCKED


def test_emitter_and_gate_name_the_same_covered_dossier():
    """#19869 -- l'emetteur et le gate designent le MEME dossier couvert.

    C'est le controle causal du defaut : deux recherches independantes
    derivent, et l'emetteur pre-remplit alors un `supersedes` que le gate
    refuse. Ici la position rendue par `find_previous_blocked_same_head`
    (ce que `--emit` ecrit) et celle que le gate cite dans son refus
    doivent coincider -- sur la meme pile de dossiers.
    """
    snapshot = _two_blocked_then_ready()
    found = mod.find_previous_blocked_same_head(snapshot, HEAD)
    assert found is not None
    emitted_position, _dossier = found
    # Deux BLOCKED sur la meme tete : l'ordre compte (le plus recent gagne).
    # Sans cette discrimination, une recherche divergente passerait inapercue.
    assert emitted_position == 3

    _verdict, errors = mod.evaluate(snapshot)
    assert len(errors) == 1
    # Le gate nomme le dossier couvert en prose : "comment <pos> of <N>".
    assert f"comment {emitted_position} of" in errors[0]
    assert f"'supersedes: {emitted_position}'" in errors[0]


def _two_blocked_then_ready() -> dict:
    """Pile : ordinary (1), BLOCKED (2), BLOCKED (3), READY muet (4).

    Deux BLOCKED a la meme tete font que l'ORDRE discrimine : le dossier
    couvert est le plus recent (position 3), pas le premier. Un READY final
    est ce qui declenche le refus du gate -- un BLOCKED apres un BLOCKED
    n'exige rien (direction conservatrice de #18934).
    """
    snapshot = _base_snapshot()
    for index in (1, 2):
        fields = {
            "verdict": "BLOCKED",
            "b0": "blocked",
            "comments-reviewed": str(index),
            "head": HEAD,
        }
        fields["surfaces-sha256"] = mod.surfaces_fingerprint(snapshot, index)
        snapshot["comments"].append(_comment(_body(**fields)))
    ready = {"comments-reviewed": "3"}
    ready["surfaces-sha256"] = mod.surfaces_fingerprint(snapshot, 3)
    snapshot["comments"].append(_comment(_body(**ready)))
    return snapshot


def test_covered_blocked_dossier_is_the_shared_core():
    """Le cœur unique est appele par les DEUX chemins (#19869).

    Une recherche en dur reintroduite d'un cote seul ferait diverger les
    organes sans qu'aucun test ne rougisse : ce controle verifie que
    `mute_contradictions` ET `find_previous_blocked_same_head` passent bien
    par `covered_blocked_dossier`.
    """
    snapshot = _two_blocked_then_ready()
    dossiers = []
    for index, comment in enumerate(snapshot["comments"]):
        dossier, _errors = mod.parse_dossier(
            comment.get("body") or "",
            index,
            comment.get("author", {}).get("login") or "jsboige",
            comment.get("createdAt") or "",
        )
        if dossier is not None:
            dossiers.append(dossier)
    expected = mod.covered_blocked_dossier(dossiers, HEAD)
    assert expected is not None
    assert expected.fields.get("verdict") == mod.VERDICT_BLOCKED

    found = mod.find_previous_blocked_same_head(snapshot, HEAD)
    assert found == (expected.comment_index + 1, expected)


def test_render_emitted_dossier_autofills_supersedes_for_ready(monkeypatch):
    """Un READY au-dessus d'un BLOCKED a meme tete : supersedes+why poses
    automatiquement, dans le bloc, avant END, par --emit."""
    monkeypatch.setattr(
        mod, "probe_b0", lambda pr: {"blocked": False, "blocking": []}
    )
    snapshot = _stacked_dossiers({}, {})
    block, verdict, _reasons = mod.render_emitted_dossier(snapshot, mod.ADJOINT_LANE)
    assert verdict == mod.VERDICT_READY
    assert "supersedes: 2" in block
    assert "supersedes-why: auto" in block
    # Positionnement : supersedes-* avant END, dans le bloc.
    lines = block.split("\n")
    end_index = next(i for i, line in enumerate(lines) if line.strip() == mod.END)
    supersedes_index = next(
        i for i, line in enumerate(lines) if line.startswith("supersedes:")
    )
    supersedes_why_index = next(
        i for i, line in enumerate(lines) if line.startswith("supersedes-why:")
    )
    assert supersedes_index < end_index
    assert supersedes_why_index < end_index
    assert supersedes_index < supersedes_why_index


def test_render_emitted_dossier_omits_supersedes_when_no_blocked(monkeypatch):
    """Pas de BLOCKED anterieur a meme tete : pas de supersedes, sortie
    identique au template + provenance."""
    monkeypatch.setattr(
        mod, "probe_b0", lambda pr: {"blocked": False, "blocking": []}
    )
    snapshot = _snapshot(_body())
    block, verdict, _reasons = mod.render_emitted_dossier(snapshot, mod.ADJOINT_LANE)
    assert verdict == mod.VERDICT_READY
    assert "supersedes" not in block


def test_render_emitted_dossier_omits_supersedes_for_blocked_verdict(monkeypatch):
    """Verdict derive BLOCKED : la direction conservatrice serre, elle ne
    debloque pas. Pas de supersedes meme si un BLOCKED anterieur existe."""
    monkeypatch.setattr(
        mod, "probe_b0", lambda pr: {"blocked": False, "blocking": []}
    )
    # Construire un snapshot ou le verdict derive sera BLOCKED : un draft.
    snapshot = _base_snapshot()
    snapshot["isDraft"] = True
    # Ajouter un BLOCKED anterieur a la meme tete.
    blocked = {"verdict": "BLOCKED", "b0": "blocked", "comments-reviewed": "1"}
    blocked["surfaces-sha256"] = mod.surfaces_fingerprint(snapshot, 1)
    snapshot["comments"].append(_comment(_body(**blocked)))
    block, verdict, _reasons = mod.render_emitted_dossier(snapshot, mod.ADJOINT_LANE)
    assert verdict == mod.VERDICT_BLOCKED
    assert "supersedes" not in block


def test_render_emitted_dossier_omits_supersedes_on_changed_head(monkeypatch):
    """BLOCKED anterieur sur une AUTRE tete : perime par exact-head, rien
    a refuter, pas de supersedes dans le rendu."""
    monkeypatch.setattr(
        mod, "probe_b0", lambda pr: {"blocked": False, "blocking": []}
    )
    snapshot = _stacked_dossiers({"head": OTHER_HEAD}, {})
    block, verdict, _reasons = mod.render_emitted_dossier(snapshot, mod.ADJOINT_LANE)
    assert verdict == mod.VERDICT_READY
    assert "supersedes" not in block


def test_render_emitted_dossier_blocked_at_same_head_then_changed_head(monkeypatch):
    """BLOCKED sur tete-1, puis tete changee : le nouveau READY n'a rien
    a refuter (tete-1 BLOCKED est deja perime par exact-head)."""
    monkeypatch.setattr(
        mod, "probe_b0", lambda pr: {"blocked": False, "blocking": []}
    )
    snapshot = _base_snapshot()
    # Premier dossier BLOCKED a tete-1 (index 1)
    blocked = {
        "verdict": "BLOCKED",
        "b0": "blocked",
        "comments-reviewed": "1",
        "head": OTHER_HEAD,
    }
    blocked["surfaces-sha256"] = mod.surfaces_fingerprint(snapshot, 1)
    snapshot["comments"].append(_comment(_body(**blocked)))
    # Snapshot a tete-2 (HEAD)
    block, verdict, _reasons = mod.render_emitted_dossier(snapshot, mod.ADJOINT_LANE)
    assert verdict == mod.VERDICT_READY
    assert "supersedes" not in block




# ===========================================================================
# #16480 -- queue derivation (--queue) and exact-head consumption (--consume)
# ===========================================================================

QUEUE_NOW = mod.datetime(2026, 10, 8, 20, 0, tzinfo=mod.timezone.utc)
OTHER_HEAD = "e" * 40


def _clear_probe(pr):
    return {"blocked": False, "blocking": []}


def _blocked_probe(pr):
    return {"blocked": True, "blocking": [
        {"kind": "review", "author": "hermes", "src": "pr"}]}


def _classified(snapshot=None, **kwargs):
    kwargs.setdefault("now", QUEUE_NOW)
    kwargs.setdefault("probe", _clear_probe)
    if snapshot is None:
        snapshot = _reviewed_snapshot()
    return mod.classify_snapshot(snapshot, **kwargs)


def _review(login="myia-ai-01", state="APPROVED", oid=HEAD,
            submitted="2026-10-08T10:00:00Z"):
    return {
        "state": state,
        "submittedAt": submitted,
        "commit": {"oid": oid},
        "author": {"login": login},
    }


def _queue_snapshot(reviews, base=None, number=123, **dossier_changes):
    """Snapshot avec les reviews posees AVANT l'empreinte du dossier.

    L'empreinte hache les lignes de review (auteur, submittedAt) et le numero
    de PR : poser les reviews apres coup ou changer le numero casserait
    surfaces-sha256 et masquerait le check sous test. Le dossier atteste le
    compte exact des reviews posees.
    """
    snapshot = dict(base) if base is not None else _base_snapshot()
    snapshot["number"] = number
    snapshot["reviews"] = reviews
    fields = {"pr": str(number), "reviews-reviewed": str(len(reviews))}
    fields.update(dossier_changes)
    fields["surfaces-sha256"] = mod.surfaces_fingerprint(snapshot)
    snapshot["comments"] = [*snapshot["comments"], _comment(_body(**fields))]
    return snapshot


def _reviewed_snapshot(**dossier_changes):
    """Nominal READY fixture: dossier + qualifying review on the exact head."""
    return _queue_snapshot([_review()], **dossier_changes)


def _dwell_run(lift="2026-10-08T21:00:00Z", remaining=60):
    title = (
        "tete du 2026-10-08T18:00:00Z -- plancher 120 min, "
        f"reste {remaining} min ; ecoule a {lift}"
    )
    return {
        "id": 7,
        "name": "PR gate",
        "status": "completed",
        "conclusion": "failure",
        "started_at": "2026-10-08T18:01:00Z",
        "output": {"title": title},
    }


# --- no dossier / stale -----------------------------------------------------


def test_queue_no_dossier_is_blocked_with_cause():
    entry = _classified(_snapshot())
    assert entry.verdict == mod.VERDICT_BLOCKED
    assert "no dossier" in entry.reject_cause
    assert entry.dossier_created_at == ""
    assert entry.grain_tag is not None and entry.grain_tag["lane"] == CARRIER


def test_queue_stale_head_is_stale():
    entry = _classified(_snapshot(_body(head=OTHER_HEAD)))
    assert entry.verdict == mod.QUEUE_VERDICT_STALE
    assert "head is stale" in entry.reject_cause


def test_queue_comment_after_dossier_is_stale():
    snapshot = _reviewed_snapshot()
    snapshot["comments"].append(_comment("late concern"))
    entry = _classified(snapshot)
    assert entry.verdict == mod.QUEUE_VERDICT_STALE


def test_queue_dossier_older_than_stale_after_is_stale():
    snapshot = _queue_snapshot([_review(submitted="2026-10-05T10:00:00Z")])
    # Le dossier porte son createdAt : plus vieux que le defaut 24 h.
    snapshot["comments"][-1] = {
        "author": {"login": "jsboige"},
        "body": snapshot["comments"][-1]["body"],
        "createdAt": "2026-10-06T10:00:00Z",
    }
    entry = _classified(snapshot)
    assert entry.verdict == mod.QUEUE_VERDICT_STALE
    assert "min old" in entry.reject_cause
    assert entry.dossier_age_minutes == 3480


def test_queue_dossier_age_below_threshold_is_not_stale():
    snapshot = _queue_snapshot([_review(submitted="2026-10-05T10:00:00Z")])
    snapshot["comments"][-1] = {
        "author": {"login": "jsboige"},
        "body": snapshot["comments"][-1]["body"],
        "createdAt": "2026-10-08T19:00:00Z",
    }
    entry = _classified(snapshot)
    assert entry.verdict == mod.VERDICT_READY
    assert entry.dossier_age_minutes == 60


# --- READY and the review door ----------------------------------------------


def test_queue_ready_nominal():
    entry = _classified()
    assert entry.verdict == mod.VERDICT_READY
    assert entry.review_qualifying is True
    assert entry.review_disposition == "approved-exact-head"
    assert entry.checks == "latest-wins-green"
    assert entry.domain == "pass"
    assert entry.last_comment_is_dossier is True
    assert entry.tail_to_read == 0
    assert entry.reject_cause == ""
    assert entry.dwell_until == ""


def test_queue_unreviewed_is_review_ready():
    snapshot = _queue_snapshot([_review(state="COMMENTED")])
    entry = _classified(snapshot)
    assert entry.verdict == mod.QUEUE_VERDICT_REVIEW_READY
    assert entry.review_disposition == "reviewed-without-disposition"
    assert entry.review_qualifying is False


def test_queue_approval_not_on_head_is_review_ready():
    snapshot = _queue_snapshot([_review(oid=OTHER_HEAD)])
    entry = _classified(snapshot)
    assert entry.verdict == mod.QUEUE_VERDICT_REVIEW_READY
    assert entry.review_disposition == "approval-not-on-head"


def test_queue_non_coordinator_approval_does_not_qualify():
    snapshot = _queue_snapshot([_review(login="some-worker")])
    entry = _classified(snapshot)
    assert entry.verdict == mod.QUEUE_VERDICT_REVIEW_READY
    assert entry.review_disposition == "approved-exact-head"
    assert entry.review_qualifying is False


def test_queue_recent_changes_requested_blocks_dispatch():
    """Divergence assumee du design #16483 : un CHANGES_REQUESTED recent n'est
    pas une review manquante, c'est une reserve a lever -- le piege « reserve
    en prose libre » (#14658) qu'aucun marqueur B.0 ne couvre."""
    snapshot = _queue_snapshot([
        _review(submitted="2026-10-08T10:00:00Z"),
        _review(state="CHANGES_REQUESTED", submitted="2026-10-08T12:00:00Z"),
    ])
    entry = _classified(snapshot)
    assert entry.verdict == mod.VERDICT_BLOCKED
    assert "CHANGES_REQUESTED" in entry.reject_cause


# --- DWELL ------------------------------------------------------------------


def test_queue_dwell_pending_red_is_dwell_pending():
    snapshot = _reviewed_snapshot()
    snapshot["checkRuns"] = [_dwell_run(lift="2026-10-08T21:00:00Z")]
    entry = _classified(snapshot)
    assert entry.verdict == mod.QUEUE_VERDICT_DWELL_PENDING
    assert entry.dwell_until == "2026-10-08T21:00:00Z"


def test_queue_dwell_elapsed_is_blocked_with_replay_hint():
    snapshot = _reviewed_snapshot()
    snapshot["checkRuns"] = [_dwell_run(lift="2026-10-08T19:00:00Z", remaining=0)]
    entry = _classified(snapshot)
    assert entry.verdict == mod.VERDICT_BLOCKED
    assert "replay the leg" in entry.reject_cause


def test_queue_dwell_plus_other_red_is_blocked():
    snapshot = _reviewed_snapshot()
    snapshot["checkRuns"] = [
        _dwell_run(),
        {
            "id": 8,
            "name": "fast-lane",
            "status": "completed",
            "conclusion": "failure",
            "started_at": "2026-10-08T18:02:00Z",
            "output": {"title": "fast-lane -- red"},
        },
    ]
    entry = _classified(snapshot)
    assert entry.verdict == mod.VERDICT_BLOCKED
    assert "no dossier worth trusting" in entry.reject_cause
    assert "fast-lane" in entry.reject_cause


# --- in-flight rollup ---------------------------------------------------------


def test_queue_rerun_inflight_over_green_blocks():
    snapshot = _reviewed_snapshot()
    snapshot["checkRuns"] = [
        snapshot["checkRuns"][0],
        {
            "id": 9,
            "name": "PR gate",
            "status": "in_progress",
            "started_at": "2026-10-08T19:59:00Z",
        },
    ]
    entry = _classified(snapshot)
    assert entry.verdict == mod.VERDICT_BLOCKED
    assert "in-flight" in entry.reject_cause
    assert entry.checks == "in-flight"


def test_queue_inflight_without_completed_blocks():
    snapshot = _reviewed_snapshot()
    snapshot["checkRuns"] = [
        {
            "id": 10,
            "name": "PR gate",
            "status": "queued",
            "started_at": "2026-10-08T19:59:30Z",
        }
    ]
    entry = _classified(snapshot)
    assert entry.verdict == mod.VERDICT_BLOCKED
    # Jambe requise sans conclusion sur la tete : l'absence est nommee.
    assert "absence of required check" in entry.reject_cause


# --- B.0 / frozen / attested BLOCKED ------------------------------------------


def test_queue_b0_refuted_blocks():
    entry = _classified(_reviewed_snapshot(), probe=_blocked_probe)
    assert entry.verdict == mod.VERDICT_BLOCKED
    assert "b0" in entry.reject_cause or "B.0" in entry.reject_cause


def test_queue_frozen_campaign_blocks(monkeypatch):
    monkeypatch.setattr(
        mod, "frozen_umbrella_exclusion",
        lambda *_a, **_k: "veto user #17040",
    )
    entry = _classified()
    assert entry.verdict == mod.VERDICT_BLOCKED
    assert "frozen" in entry.reject_cause


def test_queue_attested_blocked_stands_when_b0_still_blocks():
    entry = _classified(
        _reviewed_snapshot(verdict="BLOCKED", b0="blocked"),
        probe=_blocked_probe,
    )
    assert entry.verdict == mod.VERDICT_BLOCKED
    assert "attests BLOCKED" in entry.reject_cause


def test_queue_b0_only_blocked_expires_toward_restamp():
    entry = _classified(
        _reviewed_snapshot(verdict="BLOCKED", b0="blocked"),
        probe=_clear_probe,
    )
    assert entry.verdict == mod.VERDICT_BLOCKED
    assert "re-stamp" in entry.reject_cause or "no longer blocks" in entry.reject_cause


# --- stack child ---------------------------------------------------------------


def test_queue_stack_child_domain_not_applicable():
    """Une stack (base != main) ne peut pas porter de dossier READY : le gate
    la refuse (« retarget the PR »). La queue expose le domaine declare sans
    jamais retablir le dossier refuse -- c'est le cas not-applicable."""
    base = _base_snapshot()
    base["baseRefName"] = "feature/stack-base"
    snapshot = _queue_snapshot(
        [_review()], base=base, domain="not-applicable"
    )
    entry = _classified(snapshot)
    assert entry.verdict == mod.VERDICT_BLOCKED
    assert "baseRefName must be 'main'" in entry.reject_cause
    assert entry.domain == "not-applicable"


# --- build_queue / consume ------------------------------------------------------


def test_build_queue_unknown_pr_is_listed_not_fatal():
    def loader(pr):
        if pr == 1:
            raise RuntimeError("gh api exploded")
        return _reviewed_snapshot()

    result = mod.build_queue(
        [1, 123], now=QUEUE_NOW, probe=_clear_probe, loader=loader
    )
    assert [row["pr"] for row in result["unknown"]] == [1]
    assert [item["pr"] for item in result["queue"]] == [123]
    assert result["metrics"] == {mod.VERDICT_READY: 1}


def test_build_queue_sorts_oldest_first_not_by_number():
    older = _queue_snapshot([_review()], number=8)
    older["createdAt"] = "2026-10-01T00:00:00Z"
    newer = _queue_snapshot([_review()], number=9)
    newer["createdAt"] = "2026-10-02T00:00:00Z"
    result = mod.build_queue(
        [9, 8],
        now=QUEUE_NOW,
        probe=_clear_probe,
        loader=lambda pr: older if pr == 9 else newer,
    )
    assert [item["pr"] for item in result["queue"]] == [8, 9]


def test_build_queue_dedupes_repeated_prs():
    calls = []

    def loader(pr):
        calls.append(pr)
        return {**_reviewed_snapshot(), "number": pr}

    result = mod.build_queue(
        [5, 5], now=QUEUE_NOW, probe=_clear_probe, loader=loader
    )
    assert calls == [5]
    assert [item["pr"] for item in result["queue"]] == [5]


def test_build_queue_metrics_count_verdicts():
    stale = _reviewed_snapshot()
    stale["comments"].append(_comment("late"))
    review_ready = _queue_snapshot([])
    loader = {1: _reviewed_snapshot(), 2: review_ready, 3: stale}.__getitem__
    result = mod.build_queue(
        [1, 2, 3], now=QUEUE_NOW, probe=_clear_probe, loader=loader
    )
    assert result["metrics"] == {
        mod.VERDICT_READY: 1,
        mod.QUEUE_VERDICT_REVIEW_READY: 1,
        mod.QUEUE_VERDICT_STALE: 1,
    }


def test_consume_refuses_mutation_after_dossier():
    snapshot = _reviewed_snapshot()
    snapshot["comments"].append(_comment("posted after dossier"))
    entry = mod.consume_pr(
        123, now=QUEUE_NOW, probe=_clear_probe, loader=lambda pr: snapshot
    )
    assert entry.verdict == mod.QUEUE_VERDICT_STALE


def test_consume_ready_nominal():
    entry = mod.consume_pr(
        123, now=QUEUE_NOW, probe=_clear_probe,
        loader=lambda pr: _reviewed_snapshot(),
    )
    assert entry.verdict == mod.VERDICT_READY
    assert entry.to_json()["verdict"] == mod.VERDICT_READY
# --- #17315 : le cout de l'invocation est mesure et publie -------------------
#
# Le bucket GraphQL est partage par toute la flotte ; le bucket REST (core) est
# par machine. L'organe publie les deux pour qu'une lane secretaire puisse
# agreger le cout d'une campagne sans instrumenter le reseau.


def _reset_api_usage() -> None:
    mod.API_USAGE["rest"] = 0
    mod.API_USAGE["graphql"] = 0


class _Completed:
    def __init__(self, stdout: str) -> None:
        self.returncode = 0
        self.stdout = stdout
        self.stderr = ""


def test_api_usage_counter_separates_the_two_buckets(monkeypatch):
    """`gh api graphql` paie le bucket partage, tout le reste le bucket core."""
    monkeypatch.setattr(
        mod.subprocess, "run", lambda *a, **k: _Completed('{"ok": true}')
    )
    _reset_api_usage()

    mod.gh_json(["api", "graphql", "-f", "query={...}"])
    mod.gh_json(["api", "repos/o/r/pulls/1"])
    mod.gh_json(["api", "repos/o/r/commits/deadbeef/check-runs"])
    mod.gh_json(["pr", "view", "1", "--json", "state"])

    assert mod.API_USAGE == {"rest": 3, "graphql": 1}


def test_api_usage_is_published_in_json_and_on_stderr(monkeypatch, capsys):
    """Le cout accompagne le verdict : cle `api_usage` en --json, ligne stderr
    sinon -- stdout reste le verdict que les appelants parsent."""
    _reset_api_usage()
    rc = _run_main(monkeypatch, _snapshot(_body()), "--json")
    captured = capsys.readouterr()

    assert rc == mod.EXIT_READY
    payload = json.loads(captured.out)
    assert payload["api_usage"] == {"rest": 0, "graphql": 0}
    assert "API usage: 0 REST, 0 GraphQL operation(s)" in captured.err


# --- #17315 : les reviewThreads passent en une operation par lot -------------


def _bulk_gh_json(calls: list[list[str]], payload_for):
    def fake(args: list[str]):
        calls.append(list(args))
        assert args[0] == "api" and args[1] == "graphql"
        # Les alias demandes sont les `-F pN=<pr>` de la requete.
        prs = [int(a.split("=", 1)[1]) for a in args if a.startswith("p") and "=" in a]
        query = next(a for a in args if a.startswith("query="))
        requested = sorted(prs) if "repository(owner:$owner" in query else []
        return payload_for(requested, args)

    return fake


def _threads_payload(prs, *, overflow=(), unresolved=0):
    data = {}
    for index, pr in enumerate(prs):
        nodes = [
            {"id": f"t{pr}-{n}", "isResolved": n >= unresolved, "path": "a.py",
             "line": n, "comments": {"totalCount": 1, "nodes": [{"id": "c"}]}}
            for n in range(1, 2 + (1 if pr in overflow else 0))
        ]
        data[f"p{index}"] = {
            "pullRequest": {
                "reviewThreads": {
                    "nodes": nodes,
                    "pageInfo": {"hasNextPage": pr in overflow, "endCursor": "cur"},
                }
            }
        }
    return {"data": data}


def test_review_threads_bulk_collapses_n_prs_into_one_operation(monkeypatch):
    """Le geste mesure : N PRs = 1 operation GraphQL, pas N."""
    calls: list[list[str]] = []
    monkeypatch.setattr(
        mod, "gh_json", _bulk_gh_json(calls, lambda prs, args: _threads_payload(prs))
    )

    result = mod.review_threads_bulk([11, 12, 13, 14])

    assert len(calls) == 1
    assert sorted(result) == [11, 12, 13, 14]
    # Chaque PR recoit SES threads, pas ceux de l'alias voisin.
    assert [t["id"] for t in result[13]] == ["t13-1"]


def test_review_threads_bulk_chunks_above_the_batch_size(monkeypatch):
    calls: list[list[str]] = []
    monkeypatch.setattr(
        mod, "gh_json", _bulk_gh_json(calls, lambda prs, args: _threads_payload(prs))
    )

    result = mod.review_threads_bulk(list(range(1, 10)))

    assert len(calls) == 2, "9 PRs a batch=8 = 2 operations"
    assert sorted(result) == list(range(1, 10))


def test_review_threads_bulk_deduplicates_and_keeps_order(monkeypatch):
    calls: list[list[str]] = []
    monkeypatch.setattr(
        mod, "gh_json", _bulk_gh_json(calls, lambda prs, args: _threads_payload(prs))
    )

    result = mod.review_threads_bulk([7, 7, 7])

    assert len(calls) == 1
    assert sorted(result) == [7]


def test_review_threads_bulk_falls_back_per_pr_on_overflow(monkeypatch):
    """Une PR dont les threads debordent la premiere page repart en pagination
    par PR -- pour ELLE seule ; les autres restent dans l'operation du lot."""
    calls: list[list[str]] = []
    pages = {13: 0}

    def fake(args: list[str]):
        calls.append(list(args))
        if "query($owner:String!,$repo:String!,$number:Int!" in " ".join(args):
            pages[13] += 1
            if pages[13] == 1:
                return {
                    "data": {"repository": {"pullRequest": {"reviewThreads": {
                        "nodes": [{"id": "t13-page1", "isResolved": True,
                                   "comments": {"totalCount": 1, "nodes": [{}]}}],
                        "pageInfo": {"hasNextPage": True, "endCursor": "c1"},
                    }}}}
                }
            return {
                "data": {"repository": {"pullRequest": {"reviewThreads": {
                    "nodes": [{"id": "t13-page2", "isResolved": True,
                               "comments": {"totalCount": 1, "nodes": [{}]}}],
                    "pageInfo": {"hasNextPage": False, "endCursor": None},
                }}}}
            }
        prs = [int(a.split("=", 1)[1]) for a in args if a.startswith("p") and "=" in a]
        return _threads_payload(prs, overflow={13})

    monkeypatch.setattr(mod, "gh_json", fake)

    result = mod.review_threads_bulk([12, 13])

    assert [t["id"] for t in result[13]] == ["t13-page1", "t13-page2"]
    assert [t["id"] for t in result[12]] == ["t12-1"]
    assert len(calls) == 3, "1 lot + 2 pages pour la seule PR 13"


def test_review_threads_bulk_preserves_the_inline_pagination_refusal(monkeypatch):
    """Le garde-fou >100 commentaires inline survit au batching : sans lui une
    page tronquee se lirait comme un thread complet."""

    def fake(args: list[str]):
        return {"data": {"p0": {"pullRequest": {"reviewThreads": {
            "nodes": [{"id": "t", "isResolved": True, "comments": {
                "totalCount": 120, "nodes": [{"id": "c"}],
            }}],
            "pageInfo": {"hasNextPage": False, "endCursor": None},
        }}}}}

    monkeypatch.setattr(mod, "gh_json", fake)

    with pytest.raises(RuntimeError, match="more than 100 comments"):
        mod.review_threads_bulk([42])


def test_review_threads_single_pr_is_still_one_operation(monkeypatch):
    calls: list[list[str]] = []
    monkeypatch.setattr(
        mod, "gh_json", _bulk_gh_json(calls, lambda prs, args: _threads_payload(prs))
    )

    threads = mod.review_threads(9)

    assert len(calls) == 1
    assert [t["id"] for t in threads] == ["t9-1"]
