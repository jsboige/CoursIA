#!/usr/bin/env python3
"""Tests for ``scripts/coordination/debt_ledger.py`` -- the shared debt ledgers.

The ledgers are append-only journals carried by two DEDICATED RooSync workspace
dashboards; the reducer is the only place where the journal is folded into
state, and it must be trustworthy on five properties that are each a real
fleet failure mode:

  * two lanes observing the same entity at the same instant never clobber each
    other (distinct observations survive, the merge is deterministic);
  * an observation taken against a SUPERSEDED PR head never overwrites the
    current head's reserves/checks/dossier -- a stale view is not a verdict;
  * a re-append of the same observation is a no-op, and a re-fold of the same
    journal yields the same state (idempotency, not "mostly idempotent");
  * a malformed observation is REJECTED with its reason rather than silently
    merged into a phantom field;
  * the summary carries the EAT (issue debt) and PR metrics the cycle decides on,
    and follow-ups are tracked as named issues or explicit waivers.

Run: python -m pytest scripts/tests/test_debt_ledger.py
"""
from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import debt_ledger as dl  # noqa: E402

NOW = datetime(2026, 9, 17, 20, 0, 0, tzinfo=timezone.utc)
FROZEN = "--now=2026-09-17T20:00:00Z"
HEAD_A = "a" * 40
HEAD_B = "b" * 40
HEAD_C = "c" * 40


# --- helpers -----------------------------------------------------------------


def issue_obs(
    issue: int = 15545,
    *,
    actor: str = "myia-po-2025:CoursIA-2",
    observed_at: str = "2026-09-17T19:00:00Z",
    confidence: str = "high",
    evidence: str = "gh issue view 15545",
    **fields,
) -> dict:
    return {
        "schema": dl.OBSERVATION_SCHEMA,
        "ledger": dl.ISSUE_DEBT,
        "actor": actor,
        "observed_at": observed_at,
        "confidence": confidence,
        "evidence": evidence,
        "entity": {"repo": "jsboige/CoursIA", "issue": issue},
        "fields": dict(fields),
    }


def pr_obs(
    pr: int = 16001,
    *,
    head: str = HEAD_A,
    actor: str = "myia-po-2025:CoursIA-2",
    observed_at: str = "2026-09-17T19:00:00Z",
    confidence: str = "high",
    evidence: str = "gh pr view 16001",
    head_transition: bool = False,
    **fields,
) -> dict:
    return {
        "schema": dl.OBSERVATION_SCHEMA,
        "ledger": dl.PR_ACTIONS,
        "actor": actor,
        "observed_at": observed_at,
        "confidence": confidence,
        "evidence": evidence,
        "entity": {"repo": "jsboige/CoursIA", "pr": pr, "head_sha": head},
        "head_transition": head_transition,
        "fields": dict(fields),
    }


def journal(ledger: str, observations, *, kind: str = "full", archives=None) -> dict:
    messages = []
    for index, obs in enumerate(observations):
        normalized = dl.parse_observation(obs, ledger)
        messages.append(
            {
                "messageId": f"msg-{index}",
                "author": normalized["actor"],
                "createdAt": normalized["observed_at"],
                "content": dl.envelope_line(normalized),
            }
        )
    return {
        "schema": dl.EXPORT_SCHEMA,
        "ledger": ledger,
        "window": {"kind": kind, "archives": list(archives or [])},
        "messages": messages,
    }


def authorless_envelope(*, drop=("actor",), **fields) -> str:
    """An envelope WITHOUT ``actor``: the transport author is the only source.

    That is the real producer shape -- the message carries the author, the
    envelope carries the observation -- so the author adapter is what decides.
    Dropping ``observed_at`` too leaves the message timestamp as the only clock.
    """
    raw = {key: value for key, value in issue_obs(**fields).items() if key not in drop}
    return f"{dl.ENVELOPE_PREFIX} {dl.canonical_json(raw)}"


def reduce_it(ledger: str, observations, **kwargs):
    return dl.reduce_ledger(ledger=ledger, export=journal(ledger, observations), now=NOW, **kwargs)


def row_of(snapshot, key: str) -> dict:
    snapshot = getattr(snapshot, "snapshot", snapshot)
    return next(row for row in snapshot["rows"] if row["key"] == key)


def state_of(snapshot) -> dict:
    """The state that must survive a re-fold: values, verdict, current head."""
    snapshot = getattr(snapshot, "snapshot", snapshot)
    return {
        row["key"]: (
            row["fields"],
            row["historical"],
            (row.get("head") or {}).get("current"),
        )
        for row in snapshot["rows"]
    }


# --- observation identity ----------------------------------------------------


def test_observation_id_is_content_derived_and_stable():
    first = dl.parse_observation(issue_obs(state_class="open-blocked"), dl.ISSUE_DEBT)
    again = dl.parse_observation(issue_obs(state_class="open-blocked"), dl.ISSUE_DEBT)
    other = dl.parse_observation(issue_obs(state_class="closed"), dl.ISSUE_DEBT)
    assert first["observation_id"] == again["observation_id"]
    assert first["observation_id"] != other["observation_id"]
    assert first["observation_id"].startswith("obs-")


def test_envelope_round_trips_and_tolerates_missing_prefix():
    observation = dl.parse_observation(issue_obs(state_class="open-actionable"), dl.ISSUE_DEBT)
    line = dl.envelope_line(observation)
    assert line.startswith(dl.ENVELOPE_PREFIX)
    assert dl.parse_envelope(line) == observation
    assert dl.parse_envelope(line[len(dl.ENVELOPE_PREFIX) :]) == observation


def test_observation_id_mismatch_is_refused():
    observation = dl.parse_observation(issue_obs(state_class="open-actionable"), dl.ISSUE_DEBT)
    tampered = dict(observation, observation_id="obs-0000000000000000")
    with pytest.raises(dl.ObservationError) as excinfo:
        dl.parse_observation(tampered, dl.ISSUE_DEBT)
    assert excinfo.value.reason == "observation_id_mismatch"


# --- concurrency -------------------------------------------------------------


def test_concurrent_distinct_observations_both_survive(tmp_path):
    """Two lanes, same entity, same instant, different reads: no clobbering."""
    first = dl.parse_observation(
        issue_obs(actor="myia-po-2025:CoursIA-2", eat_hours=4.0, state_class="open-blocked"),
        dl.ISSUE_DEBT,
    )
    second = dl.parse_observation(
        issue_obs(actor="myia-po-2026:CoursIA", eat_hours=1.5, state_class="open-actionable"),
        dl.ISSUE_DEBT,
    )
    assert first["observation_id"] != second["observation_id"]

    path_a, created_a = dl.spool_observation(tmp_path, first)
    path_b, created_b = dl.spool_observation(tmp_path, second)
    assert created_a and created_b
    assert path_a != path_b
    assert len(list(tmp_path.glob("*.json"))) == 2

    snapshot = reduce_it(dl.ISSUE_DEBT, [
        issue_obs(actor="myia-po-2025:CoursIA-2", eat_hours=4.0, state_class="open-blocked"),
        issue_obs(actor="myia-po-2026:CoursIA", eat_hours=1.5, state_class="open-actionable"),
    ])
    row = row_of(snapshot, "jsboige/CoursIA#15545")
    # Same observed_at: the tie-break is declared (actor ascending), not left to
    # filesystem enumeration order.
    assert row["provenance"]["eat_hours"]["actor"] == "myia-po-2026:CoursIA"
    assert row["provenance"]["eat_hours"]["value"] == 1.5
    assert sorted(entry["actor"] for entry in row["history"]["eat_hours"]) == [
        "myia-po-2025:CoursIA-2",
        "myia-po-2026:CoursIA",
    ]
    assert [entry["applied"] for entry in row["history"]["eat_hours"]] == [False, True]


def test_merge_order_is_actor_then_digest_and_never_filesystem_order():
    observations = [
        issue_obs(actor="myia-po-2025:CoursIA-2", eat_hours=4.0),
        issue_obs(actor="myia-po-2026:CoursIA", eat_hours=1.5),
    ]
    forward = reduce_it(dl.ISSUE_DEBT, observations)
    backward = reduce_it(dl.ISSUE_DEBT, list(reversed(observations)))
    assert state_of(forward) == state_of(backward)


# --- PR head rule ------------------------------------------------------------


def test_stale_head_does_not_overwrite_current_head():
    """#1068-class trap: a late observation against a dead head is not a verdict."""
    snapshot = reduce_it(
        dl.PR_ACTIONS,
        [
            pr_obs(head=HEAD_A, observed_at="2026-09-17T18:00:00Z",
                   live_reserves=["r1"], action_class="review-ready"),
            pr_obs(head=HEAD_B, observed_at="2026-09-17T18:30:00Z",
                   live_reserves=["r2"], action_class="needs-repair", next_action="fix the reserve"),
            # Newer than everything, but taken against the head that HEAD_B replaced.
            pr_obs(head=HEAD_A, observed_at="2026-09-17T19:00:00Z",
                   live_reserves=["r3"], action_class="ready-to-merge", next_action="merge now"),
        ],
    )
    row = row_of(snapshot, "jsboige/CoursIA#16001")
    assert row["head"]["current"] == HEAD_B
    assert row["fields"]["live_reserves"] == [{"summary": "r2"}]
    assert row["fields"]["next_action"] == "fix the reserve"
    # Head-independent fields still take the newest read: they describe the PR,
    # not a commit.
    assert row["fields"]["action_class"] == "ready-to-merge"
    assert row["head"]["stale_head_observations"] == 1
    stale = [entry for entry in row["history"]["live_reserves"] if entry["reason"] == "stale_head"]
    assert len(stale) == 1
    assert stale[0]["value"] == [{"summary": "r3"}]
    assert stale[0]["head_sha"] == HEAD_A


def test_stale_head_refusal_survives_a_checkpoint_refold():
    """A -> B -> stale A, then two more cycles that only re-fold the checkpoint.

    The defect this pins: folding a history entry stamped it as a DECLARED head
    transition, so a head the reducer had already refused came back as a
    force-push on every re-fold -- the ledger drifted toward the stale view
    instead of holding the refusal.
    """
    stale_a = pr_obs(
        head=HEAD_A, observed_at="2026-09-17T19:00:00Z", actor="myia-po-2026:CoursIA",
        live_reserves=["r3"], next_action="merge now",
    )
    cycle1 = reduce_it(
        dl.PR_ACTIONS,
        [
            pr_obs(head=HEAD_A, observed_at="2026-09-17T18:00:00Z", live_reserves=["r1"]),
            pr_obs(head=HEAD_B, observed_at="2026-09-17T18:30:00Z", live_reserves=["r2"]),
            stale_a,
        ],
    )
    first = row_of(cycle1, "jsboige/CoursIA#16001")
    assert first["head"]["current"] == HEAD_B
    assert first["fields"]["live_reserves"] == [{"summary": "r2"}]
    assert first["head"]["stale_head_observations"] == 1

    # Cycle 2: the dashboard archived the journal, so the tail is EMPTY -- only
    # the checkpoint carries the refusal.
    cycle2 = dl.reduce_ledger(
        ledger=dl.PR_ACTIONS,
        export=journal(dl.PR_ACTIONS, [], kind="incremental"),
        prior_snapshot=cycle1.snapshot,
        now=NOW,
    )
    second = row_of(cycle2, "jsboige/CoursIA#16001")
    assert second["head"]["current"] == HEAD_B
    assert second["fields"]["live_reserves"] == [{"summary": "r2"}]
    assert second["head"]["stale_head_observations"] == 1
    assert second["head"]["superseded_heads"] == [HEAD_A]
    refused = [entry for entry in second["history"]["live_reserves"]
               if entry["reason"] == "stale_head"]
    assert len(refused) == 1
    assert refused[0]["value"] == [{"summary": "r3"}]

    # Cycle 3: the same journal is replayed on top of the checkpoint -- a replay
    # must not change the verdict either.
    cycle3 = dl.reduce_ledger(
        ledger=dl.PR_ACTIONS,
        export=journal(dl.PR_ACTIONS, [stale_a], kind="incremental"),
        prior_snapshot=cycle2.snapshot,
        now=NOW,
    )
    third = row_of(cycle3, "jsboige/CoursIA#16001")
    assert third["head"]["current"] == HEAD_B
    assert third["fields"]["live_reserves"] == [{"summary": "r2"}]
    assert third["head"]["stale_head_observations"] == 1
    assert third["head"]["head_regressions"] == 0


def test_stale_count_is_per_observation_not_per_field():
    """One observation carrying three head-bound fields is ONE stale observation."""
    snapshot = reduce_it(
        dl.PR_ACTIONS,
        [
            pr_obs(head=HEAD_A, observed_at="2026-09-17T18:00:00Z", live_reserves=["r1"]),
            pr_obs(head=HEAD_B, observed_at="2026-09-17T18:30:00Z", live_reserves=["r2"]),
            pr_obs(head=HEAD_A, observed_at="2026-09-17T19:00:00Z",
                   live_reserves=["r3"], live_checks={"PR gate": "failure"},
                   next_action="merge now", update_branch_status="behind"),
        ],
    )
    row = row_of(snapshot, "jsboige/CoursIA#16001")
    assert row["head"]["stale_head_observations"] == 1
    assert row["diagnostics"]["stale_head_observations"] == 1
    assert snapshot.summary["heads"]["stale_head_observations"] == 1


def test_a_declared_rewind_is_still_honoured_after_a_refusal():
    """The refusal rule must not swallow a genuine force-push declaration."""
    snapshot = reduce_it(
        dl.PR_ACTIONS,
        [
            pr_obs(head=HEAD_A, observed_at="2026-09-17T18:00:00Z", live_reserves=["r1"]),
            pr_obs(head=HEAD_B, observed_at="2026-09-17T18:30:00Z", live_reserves=["r2"]),
            pr_obs(head=HEAD_A, observed_at="2026-09-17T19:00:00Z", live_reserves=["r3"]),
            pr_obs(head=HEAD_A, observed_at="2026-09-17T19:30:00Z", head_transition=True,
                   live_reserves=["r4"]),
        ],
    )
    row = row_of(snapshot, "jsboige/CoursIA#16001")
    assert row["head"]["current"] == HEAD_A
    assert row["fields"]["live_reserves"] == [{"summary": "r4"}]
    assert row["head"]["head_regressions"] == 1
    assert row["head"]["stale_head_observations"] == 1


def test_declared_head_transition_allows_a_forced_rewind():
    snapshot = reduce_it(
        dl.PR_ACTIONS,
        [
            pr_obs(head=HEAD_A, observed_at="2026-09-17T18:00:00Z", live_reserves=["r1"]),
            pr_obs(head=HEAD_B, observed_at="2026-09-17T18:30:00Z", live_reserves=["r2"]),
            pr_obs(head=HEAD_A, observed_at="2026-09-17T19:00:00Z", head_transition=True,
                   live_reserves=["r3"]),
        ],
    )
    row = row_of(snapshot, "jsboige/CoursIA#16001")
    assert row["head"]["current"] == HEAD_A
    assert row["fields"]["live_reserves"] == [{"summary": "r3"}]
    assert row["head"]["head_regressions"] == 1
    assert row["head"]["stale_head_observations"] == 0


def test_short_head_sha_is_refused():
    raw = pr_obs(head="abc1234", live_reserves=["r"])
    with pytest.raises(dl.ObservationError) as excinfo:
        dl.parse_observation(raw, dl.PR_ACTIONS)
    assert excinfo.value.reason == "short_head_sha"


# --- idempotency -------------------------------------------------------------


def test_reappending_the_same_observation_is_a_no_op(tmp_path):
    observation = dl.parse_observation(issue_obs(state_class="open-blocked"), dl.ISSUE_DEBT)
    path, created = dl.spool_observation(tmp_path, observation)
    again_path, again_created = dl.spool_observation(tmp_path, observation)
    assert created is True and again_created is False
    assert path == again_path
    assert len(list(tmp_path.glob("*.json"))) == 1


def test_refolding_the_same_journal_is_byte_identical():
    observations = [
        issue_obs(issue=1, state_class="open-blocked", eat_hours=4.0),
        issue_obs(issue=2, state_class="open-actionable", eat_hours=1.0,
                  actor="myia-po-2026:CoursIA"),
    ]
    first = reduce_it(dl.ISSUE_DEBT, observations)
    second = reduce_it(dl.ISSUE_DEBT, observations)
    assert dl.canonical_json(first.snapshot) == dl.canonical_json(second.snapshot)


def test_incremental_refold_of_the_same_events_preserves_rows_exactly():
    """Archive-aware: the checkpoint fold must not inflate or drift the rows."""
    observations = [
        pr_obs(head=HEAD_A, observed_at="2026-09-17T18:00:00Z",
               live_reserves=["r1"], action_class="review-ready", review_required=True),
        pr_obs(head=HEAD_B, observed_at="2026-09-17T18:30:00Z",
               live_reserves=["r2"], update_branch_status="behind", dossier_status="stale"),
    ]
    full = reduce_it(dl.PR_ACTIONS, observations)
    incremental = dl.reduce_ledger(
        ledger=dl.PR_ACTIONS,
        export=journal(dl.PR_ACTIONS, observations, kind="incremental", archives=["arch-1"]),
        prior_snapshot=full.snapshot,
        now=NOW,
    )
    assert incremental.snapshot["rows"] == full.snapshot["rows"]
    assert incremental.summary["action_class"] == full.summary["action_class"]


# --- archive-aware checkpoint contract ---------------------------------------


def test_incremental_window_without_checkpoint_fails_closed():
    export = journal(dl.ISSUE_DEBT, [issue_obs(state_class="open-blocked")], kind="incremental")
    with pytest.raises(dl.LedgerError) as excinfo:
        dl.reduce_ledger(ledger=dl.ISSUE_DEBT, export=export, now=NOW)
    assert excinfo.value.reason == "MISSING_CHECKPOINT"


def test_undeclared_window_is_treated_as_incremental():
    export = journal(dl.ISSUE_DEBT, [issue_obs(state_class="open-blocked")])
    del export["window"]
    with pytest.raises(dl.LedgerError) as excinfo:
        dl.reduce_ledger(ledger=dl.ISSUE_DEBT, export=export, now=NOW)
    assert excinfo.value.reason == "MISSING_CHECKPOINT"


def test_archive_fold_carries_state_when_the_journal_is_condensed_away():
    """The whole point of the checkpoint: a condensed journal loses nothing."""
    full = reduce_it(
        dl.ISSUE_DEBT,
        [
            issue_obs(issue=1, state_class="open-blocked", eat_hours=4.0,
                      followup={"kind": "issue", "repo": "jsboige/CoursIA", "number": 16100}),
            issue_obs(issue=2, state_class="closed", closeability="unknown"),
        ],
    )
    # Next cycle the dashboard has archived both messages: the tail is empty.
    tail = dl.reduce_ledger(
        ledger=dl.ISSUE_DEBT,
        export=journal(dl.ISSUE_DEBT, [], kind="incremental", archives=["arch-2026-09-01"]),
        prior_snapshot=full.snapshot,
        now=NOW,
    )
    assert state_of(tail.snapshot) == state_of(full.snapshot)
    assert tail.snapshot["checkpoint"]["window"]["archives"] == ["arch-2026-09-01"]


def test_an_older_export_cannot_regress_state():
    observations = [issue_obs(state_class="open-actionable", eat_hours=2.0,
                              observed_at="2026-09-17T19:00:00Z")]
    newer = reduce_it(dl.ISSUE_DEBT, observations)
    stale = dl.reduce_ledger(
        ledger=dl.ISSUE_DEBT,
        export=journal(
            dl.ISSUE_DEBT,
            [issue_obs(state_class="open-blocked", eat_hours=9.0,
                       observed_at="2026-09-17T08:00:00Z")],
            kind="incremental",
        ),
        prior_snapshot=newer.snapshot,
        now=NOW,
    )
    row = row_of(stale.snapshot, "jsboige/CoursIA#15545")
    assert row["fields"]["state_class"] == "open-actionable"
    assert row["fields"]["eat_hours"] == 2.0
    assert any("export_older_than_checkpoint" in warning for warning in stale.warnings)


def test_checkpoint_ledger_mismatch_is_fatal():
    issue_snapshot = reduce_it(dl.ISSUE_DEBT, [issue_obs(state_class="open-blocked")]).snapshot
    with pytest.raises(dl.LedgerError) as excinfo:
        dl.reduce_ledger(
            ledger=dl.PR_ACTIONS,
            export=journal(dl.PR_ACTIONS, [pr_obs(live_reserves=["r"])], kind="incremental"),
            prior_snapshot=issue_snapshot,
            now=NOW,
        )
    assert excinfo.value.reason == "CHECKPOINT_LEDGER_MISMATCH"


def test_replayed_observation_is_counted():
    observation = issue_obs(state_class="open-blocked")
    first = reduce_it(dl.ISSUE_DEBT, [observation])
    second = dl.reduce_ledger(
        ledger=dl.ISSUE_DEBT,
        export=journal(dl.ISSUE_DEBT, [observation], kind="incremental"),
        prior_snapshot=first.snapshot,
        now=NOW,
    )
    assert second.summary["replayed_observations"] == 1
    assert second.snapshot["checkpoint"]["events"]["replayed"] == 1


# --- invalid entries ---------------------------------------------------------


@pytest.mark.parametrize(
    ("observation", "reason"),
    [
        (dict(issue_obs(state_class="open-blocked"), schema="debt-ledger-observation/v9"),
         "unsupported_schema_version"),
        (dict(issue_obs(state_class="open-blocked"), ledger=dl.PR_ACTIONS), "ledger_mismatch"),
        (dict(issue_obs(state_class="open-blocked"), verdict="nope"), "unknown_key"),
        (dict(issue_obs(state_class="open-blocked"), fields={"state": "open-blocked"}),
         "unknown_field"),
        (dict(issue_obs(state_class="open-blocked"), fields={"state_class": "closedish"}),
         "invalid_field_value"),
        (dict(issue_obs(state_class="open-blocked"), confidence="certain"), "invalid_confidence"),
        (dict(issue_obs(state_class="open-blocked"), actor="po 2025"), "missing_actor"),
        (dict(issue_obs(state_class="open-blocked"), evidence=""), "missing_evidence"),
        (dict(issue_obs(state_class="open-blocked"), observed_at="2026-09-17T19:00:00"),
         "naive_timestamp"),
        (dict(issue_obs(state_class="open-blocked"), observed_at="2026-09-17T21:00:00+02:00"),
         "non_utc_timestamp"),
        (dict(issue_obs(state_class="open-blocked"), observed_at="yesterday"), "invalid_timestamp"),
        (dict(issue_obs(state_class="open-blocked"),
              entity={"repo": "jsboige/CoursIA", "issue": 15545, "pr": 1}), "entity_mismatch"),
        (dict(issue_obs(state_class="open-blocked"), fields={"eat_hours": -1}),
         "invalid_field_value"),
        (dict(issue_obs(state_class="open-blocked"), fields={"followup": {"kind": "waiver"}}),
         "invalid_field_value"),
        (dict(issue_obs(state_class="open-blocked"),
              fields={"dependencies": [{"kind": "banana", "number": 1}]}),
         "invalid_field_value"),
    ],
)
def test_invalid_observations_are_rejected_with_a_reason(observation, reason):
    result = dl.reduce_ledger(
        ledger=dl.ISSUE_DEBT,
        export={"schema": dl.EXPORT_SCHEMA, "ledger": dl.ISSUE_DEBT,
                "window": {"kind": "full"},
                "messages": [{"messageId": "m", "author": "ai-01",
                              "createdAt": "2026-09-17T19:00:00Z",
                              "content": dl.canonical_json(observation)}]},
        now=NOW,
    )
    assert result.snapshot["rows"] == []
    assert [item["reason"] for item in result.snapshot["rejections"]] == [reason]
    assert result.summary["rejections"]["by_reason"] == {reason: 1}


def test_an_unparsable_message_body_is_rejected_without_killing_the_export():
    export = {
        "schema": dl.EXPORT_SCHEMA,
        "ledger": dl.ISSUE_DEBT,
        "window": {"kind": "full"},
        "messages": [
            {"messageId": "bad", "content": "[OBS] not json at all"},
            {"messageId": "good", "author": "ai-01", "createdAt": "2026-09-17T19:00:00Z",
             "content": dl.envelope_line(dl.parse_observation(
                 issue_obs(state_class="open-blocked"), dl.ISSUE_DEBT))},
        ],
    }
    result = dl.reduce_ledger(ledger=dl.ISSUE_DEBT, export=export, now=NOW)
    assert len(result.snapshot["rows"]) == 1
    assert [item["reason"] for item in result.snapshot["rejections"]] == ["unparsable_envelope"]


def test_export_ledger_mismatch_is_fatal_not_silent():
    export = journal(dl.ISSUE_DEBT, [issue_obs(state_class="open-blocked")])
    export["ledger"] = dl.PR_ACTIONS
    with pytest.raises(dl.LedgerError) as excinfo:
        dl.reduce_ledger(ledger=dl.ISSUE_DEBT, export=export, now=NOW)
    assert excinfo.value.reason == "EXPORT_LEDGER_MISMATCH"


def test_a_corrupt_config_degrades_to_the_compiled_in_workspace():
    """The dashboard a ledger lives on is a fact of the code, not of the file."""
    result = dl.reduce_ledger(
        ledger=dl.PR_ACTIONS,
        export=journal(dl.PR_ACTIONS, [pr_obs(live_reserves=["r"])]),
        now=NOW,
        config={"ledgers": {"pr-actions": "not-an-object"}},
    )
    assert result.snapshot["workspace"] == "CoursIA-pr-action-ledger"
    assert result.summary["workspace"] == "CoursIA-pr-action-ledger"


def test_a_producer_shaped_export_is_adapted_not_refused():
    """The real `roosync_dashboard read` envelope, with the REAL field names.

    Field names matter here: the transport writes ``{id, timestamp, author:
    {machineId, workspace}, content}``, not ``messageId``/``createdAt``/``machine``.
    A producer-shape test written with invented keys passes on a parser that
    would refuse every observation the fleet actually posts.
    """
    observation = authorless_envelope(
        drop=("actor", "observed_at"), issue=42, state_class="open-blocked", eat_hours=2.0
    )
    export = {
        "success": True,
        "data": {
            "intercom": {
                "section": "status",
                "messages": [
                    {"id": "msg-77",
                     "timestamp": "2026-09-17T19:00:00Z",
                     "author": {"machineId": "myia-ai-01", "workspace": "CoursIA"},
                     "content": observation},
                    {"id": "msg-78",
                     "timestamp": "2026-09-17T19:05:00Z",
                     "author": {"machineId": "myia-ai-01", "workspace": "CoursIA"},
                     "content": "[LEDGER] pr-actions @ 2026-09-17T19:05:00Z | rows 3 live"},
                ],
            }
        },
    }
    result = dl.reduce_ledger(
        ledger=dl.ISSUE_DEBT,
        export=dict(export, window={"kind": "full", "archives": []}),
        now=NOW,
    )
    row = row_of(result, "jsboige/CoursIA#42")
    assert row["fields"]["state_class"] == "open-blocked"
    assert row["provenance"]["eat_hours"]["actor"] == "myia-ai-01:CoursIA"
    assert row["provenance"]["eat_hours"]["observed_at"] == "2026-09-17T19:00:00Z"
    assert row["provenance"]["eat_hours"]["message_id"] == "msg-77"
    assert result.snapshot["checkpoint"]["window"]["messages"] == 2
    # Dashboard prose is not a malformed observation: it is ignored, not red.
    assert result.snapshot["rejections"] == []
    assert result.summary["window"]["ignored"] == 1


def test_producer_shape_still_fails_closed_on_an_undeclared_window():
    """The adapter finds the journal; it never guesses the coverage."""
    observation = dl.parse_observation(issue_obs(state_class="open-blocked"), dl.ISSUE_DEBT)
    export = {
        "data": {"intercom": {"messages": [
            {"messageId": "m1", "author": {"machine": "a", "workspace": "b"},
             "createdAt": "2026-09-17T19:00:00Z", "content": dl.envelope_line(observation)},
        ]}},
    }
    with pytest.raises(dl.LedgerError) as excinfo:
        dl.reduce_ledger(ledger=dl.ISSUE_DEBT, export=export, now=NOW)
    assert excinfo.value.reason == "MISSING_CHECKPOINT"
    window, records, rejections = dl.parse_journal_export(
        dict(export, window={"kind": "incremental", "archives": ["arch-a"]}), dl.ISSUE_DEBT
    )
    assert window["path"] == "data.intercom.messages"
    assert window["kind"] == "incremental"
    assert window["archives"] == ["arch-a"]
    assert len(records) == 1 and rejections == []


def test_a_message_that_declares_itself_an_observation_still_rejects():
    """Chatter is forgiven; a producer lying about its own format is not."""
    export = {
        "window": {"kind": "full"},
        "messages": [
            {"messageId": "prose", "content": "just a human note"},
            {"messageId": "liar", "content": "[OBS] not json at all"},
        ],
    }
    result = dl.reduce_ledger(ledger=dl.ISSUE_DEBT, export=export, now=NOW)
    assert result.snapshot["rows"] == []
    assert [item["reason"] for item in result.snapshot["rejections"]] == ["unparsable_envelope"]
    assert result.summary["window"]["ignored"] == 1


@pytest.mark.parametrize(
    "author",
    [
        {"machineId": "po-1", "workspace": "CoursIA-2"},  # the real transport shape
        {"machine_id": "po-1", "workspace": "CoursIA-2"},
        {"machine": "po-1", "workspace": "CoursIA-2"},
        {"machineId": "po-1", "lane": "CoursIA-2"},
        {"lane": "po-1:CoursIA-2"},
        "po-1:CoursIA-2",
    ],
)
def test_author_shapes_normalise_to_a_lane(author):
    export = {
        "window": {"kind": "full"},
        "messages": [{"messageId": "m", "author": author,
                      "createdAt": "2026-09-17T19:00:00Z",
                      "content": authorless_envelope(issue=42, state_class="open-blocked")}],
    }
    result = dl.reduce_ledger(ledger=dl.ISSUE_DEBT, export=export, now=NOW)
    assert result.snapshot["rows"][0]["provenance"]["state_class"]["actor"] == "po-1:CoursIA-2"


def test_an_unrecognised_author_shape_is_a_rejection_not_a_crash():
    export = {
        "window": {"kind": "full"},
        "messages": [{"messageId": "m", "author": {"unknown": "shape"},
                      "createdAt": "2026-09-17T19:00:00Z",
                      "content": authorless_envelope(issue=42, state_class="open-blocked")}],
    }
    result = dl.reduce_ledger(ledger=dl.ISSUE_DEBT, export=export, now=NOW)
    assert [item["reason"] for item in result.snapshot["rejections"]] == ["missing_actor"]


def test_an_export_declaring_another_format_is_refused():
    """A future encoding must not be silently misread as this one."""
    export = dict(journal(dl.ISSUE_DEBT, [issue_obs(state_class="open-blocked")]),
                  format="yaml")
    with pytest.raises(dl.LedgerError) as excinfo:
        dl.reduce_ledger(ledger=dl.ISSUE_DEBT, export=export, now=NOW)
    assert excinfo.value.reason == "UNSUPPORTED_EXPORT_FORMAT"


def test_unknown_ledger_is_refused():
    with pytest.raises(dl.LedgerError) as excinfo:
        dl.reduce_ledger(ledger="release-notes", export=[], now=NOW)
    assert excinfo.value.reason == "UNKNOWN_LEDGER"


@pytest.mark.parametrize(
    "fields",
    [
        {"live_checks": {"PR gate": "maybe"}},
        {"live_checks": ["PR gate"]},
        {"live_reserves": {"r1": "open"}},
        {"live_reserves": [{"note": "no summary"}]},
        {"next_action": ""},
        {"action_class": "looks-good"},
        {"review_required": "yes"},
        {"update_branch_status": "stale"},
        {"dossier_status": "pending"},
    ],
)
def test_pr_field_shapes_are_validated(fields):
    with pytest.raises(dl.ObservationError) as excinfo:
        dl.parse_observation(pr_obs(**fields), dl.PR_ACTIONS)
    assert excinfo.value.reason == "invalid_field_value"


def test_pr_field_normalisation_is_canonical():
    observation = dl.parse_observation(
        pr_obs(
            live_reserves=["bare string", {"summary": "with url", "url": "https://x/1"}],
            live_checks={"PR gate": "failure"},
        ),
        dl.PR_ACTIONS,
    )
    assert observation["fields"]["live_reserves"] == [
        {"summary": "bare string"},
        {"summary": "with url", "url": "https://x/1"},
    ]
    assert observation["fields"]["live_checks"] == {"PR gate": "failure"}


# --- terminal rows stay historical -------------------------------------------


def test_closed_and_merged_rows_remain_historical():
    issue_snapshot = reduce_it(
        dl.ISSUE_DEBT,
        [
            issue_obs(issue=1, state_class="closed"),
            issue_obs(issue=2, state_class="open-blocked"),
        ],
    )
    rows = {row["key"]: row for row in issue_snapshot.snapshot["rows"]}
    assert rows["jsboige/CoursIA#1"]["historical"] is True
    assert rows["jsboige/CoursIA#2"]["historical"] is False
    assert issue_snapshot.snapshot["counts"]["historical"] == 1
    assert issue_snapshot.summary["state_class"] == {"open-blocked": 1}

    pr_snapshot = reduce_it(
        dl.PR_ACTIONS,
        [
            pr_obs(pr=10, action_class="merged"),
            pr_obs(pr=11, action_class="ready-to-merge", live_reserves=["r"]),
        ],
    )
    pr_rows = {row["key"]: row for row in pr_snapshot.snapshot["rows"]}
    assert pr_rows["jsboige/CoursIA#10"]["historical"] is True
    assert pr_rows["jsboige/CoursIA#11"]["historical"] is False
    assert pr_snapshot.summary["action_class"] == {"ready-to-merge": 1}


# --- baseline ----------------------------------------------------------------


def test_baseline_rows_are_superseded_by_a_newer_observation():
    baseline = {
        "schema": dl.BASELINE_SCHEMA,
        "ledger": dl.ISSUE_DEBT,
        "generated_at": "2026-09-01T00:00:00Z",
        "actor": "ai-01",
        "rows": [issue_obs(issue=7, state_class="open-stale", eat_hours=9.0,
                           observed_at="2026-09-01T00:00:00Z")],
    }
    snapshot = dl.reduce_ledger(
        ledger=dl.ISSUE_DEBT,
        export=journal(dl.ISSUE_DEBT, [issue_obs(issue=7, state_class="open-actionable",
                                                 eat_hours=2.0)]),
        baseline=baseline,
        now=NOW,
    )
    row = row_of(snapshot, "jsboige/CoursIA#7")
    assert row["fields"]["state_class"] == "open-actionable"
    assert row["fields"]["eat_hours"] == 2.0
    assert row["history"]["eat_hours"][0]["source"] == "baseline"
    assert row["history"]["eat_hours"][1]["applied"] is True


def test_a_baseline_for_another_ledger_is_fatal():
    baseline = {
        "schema": dl.BASELINE_SCHEMA,
        "ledger": dl.PR_ACTIONS,
        "generated_at": "2026-09-01T00:00:00Z",
        "rows": [],
    }
    with pytest.raises(dl.LedgerError) as excinfo:
        dl.reduce_ledger(ledger=dl.ISSUE_DEBT, export=[], baseline=baseline, now=NOW)
    assert excinfo.value.reason == "BASELINE_LEDGER_MISMATCH"


def test_a_malformed_baseline_is_a_loud_configuration_error():
    """A dropped seed is a state nobody would think to look for: refuse it."""
    base = {
        "schema": dl.BASELINE_SCHEMA,
        "ledger": dl.ISSUE_DEBT,
        "generated_at": "2026-09-01T00:00:00Z",
        "rows": [],
    }
    with pytest.raises(dl.LedgerError) as excinfo:
        dl.reduce_ledger(
            ledger=dl.ISSUE_DEBT,
            export=[],
            baseline=dict(base, generated_at="2026-09-01 00:00:00"),
            now=NOW,
        )
    assert excinfo.value.reason == "INVALID_BASELINE"

    with pytest.raises(dl.LedgerError) as excinfo:
        dl.reduce_ledger(
            ledger=dl.ISSUE_DEBT,
            export=[],
            baseline=dict(base, rows=[issue_obs(issue=1, state_class="nope")]),
            now=NOW,
        )
    assert excinfo.value.reason == "INVALID_BASELINE"
    assert "baseline.rows[0]" in excinfo.value.detail


def test_a_corrupt_prior_snapshot_never_crashes_the_fold():
    """An unreadable checkpoint row is dropped, not propagated as a traceback."""
    corrupt = {
        "schema": dl.SNAPSHOT_SCHEMA,
        "ledger": dl.ISSUE_DEBT,
        "rows": [
            {"key": "jsboige/CoursIA#1", "entity": {"repo": "jsboige/CoursIA", "issue": 1},
             "fields": {"state_class": "open-blocked"},
             "history": {"state_class": [
                 {"value": "open-blocked", "observed_at": "not a timestamp", "actor": "ai-01"},
                 {"value": "open-blocked", "observed_at": "2026-09-17T18:00:00Z", "actor": "ai-01"},
             ]}},
            {"entity": "not an entity", "history": {}},
        ],
        "checkpoint": {"events": {"newest_observed_at": "yesterday", "observation_ids_recent": []}},
    }
    result = dl.reduce_ledger(
        ledger=dl.ISSUE_DEBT,
        export=journal(dl.ISSUE_DEBT, [issue_obs(issue=1, state_class="closed")], kind="incremental"),
        prior_snapshot=corrupt,
        now=NOW,
    )
    row = row_of(result, "jsboige/CoursIA#1")
    assert row["fields"]["state_class"] == "closed"
    assert any("checkpoint_newest_unreadable" in warning for warning in result.warnings)


# --- summary: EAT metrics ----------------------------------------------------


def test_summary_carries_eat_metrics():
    snapshot = reduce_it(
        dl.ISSUE_DEBT,
        [
            issue_obs(issue=1, state_class="open-blocked", eat_hours=4.0,
                      remaining_atomic_prs=3, closeability="not-closeable",
                      dependencies=[16000, {"kind": "external", "note": "provider"}]),
            issue_obs(issue=2, state_class="open-blocked", eat_hours=2.5,
                      remaining_atomic_prs=1, closeability="closeable-after-followup",
                      followup={"kind": "issue", "repo": "jsboige/CoursIA", "number": 16100}),
            issue_obs(issue=3, state_class="open-actionable", eat_hours=6.0,
                      remaining_atomic_prs=2, closeability="closeable-now",
                      followup={"kind": "none"}),
            issue_obs(issue=4, state_class="closed", eat_hours=99.0),
        ],
    )
    summary = snapshot.summary
    assert summary["eat_hours"]["total"] == 12.5
    assert summary["eat_hours"]["by_state_class"] == {"open-actionable": 6.0, "open-blocked": 6.5}
    assert summary["eat_hours"]["max_row"] == {"key": "jsboige/CoursIA#3", "eat_hours": 6.0}
    assert summary["remaining_atomic_prs"] == {
        "total": 6,
        "by_state_class": {"open-actionable": 2, "open-blocked": 4},
    }
    assert summary["closeable_now"] == ["jsboige/CoursIA#3"]
    assert summary["dependencies"] == {
        "rows_with_dependencies": 1,
        "edges": 2,
        "external_edges": 1,
    }
    assert summary["rows"] == {
        "total": 4,
        "live": 3,
        "historical": 1,
        # Each live row observed only part of the contract: partial updates are
        # legal, and incompleteness is a metric rather than an error.
        "incomplete": 3,
        "stale": 0,
    }
    assert "eat_hours 12.50" in snapshot.status_text


def test_summary_counts_missing_fields_as_incomplete():
    snapshot = reduce_it(dl.ISSUE_DEBT, [issue_obs(issue=9, state_class="open-blocked")])
    row = row_of(snapshot, "jsboige/CoursIA#9")
    assert "eat_hours" in row["missing_fields"]
    assert snapshot.summary["rows"]["incomplete"] == 1


# --- summary: PR metrics -----------------------------------------------------


def test_summary_carries_pr_action_metrics():
    snapshot = reduce_it(
        dl.PR_ACTIONS,
        [
            pr_obs(pr=20, head=HEAD_A, action_class="review-ready", review_required=True,
                   reviewer="adjoint", producer="myia-po-2025:CoursIA-2",
                   live_reserves=["nit 1", "nit 2"], live_checks={"PR gate": "pending"},
                   update_branch_status="behind", dossier_status="absent"),
            pr_obs(pr=21, head=HEAD_B, action_class="needs-repair", review_required=False,
                   reviewer="Hermes", producer="myia-po-2026:CoursIA",
                   live_reserves=["one"], live_checks={"Scripts Tests": "failure"},
                   update_branch_status="up-to-date", dossier_status="ready"),
            pr_obs(pr=22, head=HEAD_C, action_class="merged"),
        ],
    )
    summary = snapshot.summary
    assert summary["action_class"] == {"needs-repair": 1, "review-ready": 1}
    assert summary["review"] == {
        "required": 1,
        "not_required": 1,
        "unknown": 0,
        "by_reviewer": {"Hermes": 1, "adjoint": 1},
        "by_producer": {"myia-po-2025:CoursIA-2": 1, "myia-po-2026:CoursIA": 1},
    }
    assert summary["reserves"] == {
        "rows_with_live_reserves": 2,
        "live_total": 3,
        "by_action_class": {"needs-repair": 1, "review-ready": 2},
    }
    assert summary["checks"]["rows_with_failing_checks"] == 1
    assert summary["checks"]["status_counts"] == {"failure": 1, "pending": 1}
    assert summary["update_branch_status"] == {"behind": 1, "up-to-date": 1}
    assert summary["dossier_status"] == {"absent": 1, "ready": 1}
    assert summary["review_ready"] == ["jsboige/CoursIA#20"]
    assert summary["rows"]["historical"] == 1
    assert "review_required 1" in snapshot.status_text


def test_status_text_is_bounded_by_status_max_rows():
    observations = [
        pr_obs(pr=100 + index, head=HEAD_A, action_class="needs-review", live_reserves=["r"])
        for index in range(30)
    ]
    snapshot = reduce_it(dl.PR_ACTIONS, observations, config={"status_max_rows": 5})
    body = [line for line in snapshot.status_text.splitlines() if line.startswith("  ")]
    assert len([line for line in body if "more live rows" not in line]) == 5
    assert any("more live rows" in line for line in body)


# --- summary: follow-ups -----------------------------------------------------


def test_followup_tracking_issue_waiver_and_none():
    snapshot = reduce_it(
        dl.ISSUE_DEBT,
        [
            issue_obs(issue=1, state_class="open-blocked",
                      closeability="closeable-after-followup",
                      followup={"kind": "issue", "repo": "jsboige/CoursIA", "number": 16100}),
            issue_obs(issue=2, state_class="open-stale", closeability="not-closeable",
                      followup={"kind": "waiver", "reason": "superseded by #16100"}),
            issue_obs(issue=3, state_class="open-actionable", followup={"kind": "none"}),
            issue_obs(issue=4, state_class="open-actionable"),
        ],
    )
    assert snapshot.summary["followups"] == {"issue": 1, "waiver": 1, "none": 1, "missing": 1}
    waived = row_of(snapshot, "jsboige/CoursIA#2")
    assert waived["fields"]["followup"] == {"kind": "waiver", "reason": "superseded by #16100"}
    named = row_of(snapshot, "jsboige/CoursIA#1")
    assert named["fields"]["followup"] == {
        "kind": "issue",
        "repo": "jsboige/CoursIA",
        "number": 16100,
    }
    # The names have to be in the compact status: a follow-up nobody reads is a
    # residue nobody inherits.
    assert "followups: issue 1, waiver 1, none 1, missing 1" in snapshot.status_text


# --- local state tree, atomicity, lock ---------------------------------------


def test_init_dry_run_creates_nothing_then_apply_writes_the_contract(tmp_path, capsys):
    assert dl.main(["init", "--state-dir", str(tmp_path), FROZEN]) == 0
    assert list(tmp_path.iterdir()) == []
    assert "DRY-RUN" in capsys.readouterr().out

    assert dl.main(["init", "--state-dir", str(tmp_path), "--apply", FROZEN]) == 0
    config = json.loads((tmp_path / "config.json").read_text(encoding="utf-8"))
    assert config["schema"] == dl.CONFIG_SCHEMA
    assert config["ledgers"][dl.ISSUE_DEBT]["workspace"] == "CoursIA-issue-debt-ledger"
    assert config["ledgers"][dl.PR_ACTIONS]["workspace"] == "CoursIA-pr-action-ledger"

    doc = json.loads((tmp_path / dl.ISSUE_DEBT / "schema.json").read_text(encoding="utf-8"))
    assert doc["schema"] == dl.SCHEMA_DOC_VERSION
    assert doc["transport"]["envelope_prefix"] == dl.ENVELOPE_PREFIX
    names = [entry["name"] for entry in doc["ledgers"][dl.ISSUE_DEBT]["fields"]]
    assert names == ["state_class", "closeability", "remaining_atomic_prs", "eat_hours",
                     "dependencies", "followup"]
    assert doc["dashboard_calls"]["append_observation"].startswith("roosync_dashboard(action:\"append\"")
    baseline = json.loads((tmp_path / dl.PR_ACTIONS / "baseline.json").read_text(encoding="utf-8"))
    assert baseline["schema"] == dl.BASELINE_SCHEMA


def test_state_dir_inside_roosync_shared_path_is_refused(tmp_path, monkeypatch):
    shared = tmp_path / "shared"
    monkeypatch.setenv("ROOSYNC_SHARED_PATH", str(shared))
    with pytest.raises(dl.LedgerError) as excinfo:
        dl.assert_local_output(shared / "coordinator" / "debt-ledgers", what="state directory")
    assert excinfo.value.reason == "SHARED_PATH_REFUSED"
    # ... and the refusal is what a CLI call hits, not a warning it can ignore.
    assert dl.main(["init", "--state-dir", str(shared / "debt"), "--apply"]) == 1
    assert not (shared / "debt").exists()


def test_state_dir_inside_the_repo_is_refused(tmp_path):
    """Ledger state is not repo content -- the documented rule, enforced."""
    repo_root = Path(__file__).resolve().parents[2]
    assert (repo_root / ".git").exists()
    target = repo_root / "ledger-state-should-not-exist"
    with pytest.raises(dl.LedgerError) as excinfo:
        dl.assert_local_output(target, what="state directory")
    assert excinfo.value.reason == "REPO_PATH_REFUSED"
    assert dl.main(["init", "--state-dir", str(target), "--apply"]) == 1
    assert not target.exists()


@pytest.mark.parametrize("flag", ["--out", "--out-dir"])
def test_append_output_flags_are_guarded_too(tmp_path, monkeypatch, flag):
    """Guarding only the state dir left four explicit flags as a side door."""
    shared = tmp_path / "shared"
    monkeypatch.setenv("ROOSYNC_SHARED_PATH", str(shared))
    exit_code = dl.main([
        "append", "--ledger", dl.ISSUE_DEBT, "--entity", "jsboige/CoursIA#1",
        "--actor", "ai-01", "--evidence", "e", "--fields-json", '{"state_class": "open-blocked"}',
        "--state-dir", str(tmp_path / "state"), flag, str(shared / "spool"),
    ])
    assert exit_code == 1
    assert not shared.exists()


@pytest.mark.parametrize("flag", ["--out", "--summary-out", "--status-out"])
def test_reduce_output_flags_are_guarded_too(tmp_path, monkeypatch, flag, capsys):
    shared = tmp_path / "shared"
    monkeypatch.setenv("ROOSYNC_SHARED_PATH", str(shared))
    events = tmp_path / "events.json"
    events.write_text(json.dumps(journal(dl.ISSUE_DEBT, [issue_obs(state_class="closed")])),
                      encoding="utf-8")
    exit_code = dl.main([
        "reduce", "--ledger", dl.ISSUE_DEBT, "--events", str(events),
        "--state-dir", str(tmp_path / "state"), flag, str(shared / "out"), FROZEN,
    ])
    assert exit_code == 1
    assert "SHARED_PATH_REFUSED" in capsys.readouterr().err
    assert not shared.exists()


def test_atomic_text_write_leaves_no_temp_behind(tmp_path):
    target = tmp_path / "nested" / "snapshot.json"
    dl.write_json_atomic(target, {"a": 1})
    assert json.loads(target.read_text(encoding="utf-8")) == {"a": 1}
    assert list(target.parent.glob(".*tmp")) == []
    assert list(target.parent.iterdir()) == [target]


def test_lock_refuses_a_second_reducer_and_recovers_after_release(tmp_path):
    lock_path = tmp_path / ".reduce.lock"
    with dl.LedgerLock(lock_path, timeout=0.05, poll=0.01):
        assert lock_path.exists()
        with pytest.raises(dl.LedgerError) as excinfo:
            with dl.LedgerLock(lock_path, timeout=0.05, poll=0.01, stale_after=600):
                pass  # pragma: no cover - the lock must not be granted
        assert excinfo.value.reason == "LOCK_TIMEOUT"
    assert not lock_path.exists()
    with dl.LedgerLock(lock_path, timeout=0.5, poll=0.01):
        pass


def test_a_stale_lock_is_reclaimed(tmp_path):
    lock_path = tmp_path / ".reduce.lock"
    lock_path.write_text("{}", encoding="utf-8")
    old = datetime(2026, 9, 1, tzinfo=timezone.utc).timestamp()
    import os

    os.utime(lock_path, (old, old))
    with dl.LedgerLock(lock_path, timeout=1.0, poll=0.01, stale_after=60):
        pass
    assert not lock_path.exists()


# --- CLI ---------------------------------------------------------------------


def test_cli_append_prints_the_mcp_call_and_writes_nothing_by_default(tmp_path, capsys):
    exit_code = dl.main([
        "append", "--ledger", dl.ISSUE_DEBT, "--entity", "jsboige/CoursIA#15545",
        "--actor", "myia-po-2025:CoursIA-2", "--observed-at", "2026-09-17T19:00:00Z",
        "--evidence", "gh issue view 15545", "--confidence", "high",
        "--fields-json", json.dumps({"state_class": "open-blocked", "eat_hours": 4.0}),
        "--state-dir", str(tmp_path),
    ])
    captured = capsys.readouterr()
    assert exit_code == 0
    envelope = json.loads(captured.out.splitlines()[0].removeprefix(dl.ENVELOPE_PREFIX).strip())
    assert envelope["ledger"] == dl.ISSUE_DEBT
    assert envelope["fields"] == {"state_class": "open-blocked", "eat_hours": 4.0}
    assert "CoursIA-issue-debt-ledger" in captured.err
    assert list(tmp_path.iterdir()) == []


def test_cli_window_full_wraps_a_list_export(tmp_path):
    """A bare list is the natural hand-made export; the flag must cover it."""
    observation = dl.parse_observation(issue_obs(state_class="open-blocked"), dl.ISSUE_DEBT)
    events = tmp_path / "events.json"
    events.write_text(json.dumps([
        {"messageId": "m1", "author": "ai-01", "createdAt": "2026-09-17T19:00:00Z",
         "content": dl.envelope_line(observation)},
    ]), encoding="utf-8")
    state_dir = tmp_path / "state"
    assert dl.main(["reduce", "--ledger", dl.ISSUE_DEBT, "--events", str(events),
                    "--state-dir", str(state_dir), FROZEN]) == 1
    assert dl.main(["reduce", "--ledger", dl.ISSUE_DEBT, "--events", str(events),
                    "--state-dir", str(state_dir), "--window-full", FROZEN]) == 0
    snapshot = json.loads(
        (state_dir / dl.ISSUE_DEBT / "snapshots" / "snapshot.json").read_text(encoding="utf-8")
    )
    assert snapshot["checkpoint"]["window"]["kind"] == "full"
    assert snapshot["rows"][0]["fields"]["state_class"] == "open-blocked"


def test_cli_window_full_does_not_override_an_explicit_declaration(tmp_path):
    events = tmp_path / "events.json"
    events.write_text(json.dumps(journal(dl.ISSUE_DEBT, [issue_obs(state_class="closed")],
                                         kind="incremental")), encoding="utf-8")
    state_dir = tmp_path / "state"
    # An export that SAYS it is a tail is still a tail: the flag is for the
    # exports that say nothing, never a way to talk the reducer out of a fact.
    assert dl.main(["reduce", "--ledger", dl.ISSUE_DEBT, "--events", str(events),
                    "--state-dir", str(state_dir), "--window-full", FROZEN]) == 1


def test_cli_window_full_does_not_shadow_a_nested_incremental_window(tmp_path):
    """The producer may wrap coverage under data; the override must see it."""
    observation = dl.parse_observation(issue_obs(state_class="closed"), dl.ISSUE_DEBT)
    events = tmp_path / "events.json"
    events.write_text(json.dumps({
        "success": True,
        "data": {
            "window": {"kind": "incremental", "archives": ["archive-1"]},
            "intercom": {"messages": [{
                "id": "m1",
                "timestamp": "2026-09-17T19:00:00Z",
                "author": {"machineId": "myia-ai-01", "workspace": "CoursIA"},
                "content": dl.envelope_line(observation),
            }]},
        },
    }), encoding="utf-8")
    state_dir = tmp_path / "state"
    assert dl.main(["reduce", "--ledger", dl.ISSUE_DEBT, "--events", str(events),
                    "--state-dir", str(state_dir), "--window-full", FROZEN]) == 1
    assert not (state_dir / dl.ISSUE_DEBT / "snapshots" / "snapshot.json").exists()


def test_parser_refuses_unknown_window_kind_and_invalid_archives():
    base = journal(dl.ISSUE_DEBT, [issue_obs(state_class="closed")])
    base["window"] = {"kind": "mystery", "archives": []}
    with pytest.raises(dl.LedgerError, match="UNSUPPORTED_WINDOW_KIND"):
        dl.parse_journal_export(base, dl.ISSUE_DEBT)
    base["window"] = {"kind": "full", "archives": "not-a-list"}
    with pytest.raises(dl.LedgerError, match="UNSUPPORTED_WINDOW_KIND"):
        dl.parse_journal_export(base, dl.ISSUE_DEBT)


def test_stray_deep_window_is_not_a_coverage_declaration():
    """A stray ``window`` nested past ``data`` (e.g. UI pagination state) is not
    the producer's coverage declaration. Reading it (key-by-key walk) would
    treat a condensed tail as a FULL export and rebuild state from a fragment;
    the documented paths are the root and ``data`` only."""
    observation = dl.parse_observation(issue_obs(state_class="closed"), dl.ISSUE_DEBT)
    stray = journal(dl.ISSUE_DEBT, [observation])
    del stray["window"]
    stray["data"] = {
        "intercom": {
            "messages": [],
            # deep stray: pagination metadata that merely shares the key name
            "window": {"kind": "full", "archives": []},
        },
    }
    window, records, rejections = dl.parse_journal_export(stray, dl.ISSUE_DEBT)
    assert window["kind"] == "incremental"  # no declaration read: fail-closed tail
    assert window["archives"] == []
    assert len(records) == 1 and rejections == []  # root journal still parsed


def test_stray_deep_format_is_ignored_but_a_declared_format_is_enforced():
    observation = dl.parse_observation(issue_obs(state_class="closed"), dl.ISSUE_DEBT)
    base = journal(dl.ISSUE_DEBT, [observation])
    base["data"] = {"intercom": {"messages": [], "format": "yaml"}}
    window, _, _ = dl.parse_journal_export(base, dl.ISSUE_DEBT)  # stray ignored
    assert window["kind"] == base["window"]["kind"]
    declared = journal(dl.ISSUE_DEBT, [observation])
    declared["data"] = {"format": "yaml"}  # DOCUMENTED path: enforced
    with pytest.raises(dl.LedgerError, match="UNSUPPORTED_EXPORT_FORMAT"):
        dl.parse_journal_export(declared, dl.ISSUE_DEBT)


def test_cli_pr_actions_requires_head_sha(tmp_path, capsys):
    assert dl.main([
        "append", "--ledger", dl.PR_ACTIONS, "--entity", "jsboige/CoursIA#16001",
        "--actor", "ai-01", "--evidence", "gh pr view 16001",
        "--fields-json", json.dumps({"action_class": "review-ready"}),
        "--state-dir", str(tmp_path),
    ]) == 1
    assert "MISSING_INPUT" in capsys.readouterr().err


def test_cli_malformed_fields_json_is_a_controlled_error(tmp_path, capsys):
    for bad in ("{not json", "[1, 2]", '"a string"'):
        exit_code = dl.main([
            "append", "--ledger", dl.ISSUE_DEBT, "--entity", "jsboige/CoursIA#1",
            "--actor", "ai-01", "--evidence", "e", "--fields-json", bad,
            "--state-dir", str(tmp_path),
        ])
        assert exit_code == 1
        assert "INVALID_JSON" in capsys.readouterr().err


def test_cli_append_json_descriptor_and_spool_out_dir(tmp_path, capsys):
    exit_code = dl.main([
        "append", "--ledger", dl.PR_ACTIONS, "--entity", "jsboige/CoursIA#16001",
        "--head-sha", HEAD_A, "--actor", "myia-po-2025:CoursIA-2",
        "--observed-at", "2026-09-17T19:00:00Z", "--evidence", "gh pr view 16001",
        "--fields-json", json.dumps({"action_class": "review-ready", "review_required": True}),
        "--json", "--out-dir", str(tmp_path / "spool"),
    ])
    captured = capsys.readouterr()
    assert exit_code == 0
    descriptor = json.loads(captured.out)
    assert descriptor["workspace"] == "CoursIA-pr-action-ledger"
    assert descriptor["mcp_call"].startswith('roosync_dashboard(action:"append"')
    spooled = list((tmp_path / "spool").glob("*.json"))
    assert len(spooled) == 1
    assert json.loads(spooled[0].read_text(encoding="utf-8").removeprefix(dl.ENVELOPE_PREFIX))[
        "observation_id"
    ] == descriptor["observation_id"]


def test_cli_reduce_writes_snapshot_summary_and_status(tmp_path, capsys):
    events = tmp_path / "events.json"
    events.write_text(
        json.dumps(journal(dl.ISSUE_DEBT, [
            issue_obs(issue=1, state_class="open-blocked", eat_hours=4.0,
                      closeability="closeable-after-followup",
                      followup={"kind": "issue", "repo": "jsboige/CoursIA", "number": 16100}),
            issue_obs(issue=2, state_class="closed"),
        ])),
        encoding="utf-8",
    )
    state_dir = tmp_path / "state"
    assert dl.main(["init", "--state-dir", str(state_dir), "--apply", FROZEN]) == 0
    assert dl.main(["reduce", "--ledger", dl.ISSUE_DEBT, "--events", str(events),
                    "--state-dir", str(state_dir), FROZEN]) == 0
    snapshots = state_dir / dl.ISSUE_DEBT / "snapshots"
    snapshot = json.loads((snapshots / "snapshot.json").read_text(encoding="utf-8"))
    summary = json.loads((snapshots / "summary.json").read_text(encoding="utf-8"))
    status = (snapshots / "status.md").read_text(encoding="utf-8")
    assert snapshot["schema"] == dl.SNAPSHOT_SCHEMA
    assert snapshot["workspace"] == "CoursIA-issue-debt-ledger"
    assert snapshot["checkpoint"]["events"]["consumed_total"] == 2
    assert summary["eat_hours"]["total"] == 4.0
    assert summary["followups"]["issue"] == 1
    assert status.startswith("[LEDGER] issue-debt")
    assert "WROTE 2 row(s)" in capsys.readouterr().out

    # A second cycle re-reads the snapshot as its checkpoint (auto-detected).
    assert dl.main(["reduce", "--ledger", dl.ISSUE_DEBT, "--events", str(events),
                    "--state-dir", str(state_dir), FROZEN]) == 0
    again = json.loads((snapshots / "snapshot.json").read_text(encoding="utf-8"))
    assert again["rows"] == snapshot["rows"]
    assert again["checkpoint"]["events"]["replayed"] == 2


def test_cli_reduce_dry_run_writes_nothing(tmp_path):
    events = tmp_path / "events.json"
    events.write_text(json.dumps(journal(dl.PR_ACTIONS, [pr_obs(live_reserves=["r"])])),
                      encoding="utf-8")
    state_dir = tmp_path / "state"
    assert dl.main(["reduce", "--ledger", dl.PR_ACTIONS, "--events", str(events),
                    "--state-dir", str(state_dir), "--dry-run", FROZEN]) == 0
    assert not state_dir.exists()


def test_cli_reduce_fail_on_rejections(tmp_path):
    # Built by hand, not through `journal()`: the helper validates, and the whole
    # point of this case is an observation the reducer must REFUSE.
    bad = dict(issue_obs(state_class="not-a-state"))
    events = tmp_path / "events.json"
    events.write_text(
        json.dumps({
            "schema": dl.EXPORT_SCHEMA,
            "ledger": dl.ISSUE_DEBT,
            "window": {"kind": "full"},
            "messages": [{"messageId": "m", "author": "ai-01",
                          "createdAt": "2026-09-17T19:00:00Z",
                          "content": dl.canonical_json(bad)}],
        }),
        encoding="utf-8",
    )
    state_dir = tmp_path / "state"
    assert dl.main(["reduce", "--ledger", dl.ISSUE_DEBT, "--events", str(events),
                    "--state-dir", str(state_dir), "--fail-on-rejections", FROZEN]) == 1
    assert dl.main(["reduce", "--ledger", dl.ISSUE_DEBT, "--events", str(events),
                    "--state-dir", str(state_dir), FROZEN]) == 0


def test_cli_reduce_without_events_on_an_incremental_journal_is_a_fatal_error(tmp_path, capsys):
    exit_code = dl.main(["reduce", "--ledger", dl.ISSUE_DEBT, "--state-dir", str(tmp_path)])
    assert exit_code == 1
    assert "MISSING_INPUT" in capsys.readouterr().err


def test_cli_window_full_allows_a_cold_start(tmp_path):
    """Bootstrap: the very first reduce declares the export complete on purpose."""
    export = journal(dl.ISSUE_DEBT, [issue_obs(state_class="open-blocked")])
    del export["window"]
    events = tmp_path / "events.json"
    events.write_text(json.dumps(export), encoding="utf-8")
    assert dl.main(["reduce", "--ledger", dl.ISSUE_DEBT, "--events", str(events),
                    "--state-dir", str(tmp_path / "state"), FROZEN]) == 1
    assert dl.main(["reduce", "--ledger", dl.ISSUE_DEBT, "--events", str(events),
                    "--state-dir", str(tmp_path / "state"), "--window-full", FROZEN]) == 0
    snapshot = json.loads(
        (tmp_path / "state" / dl.ISSUE_DEBT / "snapshots" / "snapshot.json").read_text(
            encoding="utf-8"
        )
    )
    assert snapshot["checkpoint"]["window"]["kind"] == "full"


def test_cli_reduce_stdout_writes_nothing(tmp_path, capsys):
    events = tmp_path / "events.json"
    events.write_text(json.dumps(journal(dl.ISSUE_DEBT, [issue_obs(state_class="closed")])),
                      encoding="utf-8")
    assert dl.main(["reduce", "--ledger", dl.ISSUE_DEBT, "--events", str(events),
                    "--state-dir", str(tmp_path / "state"), "--stdout", FROZEN]) == 0
    captured = capsys.readouterr()
    assert json.loads(captured.out.split("[LEDGER]")[0])["ledger"] == dl.ISSUE_DEBT
    assert not (tmp_path / "state").exists()


def test_cli_append_from_observation_file(tmp_path, capsys):
    observation = dl.parse_observation(
        issue_obs(state_class="open-actionable", eat_hours=1.0), dl.ISSUE_DEBT
    )
    path = tmp_path / "obs.json"
    path.write_text(json.dumps(observation), encoding="utf-8")
    assert dl.main(["append", "--ledger", dl.ISSUE_DEBT, "--observation-file", str(path),
                    "--state-dir", str(tmp_path / "state")]) == 0
    line = capsys.readouterr().out.splitlines()[0]
    assert json.loads(line.removeprefix(dl.ENVELOPE_PREFIX))["observation_id"] == (
        observation["observation_id"]
    )
