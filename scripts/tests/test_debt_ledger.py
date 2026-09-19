#!/usr/bin/env python3
#!/usr/bin/env python3
"""Tests for ``scripts/coordination/debt_ledger.py`` -- the shared issue-debt ledger.

The ledger is an append-only journal carried by a DEDICATED RooSync workspace
dashboard; the reducer is the only place where the journal is folded into state,
and it must be trustworthy on four properties that are each a real fleet failure
mode:

  * two lanes observing the same entity at the same instant never clobber each
    other (distinct observations survive, the merge is deterministic);
  * a re-append of the same observation is a no-op, and a re-fold of the same
    journal yields the same state (idempotency, not "mostly idempotent");
  * a malformed observation is REJECTED with its reason rather than silently
    merged into a phantom field;
  * the summary carries the EAT (issue debt) metrics the cycle decides on, and
    follow-ups are tracked as named issues or explicit waivers.

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


def journal(ledger: str, observations) -> dict:
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
    """The state that must survive a re-fold: each row's values and verdict."""
    snapshot = getattr(snapshot, "snapshot", snapshot)
    return {
        row["key"]: (row["fields"], row["historical"]) for row in snapshot["rows"]
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


# --- archive-aware checkpoint contract ---------------------------------------


def test_replayed_observation_is_counted():
    observation = issue_obs(state_class="open-blocked")
    first = reduce_it(dl.ISSUE_DEBT, [observation])
    second = dl.reduce_ledger(
        ledger=dl.ISSUE_DEBT,
        export=journal(dl.ISSUE_DEBT, [observation]),
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
        (dict(issue_obs(state_class="open-blocked"), ledger="release-notes"), "ledger_mismatch"),
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
    export["ledger"] = "release-notes"
    with pytest.raises(dl.LedgerError) as excinfo:
        dl.reduce_ledger(ledger=dl.ISSUE_DEBT, export=export, now=NOW)
    assert excinfo.value.reason == "EXPORT_LEDGER_MISMATCH"


def test_a_corrupt_config_degrades_to_the_compiled_in_workspace():
    """The dashboard a ledger lives on is a fact of the code, not of the file."""
    result = dl.reduce_ledger(
        ledger=dl.ISSUE_DEBT,
        export=journal(dl.ISSUE_DEBT, [issue_obs(state_class="open-blocked")]),
        now=NOW,
        config={"ledgers": {dl.ISSUE_DEBT: "not-an-object"}},
    )
    assert result.snapshot["workspace"] == "CoursIA-issue-debt-ledger"
    assert result.summary["workspace"] == "CoursIA-issue-debt-ledger"


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


def test_unknown_ledger_is_refused():
    with pytest.raises(dl.LedgerError) as excinfo:
        dl.reduce_ledger(ledger="release-notes", export=[], now=NOW)
    assert excinfo.value.reason == "UNKNOWN_LEDGER"


# --- terminal rows stay historical -------------------------------------------


def test_closed_rows_remain_historical():
    """A closed issue stops being live debt but never leaves the ledger."""
    snapshot = reduce_it(
        dl.ISSUE_DEBT,
        [
            issue_obs(issue=1, state_class="closed"),
            issue_obs(issue=2, state_class="open-blocked"),
        ],
    )
    rows = {row["key"]: row for row in snapshot.snapshot["rows"]}
    assert rows["jsboige/CoursIA#1"]["historical"] is True
    assert rows["jsboige/CoursIA#2"]["historical"] is False
    assert snapshot.snapshot["counts"]["historical"] == 1
    assert snapshot.summary["state_class"] == {"open-blocked": 1}


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
        "ledger": "release-notes",
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
        export=journal(dl.ISSUE_DEBT, [issue_obs(issue=1, state_class="closed")]),
        prior_snapshot=corrupt,
        now=NOW,
    )
    row = row_of(result, "jsboige/CoursIA#1")
    assert row["fields"]["state_class"] == "closed"


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


def test_status_text_is_bounded_by_status_max_rows():
    observations = [
        issue_obs(issue=100 + index, state_class="open-actionable", eat_hours=float(index))
        for index in range(30)
    ]
    snapshot = reduce_it(dl.ISSUE_DEBT, observations, config={"status_max_rows": 5})
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

    doc = json.loads((tmp_path / dl.ISSUE_DEBT / "schema.json").read_text(encoding="utf-8"))
    assert doc["schema"] == dl.SCHEMA_DOC_VERSION
    assert doc["transport"]["envelope_prefix"] == dl.ENVELOPE_PREFIX
    names = [entry["name"] for entry in doc["ledgers"][dl.ISSUE_DEBT]["fields"]]
    assert names == ["state_class", "closeability", "remaining_atomic_prs", "eat_hours",
                     "dependencies", "followup"]
    assert doc["dashboard_calls"]["append_observation"].startswith("roosync_dashboard(action:\"append\"")
    baseline = json.loads((tmp_path / dl.ISSUE_DEBT / "baseline.json").read_text(encoding="utf-8"))
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
        "append", "--ledger", dl.ISSUE_DEBT, "--entity", "jsboige/CoursIA#16001",
        "--actor", "myia-po-2025:CoursIA-2",
        "--observed-at", "2026-09-17T19:00:00Z", "--evidence", "gh issue view 16001",
        "--fields-json", json.dumps({"state_class": "open-actionable", "eat_hours": 3.0}),
        "--json", "--out-dir", str(tmp_path / "spool"),
    ])
    captured = capsys.readouterr()
    assert exit_code == 0
    descriptor = json.loads(captured.out)
    assert descriptor["workspace"] == "CoursIA-issue-debt-ledger"
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
    events.write_text(json.dumps(journal(dl.ISSUE_DEBT, [issue_obs(state_class="open-blocked")])),
                      encoding="utf-8")
    state_dir = tmp_path / "state"
    assert dl.main(["reduce", "--ledger", dl.ISSUE_DEBT, "--events", str(events),
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
