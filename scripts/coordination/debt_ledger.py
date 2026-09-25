#!/usr/bin/env python3
r"""debt_ledger.py -- the shared debt ledgers (local artifact half).

Two kinds share this machinery: ``issue-debt`` (one row per issue, keyed
``owner/repo#N``) and ``gpu-reservation`` (one row per device hold, keyed
``<machine>#gpu<n>``, #16737). A kind declares its entity, its fields and its
terminal value; everything below is per-kind dispatch over those declarations.

WHY
===

The fleet keeps a ledger that was, until now, re-derived from scratch every
cycle by reading dashboards, inboxes and GitHub: the ISSUES that owe work
("issue debt"). Re-deriving is what makes a 4 h cadence expensive -- every cycle
re-reads the issue's surfaces and re-learns what the previous cycle already
knew -- and nothing survives a session boundary except prose.

This module is the UTILITY half of that fix: schemas, reducer, CLI, tests. It
knows nothing about GitHub and nothing about RooSync, and it never writes to the
shared filesystem.

TRANSPORT -- read this before wiring anything
=============================================

The SHARED transport is NOT a shared file. ``$ROOSYNC_SHARED_PATH`` is a Drive
mount: no locking, no compare-and-swap, so two lanes writing the same file is
last-write-wins -- a multi-writer ledger there would silently LOSE observations,
which is the exact class of loss the ledger exists to prevent.

The transport is a DEDICATED RooSync workspace dashboard, one per ledger kind
(``LEDGER_WORKSPACES``): ``CoursIA-issue-debt-ledger`` for ``issue-debt``.

Each OBSERVATION is one append-only dashboard message: ``content`` is a one-line
JSON envelope, ``[OBS] {...}``. Messages are never edited, so the journal is
append-only by construction; a stable ``observation_id`` (content-derived, see
``observation_id_for``) makes a replay detectable instead of harmful.

The SNAPSHOT is written by ai-01 ALONE, into the ``status`` section of that
dedicated dashboard, through the dashboard ``update``/``replace`` action -- never
by a second writer, and never as an append (a snapshot is a derived value, not an
event). Reducers other than ai-01 produce snapshots locally for review.

WHAT LANDS ON DISK (local artifacts only)
=========================================

Never in the repo, never under ``$ROOSYNC_SHARED_PATH``: ``assert_local_output``
refuses BOTH for every path this tool writes -- the state directory and each of
``--out``/``--out-dir``/``--summary-out``/``--status-out``, no override. Ledger
state is not repo content, and a Drive mount has no locking.

  <state>/config.json                      tunables + ledger->workspace map
  <state>/<ledger>/baseline.json           human-authored seed observations
  <state>/<ledger>/schema.json             generated contract, from this code
  <state>/<ledger>/spool/<obs_id>.json     local outbox of envelopes to post
  <state>/<ledger>/snapshots/snapshot.json
  <state>/<ledger>/snapshots/summary.json
  <state>/<ledger>/snapshots/status.md     compact text ai-01 posts in `status`

REDUCE
======

``reduce`` folds three sources. There is no source precedence: every source
contributes OBSERVATIONS and the merge rule is per field -- the newest
compatible observation wins, provenance and history are preserved.

  1. the baseline (seed observations, supersedable like any other);
  2. the PRIOR SNAPSHOT, folded field by field with each field's original
     provenance -- this is what makes the reducer ARCHIVE-AWARE: when the
     dashboard condenses and rotates old messages into archives, the state those
     messages carried is already folded, so nothing is re-derived and nothing is
     lost;
  3. the exported journal (``roosync_dashboard read`` output) with its ``window``
     declaration.

The export is read in the PRODUCER'S shape, not in a shape invented here: a
RooSync read nests the journal (``data.intercom.messages``) and its messages are
``{id, timestamp, author: {machineId, workspace}, content}`` -- the machine key is
``machineId``, and the adapter normalises it into a ``machineId:workspace`` lane
(``machine_id``/``machine``/``host`` are accepted as fallbacks). Dashboard prose
(an ai-01 status snapshot, a human note) is IGNORED and counted -- only content
that declares itself an observation (``[OBS]``) and then fails to parse is a
rejection.

ARCHIVE-AWARE CHECKPOINT CONTRACT
=================================

An export DECLARES what it covers::

    {"window": {"kind": "full" | "incremental", "archives": [...]}}

  * ``full``        -- the export claims to contain the whole journal; a prior
                       snapshot is optional.
  * ``incremental`` -- a tail export (the normal case once the dashboard has
                       condensed); THE PRIOR SNAPSHOT IS MANDATORY.
  * absent          -- treated as ``incremental``. Fail-closed: an export that
                       does not say what it covers is not trusted to rebuild
                       state from nothing.

Folding an incremental export without a checkpoint raises ``MISSING_CHECKPOINT``
rather than quietly emitting a snapshot built from the tail alone. An export
OLDER than the checkpoint is not fatal (its observations lose on ``observed_at``)
but it is surfaced as a warning -- a stale export must never regress state.

CLI
===

::

    python scripts/coordination/debt_ledger.py init   [--apply]
    python scripts/coordination/debt_ledger.py append --ledger issue-debt ...
    python scripts/coordination/debt_ledger.py init   [--apply]
    python scripts/coordination/debt_ledger.py append --ledger issue-debt ...
    python scripts/coordination/debt_ledger.py append --ledger gpu-reservation --entity 'po-2023#gpu1' ...
    python scripts/coordination/debt_ledger.py reduce --ledger issue-debt --events export.json

Dry-run defaults: ``init`` writes nothing without ``--apply`` (it creates state,
so it is opt-in); ``append`` prints the envelope and writes nothing unless
``--out``/``--out-dir`` is given -- it cannot write shared state at all, posting
is the agent's MCP call; ``reduce`` writes its three artifacts unless
``--dry-run``/``--stdout``.

Exit codes: 0 ok · 1 fatal · 2 usage.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import tempfile
import time
from dataclasses import dataclass, field as dataclass_field
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Iterable, Sequence

# ---------------------------------------------------------------------------
# 1. CONTRACT -- schemas, ledgers, vocabulary
# ---------------------------------------------------------------------------

OBSERVATION_SCHEMA = "debt-ledger-observation/v1"
EXPORT_SCHEMA = "debt-ledger-journal-export/v1"
SNAPSHOT_SCHEMA = "debt-ledger-snapshot/v1"
SUMMARY_SCHEMA = "debt-ledger-summary/v1"
CHECKPOINT_SCHEMA = "debt-ledger-checkpoint/v1"
BASELINE_SCHEMA = "debt-ledger-baseline/v1"
CONFIG_SCHEMA = "debt-ledger-config/v1"
SCHEMA_DOC_VERSION = "debt-ledger-schema/v1"

ISSUE_DEBT = "issue-debt"
GPU_RESERVATION = "gpu-reservation"
LEDGERS: tuple[str, ...] = (ISSUE_DEBT, GPU_RESERVATION)

#: The DEDICATED dashboards. One per ledger kind: a ledger never shares a
#: dashboard with another kind, so a condensation of one never truncates the
#: other's journal.
LEDGER_WORKSPACES: dict[str, str] = {
    ISSUE_DEBT: "CoursIA-issue-debt-ledger",
    GPU_RESERVATION: "CoursIA-gpu-reservation-ledger",
}

#: Tag prefix of a one-line observation envelope posted as dashboard content.
ENVELOPE_PREFIX = "[OBS]"

#: Encoding of that envelope. Declared by the producer (``append --json``) and
#: enforced by the reducer (``UNSUPPORTED_EXPORT_FORMAT``) so a future encoding
#: cannot be silently misread as this one.
ENVELOPE_FORMAT = "json"

CONFIDENCE_LEVELS: tuple[str, ...] = ("low", "medium", "high")

STATE_CLASSES: tuple[str, ...] = (
    "open-actionable",
    "open-blocked",
    "open-stale",
    "deferred",
    "closed",
    "unknown",
)
CLOSEABILITY_VALUES: tuple[str, ...] = (
    "closeable-now",
    "closeable-after-followup",
    "not-closeable",
    "unknown",
)
DEPENDENCY_KINDS: tuple[str, ...] = ("issue", "pr", "external")
FOLLOWUP_KINDS: tuple[str, ...] = ("issue", "waiver", "none")

TERMINAL_ISSUE_STATE: frozenset[str] = frozenset({"closed"})

#: Entity fields per ledger. ``repo`` is always the first component of the key.
ENTITY_FIELDS: dict[str, tuple[str, ...]] = {
    ISSUE_DEBT: ("repo", "issue"),
    GPU_RESERVATION: ("machine", "gpu_index"),
}

_REPO_RE = re.compile(r"^[\w.-]+/[\w.-]+$")
_MACHINE_RE = re.compile(r"^[A-Za-z0-9._-]+$")
_ACTOR_RE = re.compile(r"^[A-Za-z0-9._-]+(:[A-Za-z0-9._-]+)?$")
_ISSUE_REF_RE = re.compile(r"^[\w.-]+/[\w.-]+#\d+$")


@dataclass(frozen=True)
class FieldSpec:
    """One field of one ledger's row.

    ``kind`` selects both the validator and the normalisation applied before the
    observation id is computed (so a re-append of the same raw file is
    byte-identical, see ``canonical_json``).
    """

    name: str
    kind: str
    values: tuple[str, ...] = ()
    description: str = ""


ISSUE_DEBT_FIELDS: tuple[FieldSpec, ...] = (
    FieldSpec(
        "state_class",
        "enum",
        values=STATE_CLASSES,
        description="What the issue is doing right now; 'closed' is terminal.",
    ),
    FieldSpec(
        "closeability",
        "enum",
        values=CLOSEABILITY_VALUES,
        description="Whether the issue can be closed as-is, after a follow-up, or not.",
    ),
    FieldSpec(
        "remaining_atomic_prs",
        "int",
        description="Remaining atomic PRs before the issue is genuinely done.",
    ),
    FieldSpec(
        "eat_hours",
        "hours",
        description="Estimated atomic-task hours still owed (EAT).",
    ),
    FieldSpec(
        "dependencies",
        "dependencies",
        description="Issues/PRs/external items this issue waits on.",
    ),
    FieldSpec(
        "followup",
        "followup",
        description="Named follow-up issue carrying real residuals, or a waiver.",
    ),
)


GPU_RESERVATION_STATES: tuple[str, ...] = ("held", "released", "stale")

GPU_RESERVATION_FIELDS: tuple[FieldSpec, ...] = (
    FieldSpec(
        "state",
        "enum",
        values=GPU_RESERVATION_STATES,
        description="'held' while the workload runs, 'released' when it ends; released is terminal.",
    ),
    FieldSpec(
        "holder",
        "lane",
        description="The lane holding the device ('machine:workspace').",
    ),
    FieldSpec(
        "workload",
        "text",
        description="What is running on the device, in one line.",
    ),
    FieldSpec(
        "started_at",
        "utc-timestamp",
        description="When the hold began (UTC ISO-8601, normalised).",
    ),
    FieldSpec(
        "expected_end",
        "utc-timestamp",
        description="When the hold is expected to end; the basis for a stale-hold sweep.",
    ),
    FieldSpec(
        "issue",
        "issue-ref",
        description="The execution issue this hold serves ('owner/repo#N'), when one exists.",
    ),
)

LEDGER_FIELD_SPECS: dict[str, dict[str, FieldSpec]] = {
    ISSUE_DEBT: {spec.name: spec for spec in ISSUE_DEBT_FIELDS},
    GPU_RESERVATION: {spec.name: spec for spec in GPU_RESERVATION_FIELDS},
}

#: Terminal values, per ledger, keyed by the field that carries the verdict.
TERMINAL_VALUES: dict[str, tuple[str, str]] = {
    ISSUE_DEBT: ("state_class", "closed"),
    GPU_RESERVATION: ("state", "released"),
}
TERMINAL_SETS: dict[str, frozenset[str]] = {
    ISSUE_DEBT: TERMINAL_ISSUE_STATE,
    GPU_RESERVATION: frozenset({"released"}),
}

#: Top-level keys allowed in an observation envelope. Anything else is a
#: rejection (``unknown_key``): a typo that silently creates a phantom field is
#: worse than a loud refusal, because a phantom field never merges with the real
#: one and two lanes then read two different truths.
OBSERVATION_KEYS: frozenset[str] = frozenset(
    {
        "schema",
        "observation_id",
        "ledger",
        "actor",
        "observed_at",
        "confidence",
        "evidence",
        "entity",
        "head_transition",
        "fields",
        "message_id",
        "note",
    }
)

DEFAULT_CONFIG: dict[str, Any] = {
    "schema": CONFIG_SCHEMA,
    "ledgers": {
        kind: {"workspace": workspace, "snapshot_section": "status"}
        for kind, workspace in LEDGER_WORKSPACES.items()
    },
    "history_max_entries_per_field": 25,
    "observation_ids_recent_max": 200,
    "status_max_rows": 12,
    "stale_observation_hours": 72,
    "max_clock_skew_minutes": 15,
}

# ---------------------------------------------------------------------------
# 2. ERRORS
# ---------------------------------------------------------------------------


class LedgerError(Exception):
    """Fatal, non-recoverable: nothing is written and the CLI exits 1."""

    def __init__(self, reason: str, detail: str = "") -> None:
        self.reason = reason
        self.detail = detail
        super().__init__(f"{reason}: {detail}" if detail else reason)


class ObservationError(Exception):
    """One observation refused; the rest of the ledger still reduces."""

    def __init__(self, reason: str, detail: str = "") -> None:
        self.reason = reason
        self.detail = detail
        super().__init__(f"{reason}: {detail}" if detail else reason)


# ---------------------------------------------------------------------------
# 3. TIME -- UTC or nothing
# ---------------------------------------------------------------------------

_TS_RE = re.compile(
    r"^(?P<date>\d{4}-\d{2}-\d{2})[Tt ](?P<time>\d{2}:\d{2}:\d{2})"
    r"(?P<frac>\.\d+)?(?P<off>Z|z|[+-]\d{2}:?\d{2})$"
)
_NAIVE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}[Tt ]\d{2}:\d{2}:\d{2}(\.\d+)?$")


def parse_utc_timestamp(raw: Any, *, where: str = "observed_at") -> datetime:
    """Parse an explicit-UTC ISO-8601 stamp, or refuse it.

    A NAIVE stamp is refused (``naive_timestamp``) because local time read as UTC
    is indistinguishable from UTC and silently reorders the merge -- the trap
    that inverted the cross-lane claim order of #9764. A non-UTC OFFSET is
    refused too (``non_utc_timestamp``): the ledger stores one clock, UTC.
    """
    if not isinstance(raw, str) or not raw.strip():
        raise ObservationError("invalid_timestamp", f"{where} must be a non-empty string")
    text = raw.strip()
    match = _TS_RE.match(text)
    if match is None:
        if _NAIVE_RE.match(text):
            raise ObservationError(
                "naive_timestamp",
                f"{where}={text!r} has no UTC offset; write UTC with a 'Z' suffix",
            )
        raise ObservationError(
            "invalid_timestamp", f"{where}={text!r} is not ISO-8601 with an offset"
        )
    offset = match.group("off")
    if offset not in ("Z", "z", "+00:00", "+0000", "-00:00", "-0000"):
        raise ObservationError(
            "non_utc_timestamp",
            f"{where}={text!r} carries offset {offset!r}; the ledger clock is UTC",
        )
    fraction = match.group("frac") or ""
    microsecond = int((fraction[1:] + "000000")[:6]) if fraction else 0
    try:
        parsed = datetime.strptime(
            f"{match.group('date')}T{match.group('time')}", "%Y-%m-%dT%H:%M:%S"
        )
    except ValueError as exc:  # pragma: no cover - regex already constrains shape
        raise ObservationError("invalid_timestamp", f"{where}={text!r} ({exc})") from exc
    return parsed.replace(tzinfo=timezone.utc, microsecond=microsecond)


def format_utc(moment: datetime) -> str:
    """Render an aware datetime as UTC ISO-8601 with a ``Z`` suffix."""
    moment = moment.astimezone(timezone.utc)
    if moment.microsecond:
        return moment.strftime("%Y-%m-%dT%H:%M:%S.%fZ")
    return moment.strftime("%Y-%m-%dT%H:%M:%SZ")


def utcnow() -> datetime:
    return datetime.now(timezone.utc)


# ---------------------------------------------------------------------------
# 4. CANONICAL FORM -- digests and observation identity
# ---------------------------------------------------------------------------


def canonical_json(payload: Any) -> str:
    """Sorted, compact, ASCII-preserving JSON: the digest input, always."""
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def digest_of(payload: Any) -> str:
    return hashlib.sha256(canonical_json(payload).encode("utf-8")).hexdigest()


def observation_id_for(observation: dict[str, Any]) -> str:
    """Content-derived stable id -- the same observation always gets the same id.

    This is what makes an append-only journal replay-safe: a re-post is
    recognisable, and a duplicate is a no-op rather than a second contribution.
    ``observation_id`` and ``message_id`` are excluded from the digest (the
    first is the output, the second is transport metadata).
    """
    body = {
        key: value
        for key, value in observation.items()
        if key not in ("observation_id", "message_id")
    }
    return "obs-" + digest_of(body)[:16]


def envelope_line(observation: dict[str, Any]) -> str:
    """The exact one-line dashboard ``content`` for one observation."""
    return f"{ENVELOPE_PREFIX} {canonical_json(observation)}"


def parse_envelope(text: Any) -> dict[str, Any]:
    """Inverse of ``envelope_line``; tolerant of a missing ``[OBS]`` prefix."""
    if isinstance(text, dict):
        return text
    if not isinstance(text, str):
        raise ObservationError("unparsable_envelope", "content is neither a dict nor a string")
    stripped = text.strip()
    if stripped.startswith(ENVELOPE_PREFIX):
        stripped = stripped[len(ENVELOPE_PREFIX) :].strip()
    if not stripped:
        raise ObservationError("unparsable_envelope", "empty content")
    try:
        decoded = json.loads(stripped)
    except json.JSONDecodeError as exc:
        raise ObservationError("unparsable_envelope", f"content is not JSON ({exc})") from exc
    if not isinstance(decoded, dict):
        raise ObservationError("unparsable_envelope", "content JSON is not an object")
    return decoded


def looks_like_observation(content: Any) -> bool:
    """Is this message content an observation, or dashboard prose?

    The journal dashboard also carries the ai-01 status snapshot and human notes.
    Those are not malformed observations, and counting them as rejections would
    paint a healthy ledger red on every cycle it is read. A message DECLARING
    itself an observation (``[OBS]``) stays a rejection when it fails to parse:
    a producer that lies about its own format is a defect, not chatter.
    """
    if isinstance(content, dict):
        return True
    if not isinstance(content, str):
        return False
    text = content.strip()
    return text.startswith(ENVELOPE_PREFIX) or text.startswith("{")


# ---------------------------------------------------------------------------
# 5. VALIDATION -- normalise, then judge
# ---------------------------------------------------------------------------


def _collapse(text: str) -> str:
    return " ".join(text.split())


def _require_str(value: Any, where: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ObservationError("invalid_field_value", f"{where} must be a non-empty string")
    return _collapse(value)


def _validate_issue_entity(raw: dict[str, Any]) -> dict[str, Any]:
    repo = raw["repo"]
    if not isinstance(repo, str) or not _REPO_RE.match(repo.strip()):
        raise ObservationError("entity_mismatch", f"repo={repo!r} is not 'owner/name'")
    entity: dict[str, Any] = {"repo": repo.strip()}
    number = raw["issue"]
    if isinstance(number, bool) or not isinstance(number, int) or number <= 0:
        raise ObservationError("entity_mismatch", f"issue={number!r} is not a positive int")
    entity["issue"] = number
    return entity


def _validate_gpu_entity(raw: dict[str, Any]) -> dict[str, Any]:
    machine = raw["machine"]
    if not isinstance(machine, str) or not _MACHINE_RE.match(machine.strip()):
        raise ObservationError("entity_mismatch", f"machine={machine!r} is not a machine name")
    # 0-based: a device index is not a number you count from one.
    index = raw["gpu_index"]
    if isinstance(index, bool) or not isinstance(index, int) or index < 0:
        raise ObservationError(
            "entity_mismatch", f"gpu_index={index!r} is not a non-negative int"
        )
    return {"machine": machine.strip(), "gpu_index": index}


#: One entity validator per ledger -- the entity IS the row identity, so a kind
#: without its own validator would validate every row against another kind's shape.
ENTITY_VALIDATORS: dict[str, Any] = {
    ISSUE_DEBT: _validate_issue_entity,
    GPU_RESERVATION: _validate_gpu_entity,
}

#: How the row key reads in the generated schema, per ledger.
ENTITY_KEY_FORMATS: dict[str, str] = {
    ISSUE_DEBT: "owner/repo#N",
    GPU_RESERVATION: "<machine>#gpu<n>",
}


def _validate_entity(raw: Any, ledger: str) -> dict[str, Any]:
    if not isinstance(raw, dict):
        raise ObservationError("entity_mismatch", "entity must be an object")
    expected = set(ENTITY_FIELDS[ledger])
    unknown = sorted(set(raw) - expected)
    missing = sorted(expected - set(raw))
    if unknown:
        raise ObservationError("entity_mismatch", f"unknown entity key(s): {', '.join(unknown)}")
    if missing:
        raise ObservationError("entity_mismatch", f"missing entity key(s): {', '.join(missing)}")
    validator = ENTITY_VALIDATORS.get(ledger)
    if validator is None:  # pragma: no cover - every declared ledger has one
        raise LedgerError("UNKNOWN_ENTITY_KIND", ledger)
    return validator(raw)


def entity_key(entity: dict[str, Any]) -> str:
    """The row identity: ``owner/repo#N``, or ``<machine>#gpu<n>``.

    A head is NOT part of the row key. The dispatch is on the entity's own shape,
    which ``_validate_entity`` has already reduced to exactly one kind's fields.
    """
    if "machine" in entity:
        return f"{entity['machine']}#gpu{entity['gpu_index']}"
    number = entity.get("issue", entity.get("pr"))
    return f"{entity['repo']}#{number}"


def _validate_dependencies(value: Any, entity: dict[str, Any]) -> list[dict[str, Any]]:
    if not isinstance(value, list):
        raise ObservationError("invalid_field_value", "dependencies must be a list")
    out: list[dict[str, Any]] = []
    for index, item in enumerate(value):
        where = f"dependencies[{index}]"
        if isinstance(item, int) and not isinstance(item, bool):
            if item <= 0:
                raise ObservationError("invalid_field_value", f"{where} must be a positive int")
            out.append({"kind": "issue", "repo": entity["repo"], "number": item, "note": None})
            continue
        if not isinstance(item, dict):
            raise ObservationError(
                "invalid_field_value", f"{where} must be an int or an object"
            )
        unknown = sorted(set(item) - {"kind", "repo", "number", "note"})
        if unknown:
            raise ObservationError(
                "invalid_field_value", f"{where} has unknown key(s): {', '.join(unknown)}"
            )
        kind = item.get("kind", "issue")
        if kind not in DEPENDENCY_KINDS:
            raise ObservationError(
                "invalid_field_value",
                f"{where}.kind={kind!r} not in {'/'.join(DEPENDENCY_KINDS)}",
            )
        repo = item.get("repo", entity["repo"])
        if not isinstance(repo, str) or not _REPO_RE.match(repo.strip()):
            raise ObservationError(
                "invalid_field_value", f"{where}.repo={repo!r} is not 'owner/name'"
            )
        number = item.get("number")
        if kind == "external":
            number = None
        elif isinstance(number, bool) or not isinstance(number, int) or number <= 0:
            raise ObservationError(
                "invalid_field_value", f"{where}.number={number!r} is not a positive int"
            )
        note = item.get("note")
        if note is not None:
            note = _require_str(note, f"{where}.note")
        out.append({"kind": kind, "repo": repo.strip(), "number": number, "note": note})
    return out


def _validate_followup(value: Any) -> dict[str, Any] | None:
    if value is None:
        return None
    if not isinstance(value, dict):
        raise ObservationError("invalid_field_value", "followup must be null or an object")
    unknown = sorted(set(value) - {"kind", "repo", "number", "reason"})
    if unknown:
        raise ObservationError(
            "invalid_field_value", f"followup has unknown key(s): {', '.join(unknown)}"
        )
    kind = value.get("kind", "none")
    if kind not in FOLLOWUP_KINDS:
        raise ObservationError(
            "invalid_field_value", f"followup.kind={kind!r} not in {'/'.join(FOLLOWUP_KINDS)}"
        )
    if kind == "issue":
        repo = value.get("repo")
        number = value.get("number")
        if not isinstance(repo, str) or not _REPO_RE.match(repo.strip()):
            raise ObservationError(
                "invalid_field_value", f"followup.repo={repo!r} is not 'owner/name'"
            )
        if isinstance(number, bool) or not isinstance(number, int) or number <= 0:
            raise ObservationError(
                "invalid_field_value", f"followup.number={number!r} is not a positive int"
            )
        return {"kind": "issue", "repo": repo.strip(), "number": number}
    if kind == "waiver":
        # A waiver with no stated reason is an unexplained drop: refuse it.
        return {"kind": "waiver", "reason": _require_str(value.get("reason"), "followup.reason")}
    return {"kind": "none"}


def normalize_field_value(spec: FieldSpec, value: Any, entity: dict[str, Any]) -> Any:
    """Validate and normalise one field value; raise ``ObservationError``."""
    if spec.kind == "enum":
        if not isinstance(value, str) or value not in spec.values:
            raise ObservationError(
                "invalid_field_value",
                f"{spec.name}={value!r} not in {'/'.join(spec.values)}",
            )
        return value
    if spec.kind == "bool":
        if not isinstance(value, bool):
            raise ObservationError("invalid_field_value", f"{spec.name}={value!r} is not a bool")
        return value
    if spec.kind == "int":
        if isinstance(value, bool) or not isinstance(value, int) or value < 0:
            raise ObservationError(
                "invalid_field_value", f"{spec.name}={value!r} is not a non-negative int"
            )
        return value
    if spec.kind == "hours":
        if isinstance(value, bool) or not isinstance(value, (int, float)) or value < 0:
            raise ObservationError(
                "invalid_field_value", f"{spec.name}={value!r} is not a non-negative number"
            )
        return round(float(value), 3)
    if spec.kind == "text":
        return _require_str(value, spec.name)
    if spec.kind == "lane":
        if not isinstance(value, str) or not _ACTOR_RE.match(value.strip()):
            raise ObservationError(
                "invalid_field_value",
                f"{spec.name}={value!r} is not a lane ('machine:workspace')",
            )
        return value.strip()
    if spec.kind == "utc-timestamp":
        # Same clock rules as ``observed_at``: naive and non-UTC stamps are refused,
        # and the stored value is the normalised UTC rendering.
        return format_utc(parse_utc_timestamp(value, where=spec.name))
    if spec.kind == "issue-ref":
        if not isinstance(value, str) or not _ISSUE_REF_RE.match(value.strip()):
            raise ObservationError(
                "invalid_field_value", f"{spec.name}={value!r} is not 'owner/repo#N'"
            )
        return value.strip()
    if spec.kind == "dependencies":
        return _validate_dependencies(value, entity)
    if spec.kind == "followup":
        return _validate_followup(value)
    raise LedgerError("UNKNOWN_FIELD_KIND", f"{spec.name}: {spec.kind}")  # pragma: no cover


def parse_observation(
    raw: Any,
    ledger: str,
    *,
    defaults: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Validate one observation envelope and return its canonical form.

    ``defaults`` supplies the fields a journal message carries outside the
    envelope (``actor`` from the message author, ``observed_at`` from its
    timestamp, ``message_id`` from its id) and the baseline header defaults.
    """
    defaults = defaults or {}
    if not isinstance(raw, dict):
        raise ObservationError("invalid_record", "observation is not an object")
    unknown = sorted(set(raw) - OBSERVATION_KEYS)
    if unknown:
        raise ObservationError("unknown_key", f"unknown top-level key(s): {', '.join(unknown)}")

    schema = raw.get("schema", OBSERVATION_SCHEMA)
    if schema != OBSERVATION_SCHEMA:
        raise ObservationError(
            "unsupported_schema_version",
            f"schema={schema!r} (this reducer speaks {OBSERVATION_SCHEMA})",
        )
    declared_ledger = raw.get("ledger", defaults.get("ledger", ledger))
    if declared_ledger != ledger:
        raise ObservationError(
            "ledger_mismatch", f"ledger={declared_ledger!r} but target ledger is {ledger!r}"
        )

    actor = raw.get("actor", defaults.get("actor"))
    if not isinstance(actor, str) or not _ACTOR_RE.match(actor.strip()):
        raise ObservationError(
            "missing_actor", f"actor={actor!r} must be a lane ('machine:workspace') or an agent name"
        )
    actor = actor.strip()

    observed_at = parse_utc_timestamp(raw.get("observed_at", defaults.get("observed_at")))

    confidence = raw.get("confidence", defaults.get("confidence", "medium"))
    if confidence not in CONFIDENCE_LEVELS:
        raise ObservationError(
            "invalid_confidence",
            f"confidence={confidence!r} not in {'/'.join(CONFIDENCE_LEVELS)}",
        )

    evidence = raw.get("evidence", defaults.get("evidence"))
    if not isinstance(evidence, str) or not evidence.strip():
        raise ObservationError(
            "missing_evidence",
            "evidence must name where the observation was read (url, command, file:line)",
        )
    evidence = _collapse(evidence)

    entity = _validate_entity(raw.get("entity"), ledger)

    fields = raw.get("fields")
    if not isinstance(fields, dict) or not fields:
        raise ObservationError("invalid_record", "fields must be a non-empty object")
    specs = LEDGER_FIELD_SPECS[ledger]
    unknown_fields = sorted(set(fields) - set(specs))
    if unknown_fields:
        raise ObservationError(
            "unknown_field", f"unknown field(s) for {ledger}: {', '.join(unknown_fields)}"
        )
    normalized_fields = {
        name: normalize_field_value(specs[name], value, entity)
        for name, value in fields.items()
    }

    head_transition = raw.get("head_transition", False)
    if not isinstance(head_transition, bool):
        raise ObservationError("invalid_record", "head_transition must be a bool")

    note = raw.get("note")
    if note is not None:
        note = _require_str(note, "note")

    message_id = raw.get("message_id", defaults.get("message_id"))
    if message_id is not None:
        message_id = _require_str(message_id, "message_id")

    observation: dict[str, Any] = {
        "schema": OBSERVATION_SCHEMA,
        "ledger": ledger,
        "actor": actor,
        "observed_at": format_utc(observed_at),
        "confidence": confidence,
        "evidence": evidence,
        "entity": entity,
        "head_transition": head_transition,
        "fields": normalized_fields,
    }
    if note is not None:
        observation["note"] = note
    if message_id is not None:
        observation["message_id"] = message_id
    declared_id = raw.get("observation_id")
    computed = observation_id_for(observation)
    if declared_id is not None and declared_id != computed:
        # The id is content-derived; a mismatch means the content was edited
        # after the id was stamped, i.e. the journal is not append-only here.
        raise ObservationError(
            "observation_id_mismatch",
            f"declared {declared_id!r} but content digests to {computed!r}",
        )
    observation["observation_id"] = computed
    return observation


# ---------------------------------------------------------------------------
# 6. RECORDS -- the merge unit
# ---------------------------------------------------------------------------


@dataclass
class Record:
    """One (entity, field-set) contribution: an observation, or a folded one."""

    entity: dict[str, Any]
    key: str
    actor: str
    observed_at: datetime
    confidence: str
    evidence: str
    observation_id: str
    message_id: str | None
    source: str
    fields: dict[str, Any] = dataclass_field(default_factory=dict)

    def sort_key(self) -> tuple[datetime, str, str]:
        return (self.observed_at, self.actor, self.observation_id)


def record_from_observation(observation: dict[str, Any], source: str) -> Record:
    return Record(
        entity=dict(observation["entity"]),
        key=entity_key(observation["entity"]),
        actor=observation["actor"],
        observed_at=parse_utc_timestamp(observation["observed_at"]),
        confidence=observation["confidence"],
        evidence=observation["evidence"],
        observation_id=observation["observation_id"],
        message_id=observation.get("message_id"),
        source=source,
        fields=dict(observation["fields"]),
    )


def _provenance_entry(
    *,
    value: Any,
    observed_at: str,
    actor: str,
    confidence: str,
    evidence: str,
    observation_id: str,
    message_id: str | None,
    source: str,
) -> dict[str, Any]:
    entry = {
        "value": value,
        "observed_at": observed_at,
        "actor": actor,
        "confidence": confidence,
        "evidence": evidence,
        "observation_id": observation_id,
        "source": source,
    }
    if message_id is not None:
        entry["message_id"] = message_id
    return entry


def records_from_snapshot(snapshot: dict[str, Any], ledger: str) -> list[Record]:
    """Fold a prior snapshot back into records, one per (field, history entry).

    This is the archive-aware half of the checkpoint contract: whatever the
    dashboard has since condensed out of its journal is already folded here, at
    its ORIGINAL timestamp and with its ORIGINAL provenance, so the next reduce
    neither re-derives it nor loses it.
    """
    records: list[Record] = []
    for row in snapshot.get("rows", []):
        try:
            entity = _validate_entity(row.get("entity"), ledger)
        except ObservationError:
            continue  # a corrupt row is dropped, never allowed to poison the fold
        for name, entries in (row.get("history") or {}).items():
            spec = LEDGER_FIELD_SPECS[ledger].get(name)
            if spec is None or not isinstance(entries, list):
                continue
            for entry in entries:
                if not isinstance(entry, dict) or "value" not in entry:
                    continue
                raw_observation = {
                    "schema": OBSERVATION_SCHEMA,
                    "ledger": ledger,
                    "actor": entry.get("actor", "checkpoint"),
                    "observed_at": entry.get("observed_at"),
                    "confidence": entry.get("confidence", "medium"),
                    "evidence": entry.get("evidence", "snapshot"),
                    "entity": dict(entity),
                    "fields": {name: entry["value"]},
                }
                try:
                    observation = parse_observation(raw_observation, ledger)
                except ObservationError:
                    continue  # a value that no longer validates is dropped, not merged
                record = record_from_observation(observation, "checkpoint")
                # The id is preserved VERBATIM: an observation folded from the
                # checkpoint and the same observation re-read from the journal
                # must dedupe to one contribution, or every cycle would append
                # a fresh copy of the same value to the history.
                if entry.get("observation_id"):
                    record.observation_id = str(entry["observation_id"])
                records.append(record)
    return records


def records_from_baseline(baseline: dict[str, Any], ledger: str) -> list[Record]:
    if baseline.get("schema") != BASELINE_SCHEMA:
        raise LedgerError(
            "UNSUPPORTED_BASELINE_SCHEMA",
            f"baseline schema={baseline.get('schema')!r} (expected {BASELINE_SCHEMA})",
        )
    declared = baseline.get("ledger")
    if declared != ledger:
        raise LedgerError(
            "BASELINE_LEDGER_MISMATCH", f"baseline ledger={declared!r} but target is {ledger!r}"
        )
    generated_at = baseline.get("generated_at")
    try:
        parse_utc_timestamp(generated_at, where="baseline.generated_at")
    except ObservationError as exc:
        raise LedgerError("INVALID_BASELINE", exc.detail or exc.reason) from exc
    defaults = {
        "ledger": ledger,
        "actor": baseline.get("actor", "baseline"),
        "observed_at": generated_at,
        "confidence": baseline.get("confidence", "medium"),
        "evidence": baseline.get("evidence", "baseline"),
    }
    records: list[Record] = []
    for index, entry in enumerate(baseline.get("rows", [])):
        # The baseline is a hand-authored input, not a journal: a bad row is a
        # configuration error and is refused LOUDLY rather than skipped -- a
        # silently dropped seed is a state nobody would think to look for.
        try:
            observation = parse_observation(entry, ledger, defaults=defaults)
        except ObservationError as exc:
            raise LedgerError(
                "INVALID_BASELINE", f"baseline.rows[{index}]: {exc.detail or exc.reason}"
            ) from exc
        records.append(record_from_observation(observation, "baseline"))
    return records


# ---------------------------------------------------------------------------
# 7. JOURNAL EXPORT -- messages in, observations out
# ---------------------------------------------------------------------------

_MESSAGE_LIST_KEYS = ("messages", "entries", "events", "items", "journal", "content")
_MESSAGE_ID_KEYS = ("messageId", "message_id", "id", "uuid")
_MESSAGE_AUTHOR_KEYS = ("author", "actor", "lane", "from", "sender")
_MESSAGE_TIME_KEYS = ("createdAt", "created_at", "observedAt", "observed_at", "timestamp", "ts")
_MESSAGE_CONTENT_KEYS = ("content", "body", "message", "text")
#: How deep the adapter walks the producer envelope. A RooSync read wraps its
#: payload (``data.intercom.messages``), so a top-level-only reader sees
#: "no messages" on a perfectly good export -- the shape is the producer's, and
#: the adapter's job is to find the journal in it, not to demand one shape.
_EXPORT_WALK_DEPTH = 3


def _first_present(source: dict[str, Any], keys: Iterable[str]) -> Any:
    for key in keys:
        if key in source and source[key] not in (None, ""):
            return source[key]
    return None


#: Descriptor declarations live at the DOCUMENTED paths only: the root of the
#: export and its ``data`` envelope. A key-by-key BFS would also read any stray
#: ``window``/``format`` nested deeper (e.g. a UI pagination window inside the
#: payload) in place of the producer's own declaration -- more permissive than
#: the README contract, and silent about it.
def _declared_at(raw: Any, keys: Iterable[str]) -> Any:
    data_envelope = raw.get("data") if isinstance(raw, dict) else None
    for source in (raw, data_envelope):
        if isinstance(source, dict):
            found = _first_present(source, keys)
            if found is not None:
                return found
    return None


def _message_list(raw: Any) -> tuple[list[Any], str]:
    """``(messages, path)`` -- the journal inside whatever envelope wraps it."""
    if isinstance(raw, list):
        return raw, "<list>"
    queue: list[tuple[Any, str, int]] = [(raw, "", 0)]
    while queue:
        node, path, level = queue.pop(0)
        if not isinstance(node, dict):
            continue
        for key in _MESSAGE_LIST_KEYS:
            value = node.get(key)
            if isinstance(value, list):
                return value, f"{path}.{key}".lstrip(".")
        if level >= _EXPORT_WALK_DEPTH:
            continue
        for key, value in node.items():
            if isinstance(value, dict):
                queue.append((value, f"{path}.{key}".lstrip("."), level + 1))
    raise LedgerError(
        "UNSUPPORTED_EXPORT_SHAPE",
        "export must be a list of messages, or an object wrapping one under "
        f"{'/'.join(_MESSAGE_LIST_KEYS)} (a RooSync read nests them under data.intercom)",
    )


def _actor_from(value: Any) -> str | None:
    """Normalise an author, whichever shape the transport hands us.

    A RooSync message carries ``author`` as an OBJECT whose machine key is
    ``machineId`` -- ``{"machineId": "myia-ai-01", "workspace": "CoursIA"}`` --
    not the ``machine:workspace`` lane string the ledger speaks. Reading it as a
    string, or looking only for a ``machine`` key, refuses every real
    observation with ``missing_actor``: the failure is silent at the producer
    and total at the reducer.
    """
    if isinstance(value, str):
        return value.strip() or None
    if not isinstance(value, dict):
        return None
    for left in ("machineId", "machine_id", "machine", "host"):
        for right in ("workspace", "workspaceId", "workspace_id", "lane"):
            first, second = value.get(left), value.get(right)
            if not isinstance(first, str) or not isinstance(second, str):
                continue
            if first.strip() and second.strip():
                return f"{first.strip()}:{second.strip()}"
    for key in ("lane", "login", "name", "actor", "author", "id"):
        candidate = value.get(key)
        if isinstance(candidate, str) and candidate.strip():
            return candidate.strip()
    return None


def parse_journal_export(raw: Any, ledger: str) -> tuple[dict[str, Any], list[Record], list[dict]]:
    """Parse an export into ``(window, records, rejections)``."""
    window_declared: dict[str, Any] = {}
    if isinstance(raw, dict):
        declared = raw.get("schema")
        if declared is not None and declared != EXPORT_SCHEMA:
            raise LedgerError(
                "UNSUPPORTED_EXPORT_SCHEMA",
                f"export schema={declared!r} (expected {EXPORT_SCHEMA})",
            )
        declared_ledger = raw.get("ledger")
        if declared_ledger is not None and declared_ledger != ledger:
            raise LedgerError(
                "EXPORT_LEDGER_MISMATCH",
                f"export ledger={declared_ledger!r} but target is {ledger!r}",
            )
        declared_format = _declared_at(raw, ("format", "content_format"))
        if declared_format is not None and declared_format != ENVELOPE_FORMAT:
            raise LedgerError(
                "UNSUPPORTED_EXPORT_FORMAT",
                f"export format={declared_format!r} (this reducer reads {ENVELOPE_FORMAT!r})",
            )
        window_declared = _declared_at(raw, ("window",))
        if isinstance(window_declared, dict):
            window_declared = dict(window_declared)
        else:
            window_declared = {}
    # Fail-closed: an export that does not declare what it covers is treated as a
    # TAIL, because assuming 'full' would let a condensed journal rebuild state
    # from a fragment and silently drop everything the archives hold. This holds
    # for a producer-shaped export too: the adapter finds the journal, it never
    # guesses the coverage.
    kind = window_declared.get("kind", "incremental")
    if kind not in ("full", "incremental"):
        raise LedgerError("UNSUPPORTED_WINDOW_KIND", f"window.kind={kind!r}")
    archives = window_declared.get("archives") or []
    if not isinstance(archives, list) or any(not isinstance(item, str) for item in archives):
        raise LedgerError("UNSUPPORTED_WINDOW_KIND", "window.archives must be a list of strings")
    messages, path = _message_list(raw)
    window = {
        "kind": kind,
        "archives": [str(item) for item in archives],
        "messages": len(messages),
        "path": path,
    }

    records: list[Record] = []
    rejections: list[dict[str, Any]] = []
    ignored = 0
    for index, message in enumerate(messages):
        label = f"message[{index}]"
        message_id = None
        if isinstance(message, dict):
            message_id = _first_present(message, _MESSAGE_ID_KEYS)
        if message_id:
            label = f"message[{index}] id={message_id}"
        if not isinstance(message, dict):
            rejections.append(
                {"source": label, "reason": "invalid_record", "detail": "message is not an object"}
            )
            continue
        content = _first_present(message, _MESSAGE_CONTENT_KEYS)
        if content is None:
            rejections.append(
                {
                    "source": label,
                    "reason": "unparsable_envelope",
                    "detail": f"no content key ({'/'.join(_MESSAGE_CONTENT_KEYS)})",
                }
            )
            continue
        if not looks_like_observation(content):
            # Dashboard prose (an ai-01 status snapshot, a human note) is not a
            # malformed observation: refusing it would turn a healthy ledger red
            # on every cycle it is read.
            ignored += 1
            continue
        defaults: dict[str, Any] = {"ledger": ledger}
        author = _actor_from(_first_present(message, _MESSAGE_AUTHOR_KEYS))
        if author is not None:
            defaults["actor"] = author
        created = _first_present(message, _MESSAGE_TIME_KEYS)
        if created is not None:
            defaults["observed_at"] = created
        if message_id is not None:
            defaults["message_id"] = str(message_id)
        try:
            observation = parse_observation(parse_envelope(content), ledger, defaults=defaults)
        except ObservationError as exc:
            rejections.append({"source": label, "reason": exc.reason, "detail": exc.detail})
            continue
        records.append(record_from_observation(observation, f"journal:{label}"))
    window["ignored"] = ignored
    return window, records, rejections


# ---------------------------------------------------------------------------
# 8. MERGE -- newest compatible observation per field
# ---------------------------------------------------------------------------


def _merge_row(
    ledger: str,
    entity: dict[str, Any],
    records: Sequence[Record],
    config: dict[str, Any],
) -> dict[str, Any]:
    specs = LEDGER_FIELD_SPECS[ledger]
    history_cap = int(config.get("history_max_entries_per_field", 25))

    fields: dict[str, Any] = {}
    provenance: dict[str, Any] = {}
    history: dict[str, Any] = {}
    truncated: dict[str, int] = {}

    for name in specs:
        # One contribution per OBSERVATION, not per occurrence: the checkpoint
        # fold and the journal re-read describe the same observation, and the
        # journal copy (seen last) wins so the richer provenance survives.
        by_observation: dict[str, Record] = {}
        for record in records:
            if name in record.fields:
                by_observation[record.observation_id] = record
        contributions = list(by_observation.values())
        if not contributions:
            continue
        contributions.sort(key=Record.sort_key)
        winner = contributions[-1]
        fields[name] = winner.fields[name]
        provenance[name] = _provenance_entry(
            value=winner.fields[name],
            observed_at=format_utc(winner.observed_at),
            actor=winner.actor,
            confidence=winner.confidence,
            evidence=winner.evidence,
            observation_id=winner.observation_id,
            message_id=winner.message_id,
            source=winner.source,
        )
        entries = []
        for record in contributions:
            entry = _provenance_entry(
                value=record.fields[name],
                observed_at=format_utc(record.observed_at),
                actor=record.actor,
                confidence=record.confidence,
                evidence=record.evidence,
                observation_id=record.observation_id,
                message_id=record.message_id,
                source=record.source,
            )
            entry["applied"] = record is winner
            entry["reason"] = "applied" if record is winner else "superseded"
            entries.append(entry)
        if len(entries) > history_cap:
            truncated[name] = len(entries) - history_cap
            entries = entries[-history_cap:]
        history[name] = entries

    key = entity_key(entity)
    verdict_field, _terminal = TERMINAL_VALUES[ledger]
    verdict = fields.get(verdict_field)
    row: dict[str, Any] = {
        "key": key,
        "ledger": ledger,
        "entity": dict(entity),
        "historical": verdict in TERMINAL_SETS[ledger],
        "fields": fields,
        "provenance": provenance,
        "history": history,
        "missing_fields": sorted(set(specs) - set(fields)),
        "last_observed_at": max((format_utc(record.observed_at) for record in records), default=None),
        "contributions": len({record.observation_id for record in records}),
    }
    diagnostics: dict[str, Any] = {
        "rejected_observations": 0,
        # Where the CURRENT state comes from -- not every source ever folded, or
        # the field would change on a re-fold of identical observations.
        "sources": sorted({entry["source"] for entry in provenance.values()}),
    }
    if truncated:
        diagnostics["history_truncated"] = truncated
    row["diagnostics"] = diagnostics
    return row


def reduce_ledger(
    *,
    ledger: str,
    export: Any | None = None,
    prior_snapshot: dict[str, Any] | None = None,
    baseline: dict[str, Any] | None = None,
    now: datetime | None = None,
    config: dict[str, Any] | None = None,
) -> "ReduceResult":
    """Fold baseline + prior snapshot + journal export into a snapshot.

    Raises ``LedgerError`` on anything that would make the result silently
    WRONG (unknown ledger, missing mandatory checkpoint, unreadable export
    shape). Per-observation problems never raise: they land in
    ``snapshot["rejections"]`` with their reason, and the rest still reduces.
    """
    if ledger not in LEDGERS:
        raise LedgerError("UNKNOWN_LEDGER", f"{ledger!r} not in {'/'.join(LEDGERS)}")
    resolved_config = dict(DEFAULT_CONFIG)
    if config:
        resolved_config.update({k: v for k, v in config.items() if k != "ledgers"})
        if isinstance(config.get("ledgers"), dict):
            merged = dict(DEFAULT_CONFIG["ledgers"])
            merged.update(config["ledgers"])
            resolved_config["ledgers"] = merged
    moment = now or utcnow()

    if prior_snapshot is not None:
        prior_ledger = prior_snapshot.get("ledger")
        if prior_ledger is not None and prior_ledger != ledger:
            raise LedgerError(
                "CHECKPOINT_LEDGER_MISMATCH",
                f"prior snapshot ledger={prior_ledger!r} but target is {ledger!r}",
            )

    window: dict[str, Any] = {"kind": "full", "archives": [], "messages": 0}
    journal_records: list[Record] = []
    rejections: list[dict[str, Any]] = []
    warnings: list[str] = []
    if export is not None:
        window, journal_records, rejections = parse_journal_export(export, ledger)

    # The baseline is a configuration input, not a journal: a misconfigured one
    # is fatal and is reported as such even when the journal is a tail.
    baseline_records: list[Record] = []
    if baseline is not None:
        baseline_records = records_from_baseline(baseline, ledger)

    # --- archive-aware checkpoint contract (fail-closed) ---------------------
    if window["kind"] == "incremental" and prior_snapshot is None:
        raise LedgerError(
            "MISSING_CHECKPOINT",
            "an incremental window does not carry the whole journal: the prior "
            "snapshot is mandatory (pass --snapshot, or --window-full if the "
            "export really is complete)",
        )
    checkpoint = (prior_snapshot or {}).get("checkpoint") or {}
    if checkpoint:
        previous_newest = checkpoint.get("events", {}).get("newest_observed_at")
        export_newest = max(
            (record.observed_at for record in journal_records), default=None
        )
        if previous_newest and export_newest is not None:
            try:
                previous_dt = parse_utc_timestamp(previous_newest, where="checkpoint.newest")
            except ObservationError:
                previous_dt = None  # a corrupt checkpoint stamp cannot gate the fold
                warnings.append("checkpoint_newest_unreadable: ignored for ordering")
            if previous_dt is not None and export_newest < previous_dt:
                warnings.append(
                    f"export_older_than_checkpoint: newest event {format_utc(export_newest)} "
                    f"is older than the folded checkpoint {previous_newest}; older "
                    "observations lose on observed_at and cannot regress state"
                )

    snapshot_records: list[Record] = []
    if prior_snapshot is not None:
        snapshot_records = records_from_snapshot(prior_snapshot, ledger)

    all_records = baseline_records + snapshot_records + journal_records

    already_seen = set(checkpoint.get("events", {}).get("observation_ids_recent") or [])
    replayed = sum(1 for record in journal_records if record.observation_id in already_seen)

    by_key: dict[str, list[Record]] = {}
    for record in all_records:
        by_key.setdefault(record.key, []).append(record)

    rows = [
        _merge_row(ledger, records[0].entity, records, resolved_config)
        for _key, records in sorted(by_key.items())
    ]

    stale_hours = float(resolved_config.get("stale_observation_hours", 72))
    stale_before = moment - timedelta(hours=stale_hours)
    for row in rows:
        # `last_observed_dt` is a live datetime used only for the staleness test:
        # it must never reach the snapshot, which has to stay JSON-serialisable.
        newest = max(record.observed_at for record in by_key[row["key"]])
        row["stale"] = newest < stale_before

    summary = _summarize(
        ledger,
        rows,
        rejections=rejections,
        window=window,
        config=resolved_config,
        now=moment,
        replayed=replayed,
    )

    recent_ids = list(
        dict.fromkeys(
            [record.observation_id for record in journal_records]
            + list(checkpoint.get("events", {}).get("observation_ids_recent") or [])
        )
    )[: int(resolved_config.get("observation_ids_recent_max", 200))]
    consumed_total = int(checkpoint.get("events", {}).get("consumed_total", 0)) + len(
        journal_records
    )
    state_digest = digest_of(
        [
            {"key": row["key"], "fields": row["fields"], "historical": row["historical"]}
            for row in rows
        ]
    )
    checkpoint_out = {
        "schema": CHECKPOINT_SCHEMA,
        "ledger": ledger,
        "folded_at": format_utc(moment),
        "window": {
            "kind": window["kind"],
            "archives": window["archives"],
            "messages": window.get("messages", 0),
            "ignored": window.get("ignored", 0),
            "path": window.get("path"),
        },
        "events": {
            "consumed_total": consumed_total,
            "replayed": replayed,
            "newest_observed_at": max(
                (format_utc(record.observed_at) for record in journal_records), default=None
            ),
            "newest_message_id": next(
                (
                    record.message_id
                    for record in sorted(journal_records, key=Record.sort_key, reverse=True)
                    if record.message_id
                ),
                None,
            ),
            "rejected": len(rejections),
            "observation_ids_recent": recent_ids,
        },
        "folded": {
            "baseline_rows": len({record.key for record in baseline_records}),
            "checkpoint_rows": len({record.key for record in snapshot_records}),
            "journal_records": len(journal_records),
        },
        "state_digest": state_digest,
    }

    snapshot = {
        "schema": SNAPSHOT_SCHEMA,
        "ledger": ledger,
        "workspace": _workspace_of(resolved_config, ledger),
        "generated_at": format_utc(moment),
        "counts": summary["rows"],
        "rows": rows,
        "rejections": rejections,
        "warnings": warnings,
        "checkpoint": checkpoint_out,
    }
    status_text = _status_text(ledger, snapshot, summary, resolved_config)
    return ReduceResult(
        snapshot=snapshot, summary=summary, status_text=status_text, warnings=warnings
    )


# ---------------------------------------------------------------------------
# 9. SUMMARY -- EAT metrics
# ---------------------------------------------------------------------------


def _workspace_of(config: dict[str, Any], ledger: str) -> str:
    """The dedicated dashboard for a ledger, tolerant of a corrupt config.

    A malformed `config.json` must degrade to the compiled-in mapping, never
    crash the organ: the dashboard a ledger lives on is a fact of the code, and
    the config only re-states it.
    """
    try:
        workspace = config["ledgers"][ledger]["workspace"]
    except (KeyError, TypeError):
        return LEDGER_WORKSPACES[ledger]
    return workspace if isinstance(workspace, str) and workspace else LEDGER_WORKSPACES[ledger]


def _counts(values: Iterable[Any]) -> dict[str, int]:
    out: dict[str, int] = {}
    for value in values:
        if value is None:
            continue
        out[str(value)] = out.get(str(value), 0) + 1
    return dict(sorted(out.items(), key=lambda item: (-item[1], item[0])))


def _live_rows(rows: Sequence[dict[str, Any]]) -> list[dict[str, Any]]:
    return [row for row in rows if not row["historical"]]


def _row_counts(rows: Sequence[dict[str, Any]], live: Sequence[dict[str, Any]]) -> dict[str, int]:
    """The row census every ledger summary carries, whatever its fields mean."""
    return {
        "total": len(rows),
        "live": len(live),
        "historical": len(rows) - len(live),
        "incomplete": sum(1 for row in live if row["missing_fields"]),
        "stale": sum(1 for row in live if row.get("stale")),
    }


def _summarize_gpu_reservation(rows: Sequence[dict[str, Any]]) -> dict[str, Any]:
    live = _live_rows(rows)
    held_by_machine: dict[str, int] = {}
    for row in live:
        if row["fields"].get("state") == "held":
            machine = str(row["entity"].get("machine", "?"))
            held_by_machine[machine] = held_by_machine.get(machine, 0) + 1
    holders = sorted(
        {str(row["fields"]["holder"]) for row in live if row["fields"].get("holder")}
    )
    return {
        "rows": _row_counts(rows, live),
        "state": _counts(row["fields"].get("state") for row in live),
        "held_by_machine": dict(sorted(held_by_machine.items())),
        "holders": holders,
        # A hold whose deadline has passed is the row the weekly sweep must chase:
        # the state is the producer's to set, this list only surfaces them.
        "stale_holds": sorted(row["key"] for row in live if row["fields"].get("state") == "stale"),
    }


def _summarize_issue_debt(rows: Sequence[dict[str, Any]]) -> dict[str, Any]:
    live = _live_rows(rows)
    eat_by_class: dict[str, float] = {}
    prs_by_class: dict[str, int] = {}
    for row in live:
        state = str(row["fields"].get("state_class", "unknown"))
        eat_by_class[state] = round(
            eat_by_class.get(state, 0.0) + float(row["fields"].get("eat_hours", 0) or 0), 3
        )
        prs_by_class[state] = prs_by_class.get(state, 0) + int(
            row["fields"].get("remaining_atomic_prs", 0) or 0
        )
    followups = {"issue": 0, "waiver": 0, "none": 0, "missing": 0}
    for row in rows:
        followup = row["fields"].get("followup", "missing")
        if followup is None:
            followups["none"] += 1
        elif isinstance(followup, dict) and followup.get("kind") in followups:
            followups[followup["kind"]] += 1
        else:
            followups["missing"] += 1
    dependency_edges = 0
    external_edges = 0
    for row in live:
        for dependency in row["fields"].get("dependencies") or []:
            dependency_edges += 1
            if dependency.get("kind") == "external":
                external_edges += 1
    return {
        "rows": _row_counts(rows, live),
        "state_class": _counts(row["fields"].get("state_class") for row in live),
        "closeability": _counts(row["fields"].get("closeability") for row in live),
        "closeable_now": sorted(
            row["key"]
            for row in live
            if row["fields"].get("closeability") == "closeable-now"
        ),
        "remaining_atomic_prs": {
            "total": sum(prs_by_class.values()),
            "by_state_class": dict(sorted(prs_by_class.items())),
        },
        "eat_hours": {
            "total": round(sum(eat_by_class.values()), 2),
            "by_state_class": dict(sorted((k, round(v, 2)) for k, v in eat_by_class.items())),
            "max_row": max(
                (
                    {"key": row["key"], "eat_hours": float(row["fields"].get("eat_hours", 0) or 0)}
                    for row in live
                ),
                key=lambda item: (item["eat_hours"], item["key"]),
                default=None,
            ),
        },
        "dependencies": {
            "rows_with_dependencies": sum(
                1 for row in live if row["fields"].get("dependencies")
            ),
            "edges": dependency_edges,
            "external_edges": external_edges,
        },
        "followups": followups,
    }


#: One summariser per ledger: the census is shared, the meaning of a field is not.
_SUMMARIZERS: dict[str, Any] = {
    ISSUE_DEBT: _summarize_issue_debt,
    GPU_RESERVATION: _summarize_gpu_reservation,
}


def _summarize(
    ledger: str,
    rows: Sequence[dict[str, Any]],
    *,
    rejections: Sequence[dict[str, Any]],
    window: dict[str, Any],
    config: dict[str, Any],
    now: datetime,
    replayed: int,
) -> dict[str, Any]:
    detail = _SUMMARIZERS[ledger](rows)
    summary: dict[str, Any] = {
        "schema": SUMMARY_SCHEMA,
        "ledger": ledger,
        "workspace": _workspace_of(config, ledger),
        "generated_at": format_utc(now),
        "window": {
            "kind": window["kind"],
            "messages": window.get("messages", 0),
            "ignored": window.get("ignored", 0),
            "path": window.get("path"),
        },
        "rejections": {
            "total": len(rejections),
            "by_reason": _counts(item["reason"] for item in rejections),
        },
        "replayed_observations": replayed,
    }
    summary.update(detail)
    return summary


def _status_text(
    ledger: str,
    snapshot: dict[str, Any],
    summary: dict[str, Any],
    config: dict[str, Any],
) -> str:
    """Compact text ai-01 writes to the ledger dashboard's ``status`` section."""
    max_rows = int(config.get("status_max_rows", 12))
    counts = summary["rows"]
    checkpoint = snapshot["checkpoint"]["events"]
    lines = [
        f"[LEDGER] {ledger} @ {snapshot['generated_at']} | "
        f"events {checkpoint['consumed_total']} (+{snapshot['checkpoint']['folded']['journal_records']}) "
        f"| rows {counts['live']} live / {counts['historical']} historical "
        f"| window {summary['window']['kind']}"
    ]
    if ledger == ISSUE_DEBT:
        eat = summary["eat_hours"]
        lines.append(
            f"eat_hours {eat['total']:.2f} | remaining_atomic_prs "
            f"{summary['remaining_atomic_prs']['total']} | closeable-now "
            f"{len(summary['closeable_now'])} | stale rows {counts['stale']}"
        )
        lines.append(
            "state_class: "
            + (", ".join(f"{k} {v}" for k, v in summary["state_class"].items()) or "-")
        )
        followups = summary["followups"]
        lines.append(
            f"followups: issue {followups['issue']}, waiver {followups['waiver']}, "
            f"none {followups['none']}, missing {followups['missing']}"
        )
        ranked = sorted(
            _live_rows(snapshot["rows"]),
            key=lambda row: (
                -float(row["fields"].get("eat_hours", 0) or 0),
                row["key"],
            ),
        )
        for row in ranked[:max_rows]:
            lines.append(
                f"  {row['key']} {row['fields'].get('state_class', '?')} "
                f"eat {float(row['fields'].get('eat_hours', 0) or 0):.2f}h "
                f"prs {int(row['fields'].get('remaining_atomic_prs', 0) or 0)} "
                f"close {row['fields'].get('closeability', '?')}"
            )
    if ledger == GPU_RESERVATION:
        lines.append(
            "state: " + (", ".join(f"{k} {v}" for k, v in summary["state"].items()) or "-")
        )
        held = summary["held_by_machine"]
        lines.append(
            "held_by_machine: "
            + (", ".join(f"{k} {v}" for k, v in held.items()) or "-")
        )
        lines.append(
            f"holders: {len(summary['holders'])} | "
            f"stale holds {len(summary['stale_holds'])} | stale rows {counts['stale']}"
        )
        # Live holds first, then by deadline: the row a reader must act on is on top.
        ranked = sorted(
            _live_rows(snapshot["rows"]),
            key=lambda row: (
                str(row["fields"].get("expected_end") or "~"),
                row["key"],
            ),
        )
        for row in ranked[:max_rows]:
            lines.append(
                f"  {row['key']} {row['fields'].get('state', '?')} "
                f"holder {row['fields'].get('holder', '?')} "
                f"-> {row['fields'].get('expected_end', '?')} "
                f"{row['fields'].get('workload', '')}".rstrip()
            )
    if len(_live_rows(snapshot["rows"])) > max_rows:
        lines.append(f"  ... {len(_live_rows(snapshot['rows'])) - max_rows} more live rows")
    if snapshot["rejections"]:
        lines.append(f"rejected: {len(snapshot['rejections'])} observation(s)")
    if snapshot["warnings"]:
        for warning in snapshot["warnings"]:
            lines.append(f"warn: {warning}")
    return "\n".join(lines) + "\n"


@dataclass
class ReduceResult:
    snapshot: dict[str, Any]
    summary: dict[str, Any]
    status_text: str
    warnings: list[str] = dataclass_field(default_factory=list)


# ---------------------------------------------------------------------------
# 10. LOCAL STATE -- paths, atomic writes, lock
# ---------------------------------------------------------------------------


def default_state_dir() -> Path:
    override = os.environ.get("COURSIA_LEDGER_STATE_DIR")
    if override:
        return Path(override)
    local = os.environ.get("LOCALAPPDATA") or os.environ.get("XDG_STATE_HOME")
    if local:
        return Path(local) / "CoursIA" / "debt-ledgers"
    return Path.home() / ".local" / "state" / "CoursIA" / "debt-ledgers"


def _inside_git_tree(path: Path) -> bool:
    """Is this path inside a git working tree (where a stray write can be committed)?"""
    try:
        resolved = path.resolve()
    except OSError:  # pragma: no cover - unresolvable path
        return False
    for candidate in (resolved, *resolved.parents):
        if (candidate / ".git").exists():
            return True
    return False


def assert_local_output(path: Path, *, what: str) -> None:
    """Refuse any path this tool would WRITE that is shared or in the repo.

    Two refusals, no override, applied to EVERY output -- the state dir and each
    of ``--out`` / ``--out-dir`` / ``--summary-out`` / ``--status-out``:

      * under ``$ROOSYNC_SHARED_PATH`` -- Drive has no locking, so two writers
        are last-write-wins and the ledger would silently lose observations;
      * inside a git working tree -- ledger state is not repo content.

    Guarding only the state directory would have left the four explicit output
    flags as an unguarded side door onto the same mount.
    """
    shared = os.environ.get("ROOSYNC_SHARED_PATH")
    if shared:
        try:
            resolved = path.resolve()
            shared_resolved = Path(shared).resolve()
        except OSError:  # pragma: no cover - unresolvable path
            resolved = shared_resolved = None
        if resolved is not None and (
            resolved == shared_resolved or shared_resolved in resolved.parents
        ):
            raise LedgerError(
                "SHARED_PATH_REFUSED",
                f"{what} {resolved} is inside $ROOSYNC_SHARED_PATH ({shared_resolved}); the "
                "shared transport is the dashboard journal, never a shared file",
            )
    if _inside_git_tree(path):
        raise LedgerError(
            "REPO_PATH_REFUSED",
            f"{what} {path} is inside a git working tree; ledger state is not repo content "
            "(the dashboard journal carries the shared state)",
        )


def _write_text_atomic(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    handle, raw_tmp = tempfile.mkstemp(prefix=f".{path.name}.", suffix=".tmp", dir=path.parent)
    tmp = Path(raw_tmp)
    try:
        with os.fdopen(handle, "w", encoding="utf-8", newline="\n") as stream:
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(tmp, path)
    finally:
        try:
            tmp.unlink()
        except FileNotFoundError:
            pass


def write_json_atomic(path: Path, payload: Any) -> None:
    _write_text_atomic(path, json.dumps(payload, ensure_ascii=False, indent=2) + "\n")


class LedgerLock:
    """Single-writer lock for the reducer's local artifacts.

    Only the reducer takes it: ai-01 is the sole snapshot writer by contract, and
    the lock is what makes a second concurrent reducer visible instead of letting
    two writers interleave their ``os.replace`` calls.
    """

    def __init__(self, path: Path, *, timeout: float = 10.0, stale_after: float = 120.0,
                 poll: float = 0.05) -> None:
        self.path = path
        self.timeout = timeout
        self.stale_after = stale_after
        self.poll = poll
        self.acquired = False

    def _try_acquire(self) -> bool:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        try:
            handle = os.open(self.path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        except FileExistsError:
            try:
                age = time.time() - self.path.stat().st_mtime
            except OSError:
                return False
            if age > self.stale_after:
                try:
                    self.path.unlink()
                except OSError:
                    return False
                return False
            return False
        with os.fdopen(handle, "w", encoding="utf-8", newline="\n") as stream:
            json.dump(
                {
                    "pid": os.getpid(),
                    "host": os.environ.get("COMPUTERNAME") or os.environ.get("HOSTNAME") or "?",
                    "acquired_at": format_utc(utcnow()),
                },
                stream,
            )
        return True

    def __enter__(self) -> "LedgerLock":
        deadline = time.monotonic() + self.timeout
        while True:
            if self._try_acquire():
                self.acquired = True
                return self
            if time.monotonic() >= deadline:
                raise LedgerError(
                    "LOCK_TIMEOUT",
                    f"{self.path} is held by another reducer (waited {self.timeout:.0f}s)",
                )
            time.sleep(self.poll)

    def __exit__(self, *exc_info: Any) -> None:
        if self.acquired:
            try:
                self.path.unlink()
            except FileNotFoundError:  # pragma: no cover - released by a stale sweep
                pass
            self.acquired = False


def spool_path(spool_dir: Path, observation: dict[str, Any]) -> Path:
    """Collision-safe, deterministic filename: distinct observations never clash.

    Two actors observing the same entity at the same instant produce different
    ``observation_id`` values (actor and evidence are part of the digest), so the
    file itself is the collision detector -- see ``spool_observation``.
    """
    return spool_dir / f"{observation['observation_id']}.json"


def spool_observation(spool_dir: Path, observation: dict[str, Any]) -> tuple[Path, bool]:
    """Write an envelope into the local outbox; ``(path, created)``.

    Uses ``O_CREAT|O_EXCL``: a re-append of the same observation is reported as
    ``created=False`` and changes nothing, which is what makes ``append``
    idempotent without a lock.
    """
    spool_dir.mkdir(parents=True, exist_ok=True)
    path = spool_path(spool_dir, observation)
    payload = envelope_line(observation) + "\n"
    try:
        handle = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError:
        return path, False
    with os.fdopen(handle, "w", encoding="utf-8", newline="\n") as stream:
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())
    return path, True


# ---------------------------------------------------------------------------
# 11. INIT -- schema doc, config, baseline, dashboard bootstrap
# ---------------------------------------------------------------------------


def schema_document() -> dict[str, Any]:
    """The generated contract, emitted by ``init`` so it cannot drift from code."""
    return {
        "schema": SCHEMA_DOC_VERSION,
        "generated_by": "scripts/coordination/debt_ledger.py",
        "envelopes": {
            "observation": OBSERVATION_SCHEMA,
            "journal_export": EXPORT_SCHEMA,
            "snapshot": SNAPSHOT_SCHEMA,
            "summary": SUMMARY_SCHEMA,
            "checkpoint": CHECKPOINT_SCHEMA,
            "baseline": BASELINE_SCHEMA,
            "config": CONFIG_SCHEMA,
        },
        "transport": {
            "kind": "roosync_dashboard_journal",
            "rule": (
                "observations are append-only dashboard messages on the ledger's dedicated "
                "workspace dashboard; the snapshot is written by ai-01 alone in the 'status' "
                "section via update/replace; nothing is ever written to $ROOSYNC_SHARED_PATH"
            ),
            "envelope_prefix": ENVELOPE_PREFIX,
            "windows": {
                "full": "export claims the whole journal; prior snapshot optional",
                "incremental": "tail export; prior snapshot MANDATORY (fail-closed if absent)",
                "absent": "treated as incremental (fail-closed)",
            },
        },
        "ledgers": {
            ledger: {
                "workspace": LEDGER_WORKSPACES[ledger],
                "entity_keys": list(ENTITY_FIELDS[ledger]),
                "row_key": ENTITY_KEY_FORMATS[ledger],
                "terminal_values": {TERMINAL_VALUES[ledger][0]: sorted(TERMINAL_SETS[ledger])},
                "fields": [
                    {
                        "name": spec.name,
                        "kind": spec.kind,
                        "values": list(spec.values),
                        "description": spec.description,
                    }
                    for spec in LEDGER_FIELD_SPECS[ledger].values()
                ],
            }
            for ledger in LEDGERS
        },
        "observation_keys": sorted(OBSERVATION_KEYS),
        "confidence_levels": list(CONFIDENCE_LEVELS),
        "rejection_reasons": [
            "invalid_record",
            "invalid_schema",
            "unsupported_schema_version",
            "unknown_key",
            "ledger_mismatch",
            "entity_mismatch",
            "unknown_field",
            "invalid_field_value",
            "invalid_confidence",
            "missing_actor",
            "missing_evidence",
            "invalid_timestamp",
            "naive_timestamp",
            "non_utc_timestamp",
            "unparsable_envelope",
            "observation_id_mismatch",
        ],
    }


def dashboard_calls(ledger: str) -> dict[str, str]:
    """The MCP calls for this ledger, as prescribed text (never a shell command)."""
    workspace = LEDGER_WORKSPACES[ledger]
    return {
        "append_observation": (
            f'roosync_dashboard(action:"append", type:"workspace", '
            f'workspace:"{workspace}", content:"{ENVELOPE_PREFIX} {{...}}")'
        ),
        "read_journal": (
            f'roosync_dashboard(action:"read", type:"workspace", workspace:"{workspace}", '
            f'section:"all")'
        ),
        "write_snapshot": (
            f'roosync_dashboard(action:"update", type:"workspace", workspace:"{workspace}", '
            f'section:"status", content:"<snapshots/status.md>")   # ai-01 ONLY'
        ),
    }


def init_ledger_tree(
    state_dir: Path, *, ledgers: Sequence[str], dry_run: bool, now: datetime | None = None
) -> list[str]:
    """Create the local tree; return the paths (existing or planned)."""
    assert_local_output(state_dir, what="state directory")
    moment = now or utcnow()
    planned: list[str] = []
    config_path = state_dir / "config.json"
    planned.append(str(config_path))
    for ledger in ledgers:
        base = state_dir / ledger
        planned.extend(
            [
                str(base),
                str(base / "spool"),
                str(base / "snapshots"),
                str(base / "baseline.json"),
                str(base / "schema.json"),
            ]
        )
    if dry_run:
        return planned
    state_dir.mkdir(parents=True, exist_ok=True)
    if not config_path.exists():
        write_json_atomic(config_path, DEFAULT_CONFIG)
    doc = schema_document()
    doc["generated_at"] = format_utc(moment)
    baseline_doc = {
        "schema": BASELINE_SCHEMA,
        "generated_at": format_utc(moment),
        "actor": "baseline",
        "confidence": "medium",
        "evidence": "hand-authored baseline",
        "rows": [],
    }
    for ledger in ledgers:
        base = state_dir / ledger
        (base / "spool").mkdir(parents=True, exist_ok=True)
        (base / "snapshots").mkdir(parents=True, exist_ok=True)
        ledger_doc = dict(doc)
        ledger_doc["ledger"] = ledger
        ledger_doc["dashboard_calls"] = dashboard_calls(ledger)
        write_json_atomic(base / "schema.json", ledger_doc)
        if not (base / "baseline.json").exists():
            seed = dict(baseline_doc)
            seed["ledger"] = ledger
            write_json_atomic(base / "baseline.json", seed)
    return planned


# ---------------------------------------------------------------------------
# 12. CLI
# ---------------------------------------------------------------------------


def _read_json(path: Path) -> Any:
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as exc:
        raise LedgerError("UNREADABLE_INPUT", f"{path}: {exc}") from exc
    try:
        return json.loads(text)
    except json.JSONDecodeError as exc:
        raise LedgerError("INVALID_JSON", f"{path}: {exc}") from exc


def _parse_entity_argument(raw: str, ledger: str) -> dict[str, Any]:
    """Parse ``--entity`` into the ledger's entity object."""
    if ledger == GPU_RESERVATION:
        match = re.match(r"^\s*([A-Za-z0-9._-]+)\s*#\s*gpu\s*(\d+)\s*$", raw, re.IGNORECASE)
        if not match:
            raise LedgerError("INVALID_ENTITY", f"{raw!r} is not '<machine>#gpu<n>'")
        return {"machine": match.group(1), "gpu_index": int(match.group(2))}
    match = re.match(r"^\s*([\w.-]+/[\w.-]+)\s*#\s*(\d+)\s*$", raw)
    if not match:
        raise LedgerError("INVALID_ENTITY", f"{raw!r} is not 'owner/repo#N'")
    return {"repo": match.group(1), "issue": int(match.group(2))}


def _loads_object(text: str, *, where: str) -> dict[str, Any]:
    """Parse a JSON object from a CLI argument, or fail with a reason (no traceback)."""
    try:
        parsed = json.loads(text)
    except json.JSONDecodeError as exc:
        raise LedgerError("INVALID_JSON", f"{where}: {exc}") from exc
    if not isinstance(parsed, dict):
        raise LedgerError("INVALID_JSON", f"{where} must be a JSON object")
    return parsed


def _declare_full_window(export: Any, ledger: str) -> Any:
    """``--window-full`` on anything an export can legitimately be.

    A bare LIST is the most natural hand-made export ("here are the messages"),
    and it used to fall through the wrapper untouched -- so the flag documented
    as "declare this complete" silently did nothing and the fold still failed
    closed with MISSING_CHECKPOINT.
    """
    if isinstance(export, list):
        return {
            "schema": EXPORT_SCHEMA,
            "ledger": ledger,
            "window": {"kind": "full", "archives": []},
            "messages": export,
        }
    if isinstance(export, dict):
        # Use the same bounded envelope walk as parse_journal_export. Looking
        # only at export["window"] lets --window-full inject a top-level FULL
        # declaration that shadows an explicit nested INCREMENTAL declaration
        # (for example data.window), rebuilding state from a condensed tail.
        declared = _declared_at(export, ("window",))
        if not isinstance(declared, dict):
            return {**export, "window": {"kind": "full", "archives": []}}
    return export


def _cli_init(args: argparse.Namespace) -> int:
    ledgers = [args.ledger]
    state_dir = Path(args.state_dir) if args.state_dir else default_state_dir()
    planned = init_ledger_tree(
        state_dir, ledgers=ledgers, dry_run=not args.apply, now=parse_utc_timestamp(args.now, where="--now") if args.now else None
    )
    for ledger in ledgers:
        print(f"# {ledger} -> dashboard {LEDGER_WORKSPACES[ledger]}")
        for name, call in dashboard_calls(ledger).items():
            print(f"#   {name}: {call}")
    if args.apply:
        print(f"APPLIED: local state tree at {state_dir}")
    else:
        print(f"DRY-RUN: would create {len(planned)} path(s) under {state_dir} (pass --apply)")
    for path in planned:
        print(f"  {path}")
    return 0


def _cli_append(args: argparse.Namespace) -> int:
    state_dir = Path(args.state_dir) if args.state_dir else default_state_dir()
    assert_local_output(state_dir, what="state directory")
    if args.observation_file:
        raw = _read_json(Path(args.observation_file))
    else:
        if not args.entity or not args.fields_json:
            raise LedgerError(
                "MISSING_INPUT", "append needs --observation-file, or --entity with --fields-json"
            )
        raw = {
            "schema": OBSERVATION_SCHEMA,
            "ledger": args.ledger,
            "actor": args.actor,
            "observed_at": args.observed_at or format_utc(utcnow()),
            "confidence": args.confidence,
            "evidence": args.evidence,
            "entity": _parse_entity_argument(args.entity, args.ledger),
            "head_transition": False,
            "fields": _loads_object(args.fields_json, where="--fields-json"),
        }
        if args.note:
            raw["note"] = args.note
    observation = parse_observation(raw, args.ledger)
    line = envelope_line(observation)
    if args.json:
        payload = {
            "observation_id": observation["observation_id"],
            "ledger": args.ledger,
            "workspace": LEDGER_WORKSPACES[args.ledger],
            "format": ENVELOPE_FORMAT,
            "content_prefix": ENVELOPE_PREFIX,
            "content": line,
            "mcp_call": dashboard_calls(args.ledger)["append_observation"],
        }
    else:
        payload = None
    created = None
    out_path = None
    if args.dry_run:
        # The default: build and print. Appending cannot write shared state at
        # all -- posting the envelope is the agent's MCP call -- so the only
        # local side effect is opt-in via --out/--out-dir.
        pass
    elif args.out:
        out_path = Path(args.out)
        assert_local_output(out_path, what="--out")
        _write_text_atomic(out_path, line + "\n")
        created = True
    elif args.out_dir:
        out_path = Path(args.out_dir)
        assert_local_output(out_path, what="--out-dir")
        out_path, created = spool_observation(out_path, observation)
    if not args.quiet:
        if args.json:
            print(json.dumps(payload, ensure_ascii=False, indent=2))
        else:
            print(line)
        if out_path is not None:
            print(
                f"# spooled {observation['observation_id']} -> {out_path} "
                f"({'new' if created else 'already present, idempotent no-op'})",
                file=sys.stderr,
            )
        print(f"# post it with: {dashboard_calls(args.ledger)['append_observation']}", file=sys.stderr)
    return 0


def _cli_reduce(args: argparse.Namespace) -> int:
    state_dir = Path(args.state_dir) if args.state_dir else default_state_dir()
    assert_local_output(state_dir, what="state directory")
    base = state_dir / args.ledger
    snapshot_path = Path(args.snapshot) if args.snapshot else base / "snapshots" / "snapshot.json"
    prior = None
    if snapshot_path.exists():
        prior = _read_json(snapshot_path)
    export = None
    if args.events:
        export = _read_json(Path(args.events))
    elif not args.no_events:
        raise LedgerError("MISSING_INPUT", "reduce needs --events <journal export>")
    if args.window_full:
        export = _declare_full_window(export, args.ledger)
    baseline_path = Path(args.baseline) if args.baseline else base / "baseline.json"
    baseline = _read_json(baseline_path) if baseline_path.exists() else None
    config = None
    config_path = state_dir / "config.json"
    if config_path.exists():
        config = _read_json(config_path)
    moment = parse_utc_timestamp(args.now, where="--now") if args.now else None
    result = reduce_ledger(
        ledger=args.ledger,
        export=export,
        prior_snapshot=prior,
        baseline=baseline,
        now=moment,
        config=config,
    )
    rejections = len(result.snapshot["rejections"])
    if args.stdout:
        print(json.dumps(result.summary, ensure_ascii=False, indent=2))
        print(result.status_text, end="")
    elif args.dry_run:
        print(
            f"DRY-RUN: {len(result.snapshot['rows'])} row(s), {rejections} rejection(s), "
            f"nothing written (state dir {state_dir})"
        )
        print(result.status_text, end="")
    else:
        outputs = {
            "--out": Path(args.out) if args.out else snapshot_path,
        }
        if not args.no_summary:
            outputs["--summary-out"] = (
                Path(args.summary_out) if args.summary_out else base / "snapshots" / "summary.json"
            )
        if not args.no_status:
            outputs["--status-out"] = (
                Path(args.status_out) if args.status_out else base / "snapshots" / "status.md"
            )
        for what, path in outputs.items():
            assert_local_output(path, what=what)
        with LedgerLock(base / ".reduce.lock"):
            write_json_atomic(outputs["--out"], result.snapshot)
            if not args.no_summary:
                write_json_atomic(outputs["--summary-out"], result.summary)
            if not args.no_status:
                _write_text_atomic(outputs["--status-out"], result.status_text)
        print(
            f"WROTE {len(result.snapshot['rows'])} row(s), {rejections} rejection(s) "
            f"under {base}"
        )
        print(result.status_text, end="")
    if args.fail_on_rejections and rejections:
        print(f"FAIL: {rejections} observation(s) rejected", file=sys.stderr)
        return 1
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="debt_ledger.py",
        description=(
            "Reducer for the shared append-only debt ledgers "
            "(issue-debt, gpu-reservation). Observations travel "
            "as append-only dashboard messages; this tool only ever writes LOCAL "
            "artifacts."
        ),
    )
    sub = parser.add_subparsers(dest="command", required=True)

    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--state-dir", help="local state dir (never $ROOSYNC_SHARED_PATH)")
    common.add_argument(
        "--now", help="freeze the clock (UTC ISO-8601) for byte-identical, testable output"
    )

    init = sub.add_parser("init", parents=[common], help="create the local ledger tree")
    init.add_argument("--ledger", choices=list(LEDGERS), default=ISSUE_DEBT)
    init.add_argument("--apply", action="store_true", help="write (default is dry-run)")
    init.set_defaults(func=_cli_init)

    append = sub.add_parser("append", parents=[common], help="build one observation envelope")
    append.add_argument("--ledger", choices=list(LEDGERS), required=True)
    append.add_argument("--observation-file", help="read a full observation envelope from JSON")
    append.add_argument(
        "--entity", help="'owner/repo#N', or '<machine>#gpu<n>' for gpu-reservation"
    )
    append.add_argument("--actor", default=os.environ.get("COURSIA_LEDGER_ACTOR", "ai-01"))
    append.add_argument("--observed-at", help="UTC ISO-8601; defaults to now")
    append.add_argument("--confidence", choices=list(CONFIDENCE_LEVELS), default="medium")
    append.add_argument("--evidence", default="manual append")
    append.add_argument("--fields-json", help="JSON object of field values")
    append.add_argument("--note")
    append.add_argument("--out", help="write the envelope to this local file")
    append.add_argument("--out-dir", help="write into this local spool dir")
    append.add_argument("--json", action="store_true", help="emit the MCP call descriptor")
    append.add_argument("--dry-run", action="store_true", help="print only (the default)")
    append.add_argument("--quiet", action="store_true")
    append.set_defaults(func=_cli_append)

    reduce_ = sub.add_parser("reduce", parents=[common], help="fold journal + checkpoint")
    reduce_.add_argument("--ledger", choices=list(LEDGERS), required=True)
    reduce_.add_argument("--events", help="journal export JSON (roosync_dashboard read)")
    reduce_.add_argument("--snapshot", help="prior snapshot (the checkpoint); auto-detected")
    reduce_.add_argument("--baseline", help="baseline JSON; auto-detected")
    reduce_.add_argument("--out")
    reduce_.add_argument("--summary-out")
    reduce_.add_argument("--status-out")
    reduce_.add_argument("--no-summary", action="store_true")
    reduce_.add_argument("--no-status", action="store_true")
    reduce_.add_argument("--no-events", action="store_true", help="fold the checkpoint alone")
    reduce_.add_argument(
        "--window-full",
        action="store_true",
        help="declare the export complete when it omits `window`",
    )
    reduce_.add_argument("--dry-run", action="store_true")
    reduce_.add_argument("--stdout", action="store_true")
    reduce_.add_argument("--fail-on-rejections", action="store_true")
    reduce_.set_defaults(func=_cli_reduce)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except LedgerError as exc:
        print(f"ERROR {exc.reason}: {exc.detail}", file=sys.stderr)
        return 1
    except ObservationError as exc:
        # Defence in depth: a malformed observation is a REJECTION inside the
        # reducer, never a traceback out of an organ the fleet runs on a cron.
        print(f"ERROR {exc.reason}: {exc.detail}", file=sys.stderr)
        return 1


if __name__ == "__main__":  # pragma: no cover - exercised via subprocess in tests
    sys.exit(main())
