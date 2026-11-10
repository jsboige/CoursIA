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
import shutil
import subprocess
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

#: Branche dediee du transport git du ledger (#22456) : un fichier par machine
#: ``gpu-reservation/<machine>.jsonl``, une ligne par observation (format
#: ``envelope_line``), en ajout seul. La branche est la source PRIMAIRE de
#: l'etat de reservation ; le dashboard RooSync en est un MIROIR, et le
#: snapshot local n'est qu'un CACHE, jamais une autorite.
GIT_LEDGER_BRANCH = "ops/gpu-ledger"

#: La REFERENCE du registre des reservations GPU est un depot git PRIVE et
#: dedie : `jsboige/coursia-gpu-ledger` (decision du mainteneur du 2026-10-27,
#: arbitrage rendu sur #22456). Le remote du depot de travail (`origin` =
#: `jsboige/CoursIA`, PUBLIC) ne peut donc plus designer la cible : y publier
#: l'etat GPU de la flotte exposerait des reservations de la flotte dans un
#: depot public. La cible est un PARAMETRE (`--remote`), seul son DEFAUT
#: change -- et le defaut est refuse par une garde si on le redesigne.
GIT_LEDGER_REMOTE_DEFAULT = "gpu-ledger"
#: URL du depot de reference. Elle n'est JAMAIS utilisee automatiquement :
#: chaque siege configure son remote (`git remote add gpu-ledger <url>`),
#: l'authentification passant par le helper `gh` -- jamais par un jeton dans
#: une URL git.
GIT_LEDGER_REPO_URL = "https://github.com/jsboige/coursia-gpu-ledger.git"
#: Cibles explicitement refusees (fail-CLOSED) : le depot de travail, public.
GIT_LEDGER_FORBIDDEN_TARGETS: tuple[str, ...] = ("jsboige/coursia",)

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

#: Roster des machines de la flotte (#21580). La liste est FIGEE ici : un organe
#: appele en CI ne peut pas deriver une liste de fichiers au runtime. Une machine
#: hors de ce roster est REFUSEE, jamais acceptee telle quelle -- c'est la seule
#: garantie qu'une faute de frappe ne cree pas une ligne fantome dans le registre.
#:
#: Contenu = la flotte MyIA entiere (9 machines), et non seulement les sept
#: machines que portent les deux listes internes (``gh_identity.HOST_ACCOUNTS`` et
#: ``secrets/agent_keyring.FLEET_MACHINES``, qui n'ont pas encore ``po-2028`` ni
#: ``web2``) : le ledger doit pouvoir accepter une observation de *n'importe*
#: machine reelle de la flotte, y compris une lane qui travaille hors CoursIA.
#: Les listes internes rattraperont ce decalage ; le gesture ici est de ne pas
#: refuser une machine qui existe.
FLEET_MACHINES: frozenset[str] = frozenset(
    {
        "myia-ai-01",
        "myia-po-2023",
        "myia-po-2024",
        "myia-po-2025",
        "myia-po-2026",
        "myia-po-2027",
        "myia-po-2028",
        "myia-web1",
        "myia-web2",
    }
)

#: Alias acceptes -> nom canonique. Le nom court (prefixe ``myia-`` retire) est
#: derive MECANIQUEMENT du roster : c'est la seule forme d'alias verifiable, et
#: c'est celle que la regle de protocole demande ("le nom du roster"). Les
#: formes sans tiret sont ajoutees a la main.
MACHINE_ALIASES: dict[str, str] = {
    **{
        name[len("myia-") :]: name
        for name in FLEET_MACHINES
        if name.startswith("myia-")
    },
    "ai01": "myia-ai-01",
    "ai-1": "myia-ai-01",
    "web-1": "myia-web1",
    "web-2": "myia-web2",
}


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


_OBSERVATION_DIGEST_ID_RE = re.compile(r"^obs-[0-9a-f]{16}$")


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


def canonical_machine(raw: Any) -> str:
    """The canonical machine name of the fleet, or an explicit refusal (#21580).

    The machine part of a reservation key was free text: two spellings of the
    same machine (``ai-01`` and ``myia-ai-01``) produced two rows that never
    locked against each other -- and the lock is the whole point of a GPU
    reservation. The refusal is explicit rather than lenient: a name outside
    the roster is a typo, not a new machine.
    """
    if not isinstance(raw, str):
        raise ObservationError("entity_mismatch", f"machine={raw!r} is not a machine name")
    name = raw.strip().lower()
    if name in FLEET_MACHINES:
        return name
    canonical = MACHINE_ALIASES.get(name)
    if canonical is not None:
        return canonical
    raise ObservationError(
        "entity_mismatch",
        f"machine={raw!r} is not a fleet machine "
        f"(known: {', '.join(sorted(FLEET_MACHINES))})",
    )


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
    # Canonical machine name (#21580): the row identity must not depend on the
    # spelling, or two lanes reserve the same card without ever colliding.
    return {"machine": canonical_machine(machine), "gpu_index": index}


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


_PULL_URL_RE = re.compile(r"/pull/([1-9][0-9]*)")


def _entity_is_pr(evidence: str, entity: dict[str, Any]) -> bool:
    """True si l'evidence cite une URL ``/pull/<N>`` pour le N de l'entite.

    Issues et PRs partagent l'espace de numerotation GitHub : un ``/pull/<N>``
    portant le numero de l'entite prouve que l'entite EST une PR. Le ledger
    ``issue-debt`` s'est fait coloniser par des etats de PR (#17956 point 6) --
    l'etat d'une PR vit dans son dossier exact-head, pas ici.
    """
    if "issue" not in entity:
        return False
    n = entity["issue"]
    return any(int(m) == n for m in _PULL_URL_RE.findall(evidence))


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
    warnings: list[str] | None = None,
) -> dict[str, Any]:
    """Validate one observation envelope and return its canonical form.

    ``defaults`` supplies the fields a journal message carries outside the
    envelope (``actor`` from the message author, ``observed_at`` from its
    timestamp, ``message_id`` from its id) and the baseline header defaults.
    Un identifiant manuscrit est re-clé sur l'empreinte du contenu ; lorsque
    ``warnings`` est fourni, le re-cléage y est consigné au lieu de passer
    inaperçu. Une empreinte déclarée mais différente reste refusée.
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

    if ledger == ISSUE_DEBT and _entity_is_pr(evidence, entity):
        raise ObservationError(
            "entity_is_pr",
            f"entity {entity_key(entity)} is a pull request -- PR state lives in its "
            "exact-head dossier, not in the issue-debt ledger (#17956 point 6)",
        )

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
        # An observation posted BEFORE the machine-name canonicalisation (#21580)
        # carries the digest of its RAW entity ("ai-01#gpu2"); the canonical
        # entity now digests differently. That is not a tampered journal -- it
        # is the same content, re-keyed -- so the raw digest is accepted and
        # the CANONICAL entity is kept: the row identity converges and the
        # historical observation is not silently discarded by the fail-closed
        # check below.
        legacy = _legacy_observation_id(observation, raw.get("entity"), ledger)
        if legacy is not None and declared_id == legacy:
            observation["observation_id"] = computed
            return observation
        if not isinstance(declared_id, str) or not _OBSERVATION_DIGEST_ID_RE.fullmatch(
            declared_id
        ):
            # Un libellé manuscrit ne prétend pas être une empreinte : le contenu
            # reste vérifiable et sa nouvelle clé converge entre toutes les lanes.
            # Conserver le re-cléage dans les avertissements évite qu'il soit muet.
            observation["observation_id"] = computed
            if warnings is not None:
                warnings.append(
                    "observation_id_rekeyed: "
                    f"declared {declared_id!r} is not digest-shaped; "
                    f"re-keyed to {computed!r}"
                )
            return observation
        # Une empreinte bien formée mais différente accuse un autre contenu :
        # c'est le cas de falsification que la garantie append-only refuse.
        raise ObservationError(
            "observation_id_mismatch",
            f"declared {declared_id!r} but content digests to {computed!r}",
        )
    observation["observation_id"] = computed
    return observation


def _legacy_observation_id(
    observation: dict[str, Any], raw_entity: Any, ledger: str
) -> str | None:
    """The digest an observation would have had BEFORE canonicalisation (#21580).

    Only the GPU ledger has a canonicalised field (the machine name); for every
    other ledger the answer is ``None`` -- there is no legacy form to accept, so
    the fail-closed check stays exactly as strict as it was.
    """
    if ledger != GPU_RESERVATION or not isinstance(raw_entity, dict):
        return None
    machine = raw_entity.get("machine")
    index = raw_entity.get("gpu_index")
    if not isinstance(machine, str) or not isinstance(index, int) or isinstance(index, bool):
        return None
    legacy = dict(observation)
    legacy["entity"] = {"machine": machine.strip(), "gpu_index": index}
    if legacy["entity"] == observation["entity"]:
        return None
    return observation_id_for(legacy)


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


#: Verdict constants for check_pending (gpu-reservation).
#: OK_TO_RUN: a `held` observation by `my_lane`, with now in the run window.
#: NO_OBS: no record for the entity -- the picker should NOT run a workload there.
#: HOLD: `held` by a different lane, or `held` by us but outside the run window.
#: RELEASED: terminal state -- the workload ended; the GPU is free to take.
#: STALE: `held` past expected_end with no release; needs a follow-up observation.
GPU_PENDING_VERDICTS: tuple[str, ...] = ("OK_TO_RUN", "NO_OBS", "HOLD", "RELEASED", "STALE")

#: Verdicts rendus par la GATE elle-meme, avant toute lecture du snapshot.
#: UNREADABLE_SPOOL : un fichier de l'outbox est illisible ; il peut porter une
#: reservation, donc le ledger est illisible, pas libre.
#: UNPOSTED : l'outbox porte des observations qui n'ont jamais atteint le
#: dashboard ; un verdict reduit d'un snapshot ne voit pas ce qui n'a pas voyag.
VERDICT_UNREADABLE_SPOOL = "UNREADABLE_SPOOL"
VERDICT_UNPOSTED = "UNPOSTED"
VERDICT_UNREADABLE = "UNREADABLE"
GPU_GATE_VERDICTS: tuple[str, ...] = (
    VERDICT_UNREADABLE_SPOOL,
    VERDICT_UNPOSTED,
    VERDICT_UNREADABLE,
)

#: Code de sortie par verdict -- source unique, reprise telle quelle par le
#: tableau de ``docs/coordination/gpu-reservation.md``. Un verdict qui refuse
#: porte 1, un etat perime porte 2 (l'appelant decide), un verdict neutre 0.
GPU_VERDICT_EXIT_CODES: dict[str, int] = {
    "OK_TO_RUN": 0,
    "NO_OBS": 0,
    "RELEASED": 0,
    "HOLD": 1,
    VERDICT_UNREADABLE_SPOOL: 1,
    VERDICT_UNPOSTED: 1,
    VERDICT_UNREADABLE: 1,
    "STALE": 2,
}


def evaluate_gpu_pending(
    records: list,
    entity: dict,
    now,
    my_lane,
):
    """Return (verdict, reason) for a gpu-reservation entity.

    The verdict is one of GPU_PENDING_VERDICTS; the reason is a one-line
    human-readable explanation that names the dominant input (e.g. the
    holder, the expected_end, or the absence of a record).

    The function is pure -- no IO, no clock, no shared state -- so a test
    or a pre-launch gate can call it with a fixed `now` and a list of
    records read from the snapshot. Callers that want to walk the
    fold-from-snapshot first use ``records_from_snapshot``.

    `my_lane` may be None: in that case, a `held` record is always reported
    as HOLD (no ownership can be proven), and OK_TO_RUN is never returned.
    This is the safe default for a caller that is not yet sure it owns the
    device. Likewise, a `held` record WITHOUT a holder is HOLD for every
    caller: nobody can prove it owns that window.
    """
    # Filter records to this entity, newest observed_at first.
    matching = []
    for record in records:
        record_entity = record.entity
        if record_entity.get("machine") != entity.get("machine"):
            continue
        if str(record_entity.get("gpu_index")) != str(entity.get("gpu_index")):
            continue
        matching.append(record)
    matching.sort(key=lambda r: r.observed_at, reverse=True)

    if not matching:
        return ("NO_OBS", f"no record for {entity.get('machine')}#gpu{entity.get('gpu_index')}")

    latest = matching[0]
    fields = latest.fields
    state = fields.get("state")
    holder = fields.get("holder")
    started_at_raw = fields.get("started_at")
    expected_end_raw = fields.get("expected_end")

    if state == "released":
        return ("RELEASED", f"last state=released at {latest.observed_at.isoformat()} by {holder}")

    if state == "stale":
        return ("STALE", f"last state=stale at {latest.observed_at.isoformat()} by {holder}")

    if state != "held":
        return ("HOLD", f"unknown state={state!r} at {latest.observed_at.isoformat()}")

    # state == "held" -- ownership FIRST, then the window.
    #
    # OK_TO_RUN is reserved to the holder: it needs a NAMED caller and a
    # named holder equal to it. The former predicate (`my_lane is not None
    # and holder is not None and holder != my_lane`) let both unnamed cases
    # fall through to the window checks and end in OK_TO_RUN -- a caller
    # that did not say who it was was admitted onto a device held by another
    # lane, against the contract stated above (PR #22755, Hermes finding 1).
    if my_lane is None:
        return (
            "HOLD",
            f"held by {holder} at {latest.observed_at.isoformat()} -- no calling "
            "lane given (--my-lane): ownership cannot be proven, never OK_TO_RUN",
        )
    if holder != my_lane:
        return ("HOLD", f"held by {holder} (not {my_lane}) at {latest.observed_at.isoformat()}")

    if started_at_raw is not None:
        try:
            started_at = parse_utc_timestamp(started_at_raw, where="started_at")
        except ObservationError as exc:
            return ("HOLD", f"unparseable started_at={started_at_raw!r}: {exc.detail}")
        if now < started_at:
            return ("HOLD", f"held by {holder}, window starts at {started_at.isoformat()}")

    if expected_end_raw is not None:
        try:
            expected_end = parse_utc_timestamp(expected_end_raw, where="expected_end")
        except ObservationError as exc:
            return ("HOLD", f"unparseable expected_end={expected_end_raw!r}: {exc.detail}")
        if now > expected_end:
            return ("STALE", f"held by {holder}, expected_end {expected_end.isoformat()} passed")

    return ("OK_TO_RUN", f"held by {holder} (= calling lane), now={now.isoformat()}")


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


def record_views_from_snapshot(snapshot: dict[str, Any], ledger: str) -> list[Record]:
    """One record per row, carrying that row's FULL current field set.

    ``records_from_snapshot`` emits one record per (field, history entry) -- the
    right grain to re-fold a checkpoint without losing provenance, and the wrong
    grain for a verdict. ``evaluate_gpu_pending`` reads ``state``, ``holder``,
    ``started_at`` and ``expected_end`` off ONE record; fed per-field records it
    sees a single key, so ``holder`` is always ``None``, the ownership branch
    cannot fire, and the gate answers ``OK_TO_RUN`` to every lane (#20077).

    The row already holds the merged view, so take it whole and date it by the
    newest provenance entry it carries.
    """
    records: list[Record] = []
    for row in snapshot.get("rows", []):
        try:
            entity = _validate_entity(row.get("entity"), ledger)
        except ObservationError:
            continue  # a corrupt row is dropped, never allowed to poison a verdict
        fields = row.get("fields")
        if not isinstance(fields, dict) or not fields:
            continue
        provenance = row.get("provenance") or {}
        observed_at: str | None = None
        actor, confidence, evidence = "snapshot", "medium", "snapshot row"
        for name in fields:
            entry = provenance.get(name)
            if not isinstance(entry, dict):
                continue
            stamp = entry.get("observed_at")
            if isinstance(stamp, str) and (observed_at is None or stamp > observed_at):
                observed_at = stamp
                actor = str(entry.get("actor") or actor)
                confidence = str(entry.get("confidence") or confidence)
                evidence = str(entry.get("evidence") or evidence)
        if observed_at is None:
            # The row carries a current state but nothing dates it; an undated
            # record cannot be ordered against the others, so drop it rather
            # than invent a stamp that would win or lose the sort by accident.
            continue
        raw_observation = {
            "schema": OBSERVATION_SCHEMA,
            "ledger": ledger,
            "actor": actor,
            "observed_at": observed_at,
            "confidence": confidence,
            "evidence": evidence,
            "entity": dict(entity),
            "fields": dict(fields),
        }
        try:
            observation = parse_observation(raw_observation, ledger)
        except ObservationError:
            continue  # a row that no longer validates is dropped, not merged
        records.append(record_from_observation(observation, "snapshot"))
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


def parse_journal_export(
    raw: Any,
    ledger: str,
    *,
    warnings: list[str] | None = None,
) -> tuple[dict[str, Any], list[Record], list[dict]]:
    """Parse an export into ``(window, records, rejections)``.

    ``warnings`` reçoit notamment les re-cléages d'identifiants manuscrits ;
    le tuple de retour et la politique de rejet restent inchangés.
    """
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
            observation = parse_observation(
                parse_envelope(content), ledger, defaults=defaults, warnings=warnings
            )
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
        window, journal_records, rejections = parse_journal_export(
            export, ledger, warnings=warnings
        )

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


def _read_spool_envelope(path: Path) -> tuple[dict[str, Any] | None, str | None]:
    """Lire une enveloppe sans qu'un seul fichier bloque tout le spool.

    Le couple ``(enveloppe, motif)`` contient exactement une valeur non nulle.
    Un mauvais ``ledger`` ou un ``observation_id`` absent rend le fichier
    illisible pour TOUS les consommateurs : il ne peut pas être compté comme
    en attente ni publié, mais son motif reste visible via ``spool_unreadable``.
    """
    try:
        observation = parse_envelope(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, ObservationError) as exc:
        return None, str(exc)
    ledger = observation.get("ledger")
    if ledger not in LEDGERS:
        return None, "missing or unknown ledger"
    if not observation.get("observation_id"):
        return None, "missing observation_id"
    return observation, None


def _scan_spool(spool_dir: Path) -> list[tuple[Path, dict[str, Any] | None, str | None]]:
    """Le scan unique et trié partagé par les lectures du spool."""
    if not spool_dir.exists():
        return []
    return [
        (path, *_read_spool_envelope(path))
        for path in sorted(spool_dir.glob("*.json"))
        if not path.name.startswith(".superseded-")
    ]


def spool_unreadable(spool_dir: Path) -> list[dict[str, str]]:
    """Fichiers du spool illisibles, avec leur chemin et leur motif.

    Ces fichiers restent sur disque : les écarter de l'index de publication ne
    les supprime pas et préserve la trace exigée par #22456.
    """
    return [
        {"path": str(path), "reason": reason or "unknown reason"}
        for path, _observation, reason in _scan_spool(spool_dir)
        if reason is not None
    ]


def spool_status(spool_dir: Path) -> dict[str, dict[str, Any]]:
    """Compter les enveloppes lisibles, sans masquer les fichiers illisibles.

    La forme de retour reste strictement ``{ledger: {pending, oldest...}}`` ;
    ``spool_unreadable`` porte séparément le diagnostic des fichiers écartés.
    """
    oldest: dict[str, datetime | None] = {ledger: None for ledger in LEDGERS}
    counts = dict.fromkeys(LEDGERS, 0)
    for path, observation, reason in _scan_spool(spool_dir):
        if reason is not None:
            continue
        assert observation is not None
        ledger = observation["ledger"]
        try:
            moment = parse_utc_timestamp(observation.get("observed_at"))
        except ObservationError:
            try:
                moment = datetime.fromtimestamp(path.stat().st_mtime, timezone.utc)
            except OSError as exc:
                raise LedgerError("UNREADABLE_INPUT", f"{path}: {exc}") from exc
        counts[ledger] += 1
        if oldest[ledger] is None or moment < oldest[ledger]:
            oldest[ledger] = moment
    return {
        ledger: {
            "pending": counts[ledger],
            "oldest_observed_at": format_utc(oldest[ledger]) if oldest[ledger] else None,
        }
        for ledger in LEDGERS
    }


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


def spool_pending(spool_dir: Path, *, ledger: str) -> list[dict[str, Any]]:
    """Enveloppes lisibles de ``ledger``, de la plus ancienne à la plus récente.

    ``spool_status`` répond « combien » et cette fonction « lesquelles », avec
    le même scan et les mêmes critères. Un fichier illisible n'est pas publiable
    et n'interrompt plus le lot ; son chemin et son motif sont rapportés par
    ``spool_unreadable`` afin qu'aucune observation ne disparaisse sans trace.
    """
    pending: list[dict[str, Any]] = []
    for path, observation, reason in _scan_spool(spool_dir):
        if reason is not None:
            continue
        assert observation is not None
        if observation["ledger"] != ledger:
            continue
        try:
            moment = parse_utc_timestamp(observation.get("observed_at"))
        except ObservationError:
            try:
                moment = datetime.fromtimestamp(path.stat().st_mtime, timezone.utc)
            except OSError as exc:
                raise LedgerError("UNREADABLE_INPUT", f"{path}: {exc}") from exc
        pending.append({"path": path, "moment": moment, "observation": observation})
    pending.sort(key=lambda item: (item["moment"], item["observation"]["observation_id"]))
    return pending


def flush_manifest(ledger: str, pending: Sequence[dict[str, Any]]) -> dict[str, Any]:
    """The postable batch: one dashboard ``content`` per pending observation.

    ``content`` is byte-identical to the spool file, so what an agent posts is
    what the organ wrote -- no re-serialisation step where a field can drift.
    """
    return {
        "ledger": ledger,
        "workspace": LEDGER_WORKSPACES[ledger],
        "count": len(pending),
        "calls": [
            {
                "observation_id": item["observation"]["observation_id"],
                "observed_at": format_utc(item["moment"]),
                "content": envelope_line(item["observation"]),
            }
            for item in pending
        ],
    }


def _index_spool(directory: Path, *, strict: bool) -> dict[str, Path]:
    """Map observation id -> envelope file, for BOTH keying conventions.

    ``flush_manifest`` publie l'``observation_id`` de l'enveloppe ; le nom du
    fichier est une seconde convention, plus ancienne. Les deux sont indexés,
    en donnant priorité à l'identifiant déclaré par l'enveloppe.

    Le côté EN ATTENTE n'échoue plus pour un seul fichier illisible : celui-ci
    n'est simplement pas publiable. Sa trace est préservée parce que le fichier
    reste sur disque et que ``spool_unreadable`` rapporte son chemin et son
    motif. ``strict=True`` conserve son refus explicite pour un appelant qui
    demande ce mode ; ``archive_posted`` choisit ``strict=False`` des deux
    côtés afin que l'archivage des bonnes enveloppes reste possible. Le côté
    ARCHIVE reste tolérant comme auparavant (#22456).
    """
    index: dict[str, Path] = {}
    scanned = _scan_spool(directory)
    for path, _observation, reason in scanned:
        if reason is None:
            index[path.stem] = path
    for path, observation, reason in scanned:
        if reason is not None and strict:
            raise LedgerError("INVALID_SPOOL", f"{path}: {reason}")
        if reason is None:
            assert observation is not None
            index[str(observation["observation_id"])] = path
    return index


def archive_posted(spool_dir: Path, observation_ids: Sequence[str]) -> dict[str, list[str]]:
    """Move posted envelopes out of the pending set; idempotent by id.

    All-or-nothing: an unknown id refuses the whole call rather than
    archiving half a batch, because a partially drained outbox is exactly the
    state that makes ``check_pending`` lie.
    """
    posted_dir = spool_dir / "posted"
    pending_index = _index_spool(spool_dir, strict=False)
    posted_index = _index_spool(posted_dir, strict=False)
    moved: list[str] = []
    already: list[str] = []
    missing: list[str] = []
    plan: dict[str, Path] = {}
    for observation_id in observation_ids:
        source = pending_index.get(observation_id)
        if source is not None:
            plan.setdefault(observation_id, source)
        elif observation_id in posted_index:
            already.append(observation_id)
        else:
            missing.append(observation_id)
    if missing:
        raise LedgerError(
            "UNKNOWN_OBSERVATION",
            "no pending or posted envelope for: " + ", ".join(sorted(set(missing))),
        )
    for observation_id, source in plan.items():
        posted_dir.mkdir(parents=True, exist_ok=True)
        os.replace(source, posted_dir / source.name)
        moved.append(observation_id)
    return {"moved": moved, "already": already}


_NOW_SENTINEL = re.compile(r"^now\s*(?:([+-])\s*(\d+)\s*([mh]))?$")


def resolve_now_sentinels(fields: dict[str, Any], *, moment: datetime) -> dict[str, Any]:
    """Resolve ``now`` / ``now+30m`` / ``now-2h`` in hold timestamps.

    The 2026-10-25 skew (#22456) came from a caller formatting its own clock:
    a local time labelled ``Z`` is well-formed, so nothing downstream can
    detect it. The organ offers the alternative -- it writes the stamp itself
    from an aware ``moment`` -- so no caller has a reason to format one.
    """
    resolved = dict(fields)
    for name in ("started_at", "expected_end"):
        value = resolved.get(name)
        if not isinstance(value, str):
            continue
        match = _NOW_SENTINEL.match(value.strip())
        if match is None:
            continue
        sign, amount, unit = match.groups()
        delta = timedelta(0)
        if sign is not None:
            delta = timedelta(minutes=int(amount)) if unit == "m" else timedelta(hours=int(amount))
            if sign == "-":
                delta = -delta
        resolved[name] = format_utc(moment + delta)
    return resolved


# ---------------------------------------------------------------------------
# 10bis. GIT TRANSPORT -- la branche dediee ops/gpu-ledger (#22456)
# ---------------------------------------------------------------------------
#
# Le dashboard RooSync suppose le MCP roo-state-manager disponible : sans lui,
# personne ne peut lire l'etat de reservation, et le gate d'admission GPU
# devient aveugle. La branche dediee est le transport SANS DEPENDANCE : chaque
# machine publie ses enveloppes (un fichier ``gpu-reservation/<machine>.jsonl``,
# une ligne par observation, ajout seul), tout le monde lit par ``git show``.
# La branche est la source PRIMAIRE ; le dashboard reste un MIROIR de la
# publication ; le snapshot local reste un CACHE, jamais une autorite.
# Aucun jeton dans une URL git : l'identite est celle, ambiante, de la machine
# (la config git du depot).


def _git(args: Sequence[str], *, cwd: Path) -> tuple[int, str, str]:
    """Run git in ``cwd``; ``(returncode, stdout, stderr)``, never raises."""
    try:
        proc = subprocess.run(
            ["git", *args],
            cwd=str(cwd),
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
    except OSError as exc:  # git absent du PATH : echec explicite, pas de crash
        return 127, "", str(exc)
    return proc.returncode, proc.stdout or "", proc.stderr or ""


def default_repo_root() -> Path | None:
    """Le depot git qui porte ce script (jamais un chemin en dur)."""
    rc, out, _ = _git(
        ["rev-parse", "--show-toplevel"], cwd=Path(__file__).resolve().parent
    )
    if rc != 0 or not out.strip():
        return None
    return Path(out.strip())


def _tracking_ref(remote: str) -> str:
    return f"refs/remotes/{remote}/{GIT_LEDGER_BRANCH}"


def _normalise_repo_slug(url: str) -> str:
    """Slug ``owner/repo`` d'une URL git, pour comparer deux cibles.

    Accepte les formes https, ssh (``git@github.com:owner/repo.git``) et
    ``ssh://`` ; le resultat est compare en minuscules.
    """
    text = url.strip().rstrip("/")
    if text.endswith(".git"):
        text = text[: -len(".git")]
    if text.startswith("git@"):
        text = text[len("git@") :]
        text = text.replace(":", "/", 1)
    else:
        for prefix in ("https://", "http://", "ssh://", "git://"):
            if text.startswith(prefix):
                text = text[len(prefix) :]
                break
    parts = [part for part in text.split("/") if part]
    if len(parts) >= 2:
        return "/".join(parts[-2:]).lower()
    return text.lower()


def _git_remote_urls(repo: Path, remote: str) -> tuple[str, str]:
    """Les DEUX URL d'un remote : celle de fetch et celle de push.

    ``git remote get-url`` rend l'URL de **fetch** ; ``git push`` utilise la
    ``pushurl`` quand elle est definie. Une garde qui ne regarde que la
    premiere ne voit donc jamais la cible reelle d'ecriture -- et le refus
    qu'elle prononce porte sur un depot qui n'est pas celui qui recevra la
    poussee. Les deux sont donc resolues ici.

    Renvoie ``("", "")`` si le remote n'est pas configure.
    """
    rc, fetch_url, _ = _git(["remote", "get-url", remote], cwd=repo)
    if rc != 0 or not fetch_url.strip():
        return "", ""
    push_url = fetch_url.strip()
    rc_push, pushed, _ = _git(["remote", "get-url", "--push", remote], cwd=repo)
    if rc_push == 0 and pushed.strip():
        push_url = pushed.strip()
    return fetch_url.strip(), push_url


def ensure_git_ledger_remote(repo: Path, remote: str) -> str:
    """Resout la cible de publication ; refuse la cible interdite.

    Le remote doit etre **configure sur le siege** : l'organe ne le cree
    pas tout seul, parce qu'ecrire dans un depot partage ne doit pas
    dependre d'un effet de bord d'une commande de lecture ou de test. Un
    remote absent est donc un refus nomme, porteur du geste exact.

    Une cible qui designerait le depot de travail **public** est refusee
    (fail-CLOSED) : le registre des reservations GPU ne sort pas d'un depot
    public, quel que soit le `--remote` passe. Les **deux** URL du remote
    sont verifiees (fetch et push) : c'est la ``pushurl`` qui porte la
    cible reelle d'ecriture, une URL de fetch privee ne dit rien d'elle.
    """
    fetch_url, push_url = _git_remote_urls(repo, remote)
    if not fetch_url:
        raise LedgerError(
            "GIT_LEDGER_REMOTE_UNKNOWN",
            f"remote git {remote!r} non configure dans {repo} ; la reference du "
            f"registre GPU est le depot PRIVE "
            f"git remote add {remote} {GIT_LEDGER_REPO_URL}",
        )
    for label, url in (("fetch", fetch_url), ("push", push_url)):
        slug = _normalise_repo_slug(url)
        if slug in GIT_LEDGER_FORBIDDEN_TARGETS:
            raise LedgerError(
                "GIT_LEDGER_FORBIDDEN_TARGET",
                f"la cible de publication {slug!r} (URL de {label}) est "
                "interdite : le registre des reservations GPU ne se publie pas "
                "dans le depot de travail (public) ; reference attendue : "
                f"{GIT_LEDGER_REMOTE_DEFAULT} -> {GIT_LEDGER_REPO_URL}",
            )
    return fetch_url


def _git_reason(stderr: str) -> str:
    """La premiere ligne utile d'un stderr git, bornée (jamais un dump)."""
    return " ".join(stderr.split())[:200]


def fetch_git_ledger_branch(
    repo: Path, *, remote: str = GIT_LEDGER_REMOTE_DEFAULT
) -> str | None:
    """Fetch de la branche dediee ; ``None`` si reussi, sinon la raison.

    Ce que vaut un echec depend de l'appelant. La publication peut continuer :
    un ref de suivi perime y produit au pire une poussee refusee (non
    fast-forward), jamais une perte. Le gate ``check_pending``, lui, refuse
    (UNREADABLE) : un ref perime ne peut pas autoriser un lancement.
    """
    rc, _, err = _git(
        ["fetch", "--quiet", remote, f"+refs/heads/{GIT_LEDGER_BRANCH}:{_tracking_ref(remote)}"],
        cwd=repo,
    )
    if rc == 0:
        return None
    return _git_reason(err) or f"git fetch {remote} {GIT_LEDGER_BRANCH} a echoue"


def _branche_absente_du_remote(repo: Path, *, remote: str) -> bool:
    """La branche dediee n'existe-t-elle pas ENCORE sur le remote ?

    Distinguer par une interrogation du remote (``ls-remote``), **jamais par
    le TEXTE de stderr** : ce texte est localise et sa formulation change
    d'une version de git a l'autre. Un remote joignable dont la liste est
    VIDE veut dire « la branche n'existe pas encore » -- cas normal de la
    premiere publication d'une machine, et non une panne.

    Un remote injoignable (rc != 0) ne prouve rien : la reponse est False,
    et l'appelant garde le motif du fetch.
    """
    rc, out, _ = _git(
        ["ls-remote", remote, f"refs/heads/{GIT_LEDGER_BRANCH}"], cwd=repo
    )
    return rc == 0 and not out.strip()


def git_ledger_ref_available(
    repo: Path, *, remote: str = GIT_LEDGER_REMOTE_DEFAULT
) -> bool:
    """La branche dediee est-elle lisible localement (ref de suivi present) ?"""
    rc, _, _ = _git(
        ["rev-parse", "--verify", "--quiet", _tracking_ref(remote)], cwd=repo
    )
    return rc == 0


def read_git_ledger_files(
    repo: Path, *, remote: str = GIT_LEDGER_REMOTE_DEFAULT
) -> dict[str, str]:
    """Contenu brut ``{machine: texte}`` des fichiers gpu-reservation de la branche."""
    ref = _tracking_ref(remote)
    if not git_ledger_ref_available(repo, remote=remote):
        raise LedgerError(
            "GIT_LEDGER_UNAVAILABLE",
            f"{ref} absent (branche jamais publiee, ou remote injoignable)",
        )
    rc, out, err = _git(["ls-tree", "-r", "--name-only", ref], cwd=repo)
    if rc != 0:
        raise LedgerError("GIT_LEDGER_UNAVAILABLE", f"ls-tree {ref} : {_git_reason(err)}")
    prefix = f"{GPU_RESERVATION}/"
    files: dict[str, str] = {}
    for rel in out.splitlines():
        rel = rel.strip()
        if not rel.startswith(prefix) or not rel.endswith(".jsonl"):
            continue
        machine = rel[len(prefix) : -len(".jsonl")]
        if not machine:
            continue
        rc_show, content, err_show = _git(["show", f"{ref}:{rel}"], cwd=repo)
        if rc_show != 0:
            raise LedgerError(
                "GIT_LEDGER_UNAVAILABLE",
                f"git show {ref}:{rel} : {_git_reason(err_show)}",
            )
        files[machine] = content
    return files


def observations_from_git_ledger(
    repo: Path, *, remote: str = GIT_LEDGER_REMOTE_DEFAULT
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """``(observations, rejets)`` lus de la branche ; une ligne invalide est un
    rejet nomme, jamais un crash du lecteur (meme discipline que le journal)."""
    observations: list[dict[str, Any]] = []
    rejections: list[dict[str, Any]] = []
    for machine, content in sorted(read_git_ledger_files(repo, remote=remote).items()):
        for index, line in enumerate(content.splitlines()):
            line = line.strip()
            if not line:
                continue
            label = f"{GIT_LEDGER_BRANCH}:{GPU_RESERVATION}/{machine}.jsonl[{index}]"
            try:
                observation = parse_observation(parse_envelope(line), GPU_RESERVATION)
            except ObservationError as exc:
                rejections.append(
                    {"source": label, "reason": exc.reason, "detail": exc.detail}
                )
                continue
            observations.append(observation)
    return observations, rejections


def _publishable_observations(spool_dir: Path, *, ledger: str) -> list[dict[str, Any]]:
    """Source de publication : spool PENDING + archives ``posted``, dedupliquees
    par ``observation_id`` et triees par horodatage.

    Les archives repostent ce que le depot distant pourrait avoir purge ; la
    deduplication par id fait qu'une republication n'ajoute jamais de ligne.
    """
    merged: dict[str, dict[str, Any]] = {}
    for item in spool_pending(spool_dir, ledger=ledger):
        merged[str(item["observation"]["observation_id"])] = item["observation"]
    posted_dir = spool_dir / "posted"
    if posted_dir.exists():
        for path in sorted(posted_dir.glob("*.json")):
            if path.name.startswith(".superseded-"):
                continue
            try:
                archived = parse_envelope(path.read_text(encoding="utf-8"))
            except (OSError, UnicodeError, ObservationError):
                continue  # une archive endommagee ne doit pas bloquer le transport
            if (
                isinstance(archived, dict)
                and archived.get("ledger") == ledger
                and archived.get("observation_id")
            ):
                merged.setdefault(str(archived["observation_id"]), archived)
    return sorted(
        merged.values(),
        key=lambda obs: (str(obs.get("observed_at", "")), str(obs.get("observation_id", ""))),
    )


def _pin_ledger_base(repo: Path, *, remote: str) -> str | None:
    """Le sha du ref de suivi, resolu UNE SEULE fois ; ``None`` s'il est absent.

    Une tentative de publication lit tout depuis CE sha -- le texte du
    fichier, l'index, et le parent du commit. Resoudre le ref a plusieurs
    moments laissait un autre publieur du meme depot le deplacer entre deux
    lectures (finding Hermes 2 de la PR #22755) : le commit recevait pour
    parent la nouvelle tete mais l'ancien fichier, la poussee etait un
    fast-forward, et la ligne de l'autre publieur disparaissait en silence.
    """
    rc, out, _ = _git(
        ["rev-parse", "--verify", "--quiet", f"{_tracking_ref(remote)}^{{commit}}"],
        cwd=repo,
    )
    sha = out.strip()
    if rc != 0 or not sha:
        return None
    return sha


def _branch_file_text(
    repo: Path, rel: str, *, remote: str, rev: str | None = None
) -> str:
    """Contenu d'un fichier de la branche ; ``''`` s'il n'existe pas.

    ``rev`` : le commit a lire (un sha epingle par `_pin_ledger_base`) ; a
    defaut, le ref de suivi tel qu'il est a l'instant de la lecture.
    """
    ref = rev if rev is not None else _tracking_ref(remote)
    # L'absence du fichier est detectee par le CODE DE SORTIE de `cat-file -e`,
    # jamais par le TEXTE de stderr : ce texte est LOCALISE (gettext), et une
    # sous-chaine "does not exist" echouerait sur un siege francais -- la
    # premiere publication d'une machine y echouerait systematiquement.
    rc, _, err = _git(["cat-file", "-e", f"{ref}:{rel}"], cwd=repo)
    if rc != 0:
        # rc != 0 : le fichier est absent OU le ref est illisible. On
        # distingue les deux -- un ref illisible est une panne, pas une absence.
        rc_ref, _, _ = _git(["rev-parse", "--verify", "--quiet", ref], cwd=repo)
        if rc_ref != 0:
            raise LedgerError(
                "GIT_LEDGER_UNAVAILABLE",
                f"ref {ref} illisible : {_git_reason(err)}",
            )
        return ""
    rc, out, err = _git(["show", f"{ref}:{rel}"], cwd=repo)
    if rc == 0:
        return out
    raise LedgerError(
        "GIT_LEDGER_UNAVAILABLE", f"git show {ref}:{rel} : {_git_reason(err)}"
    )


def _published_ids(text: str) -> set[str]:
    """Les ``observation_id`` d'un fichier de branche (lignes invalides ignorees)."""
    ids: set[str] = set()
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            parsed = parse_envelope(line)
        except ObservationError:
            continue
        if isinstance(parsed, dict) and parsed.get("observation_id"):
            ids.add(str(parsed["observation_id"]))
    return ids


def _ids_at(repo: Path, rev: str, rel: str, *, remote: str) -> set[str]:
    """Les ``observation_id`` du fichier ``rel`` tel que le porte ``rev``."""
    return _published_ids(_branch_file_text(repo, rel, remote=remote, rev=rev))


def _publish_attempt(
    *,
    repo: Path,
    rel: str,
    canonical: str,
    ledger: str,
    remote: str,
    to_publish: list[dict[str, Any]],
    base_sha: str | None,
) -> str | None:
    """Un cycle worktree -> commit -> push ; retourne le sha pousse, ``None`` si
    le push est rejete (l'appelant a droit a UN retry).

    ``base_sha`` est la tete EPINGLEE par l'appelant apres son fetch (``None``
    a la creation de la branche) : l'arbre, le texte du fichier et le parent
    du commit en viennent tous. Si le distant a avance depuis, la poussee
    n'est pas un fast-forward : elle est rejetee et l'appelant repart d'un
    arbre relu, au lieu de publier un fichier qui a perdu des lignes.
    """
    # Worktree temporaire, meme volume que les worktrees de la machine (D:\...)
    # quand le parent du depot est inscriptible ; sinon le tmp par defaut.
    try:
        repo.parent.mkdir(parents=True, exist_ok=True)
        tmp_root = Path(tempfile.mkdtemp(prefix="git-ledger-", dir=repo.parent))
    except OSError:
        tmp_root = Path(tempfile.mkdtemp(prefix="git-ledger-"))
    worktree = tmp_root / "wt"
    try:
        base = base_sha if base_sha is not None else "HEAD"
        rc, _, err = _git(
            ["worktree", "add", "--detach", "--no-checkout", str(worktree), base],
            cwd=repo,
        )
        if rc != 0:
            raise LedgerError("GIT_WORKTREE_FAILED", f"git worktree add : {_git_reason(err)}")
        # Index = arbre de la branche (ou vide a la creation de la branche), SANS
        # extraction : le commit ne peut ni perdre les fichiers des autres
        # machines, ni embarquer le contenu du depot principal.
        if base_sha is not None:
            rc, _, err = _git(["read-tree", base_sha], cwd=worktree)
        else:
            rc, _, err = _git(["read-tree", "--empty"], cwd=worktree)
        if rc != 0:
            raise LedgerError("GIT_WORKTREE_FAILED", f"git read-tree : {_git_reason(err)}")
        target = worktree / ledger / f"{canonical}.jsonl"
        # Garde levee EXPLICITEMENT et uniquement pour ce chemin : c'est le
        # worktree TEMPORAIRE de la branche dediee, pas l'arbre de travail du
        # depot principal (assert_local_output continue de refuser toute autre
        # ecriture dans un arbre git) ; l'etat publie vit sur la branche, jamais
        # dans le depot principal.
        target.parent.mkdir(parents=True, exist_ok=True)
        text = (
            _branch_file_text(repo, rel, remote=remote, rev=base_sha)
            if base_sha is not None
            else ""
        )
        if text and not text.endswith("\n"):
            text += "\n"
        # Ajout seul : les lignes distantes existantes sont recopiees telles
        # quelles, les nouvelles sont appendues dans l'ordre du spool.
        text += "".join(envelope_line(obs) + "\n" for obs in to_publish)
        with open(target, "w", encoding="utf-8", newline="\n") as stream:
            stream.write(text)
        rc, _, err = _git(["add", "--", rel], cwd=worktree)
        if rc != 0:
            raise LedgerError("GIT_COMMIT_FAILED", f"git add : {_git_reason(err)}")
        # Le commit est fabrique en PLOMBING (write-tree + commit-tree) et non
        # par `git commit` : le parent est choisi explicitement.
        #
        # Pourquoi : `git commit` dans un worktree detache aurait pour parent
        # la tete du worktree -- le HEAD du depot principal a la CREATION de la
        # branche. L'arbre de la branche (vide, hors notre fichier) serait
        # alors un commit qui SUPPRIME tout le contenu du depot (README.md
        # compris). C'est ce que la garde `GIT_PUBLISH_SCOPE` a attrape.
        # Ici, le parent est la tete EPINGLEE de la branche quand elle existe
        # (le sha dont viennent l'arbre et le texte, jamais le ref relu a cet
        # instant), et AUCUN parent quand la branche est creee (racine sans
        # parent) : la branche porte alors exactement les fichiers du ledger.
        rc, out, err = _git(["write-tree"], cwd=worktree)
        if rc != 0:
            raise LedgerError("GIT_COMMIT_FAILED", f"git write-tree : {_git_reason(err)}")
        tree = out.strip()
        commit_args = [
            "commit-tree", tree,
            "-m", f"{ledger}: publish {len(to_publish)} observation(s) from {canonical}",
        ]
        if base_sha is not None:
            commit_args += ["-p", base_sha]
        rc, out, err = _git(commit_args, cwd=worktree)
        if rc != 0:
            raise LedgerError(
                "GIT_COMMIT_FAILED",
                f"git commit-tree : {_git_reason(err)} (identite git ambiante requise)",
            )
        sha = out.strip()
        # INVARIANT, CODE et non observation : le commit publie ne touche que
        # le fichier de la machine. Les fichiers des autres machines sont lus
        # depuis la branche et recopies tels quels ; si le commit en modifie un,
        # la publication est refusee plutot que poussee. `--root` traite le cas
        # de la branche nee (commit sans parent) : la liste porte alors tout
        # l'arbre, qui doit se resumer au fichier de la machine.
        rc, out, err = _git(
            ["diff-tree", "--no-commit-id", "--name-only", "-r", "--root", sha],
            cwd=worktree,
        )
        if rc != 0:
            raise LedgerError(
                "GIT_COMMIT_FAILED", f"git diff-tree {sha} : {_git_reason(err)}"
            )
        touched = [line.strip() for line in out.splitlines() if line.strip()]
        if touched != [rel]:
            # Le sha est nomme : l'operateur voit OUV est le commit (il peut
            # l'inspecter) au lieu d'apprendre qu'une entree a disparu. Rien
            # n'a ete pousse -- le worktree temporaire est supprime au finally.
            raise LedgerError(
                "GIT_PUBLISH_SCOPE",
                f"commit {sha} publie sur {touched} au lieu de {rel} seule ; "
                "rien n'a ete pousse, le worktree temporaire a ete supprime",
            )
        # INVARIANT d'ajout seul, mesure sur le commit FABRIQUE et non sur ce
        # qu'on croit avoir lu : aucun identifiant porte par le fichier du
        # PARENT reel (`<sha>^`) ne disparait, et chaque observation a
        # publier figure dans le nouveau fichier. `GIT_PUBLISH_SCOPE` ne voit
        # que les chemins ; il laissait passer un commit qui reecrivait le bon
        # fichier en y perdant la ligne d'un autre publieur (finding Hermes 2
        # de la PR #22755).
        parent_ids = (
            _ids_at(repo, f"{sha}^", rel, remote=remote) if base_sha is not None else set()
        )
        new_ids = _ids_at(repo, sha, rel, remote=remote)
        wanted_ids = {str(obs["observation_id"]) for obs in to_publish}
        lost = sorted(parent_ids - new_ids)
        absent = sorted(wanted_ids - new_ids)
        if lost or absent:
            raise LedgerError(
                "GIT_PUBLISH_LOSS",
                f"commit {sha} sur {rel} : identifiants du parent perdus "
                f"{lost or '(aucun)'}, observations a publier absentes "
                f"{absent or '(aucune)'} ; rien n'a ete pousse, le spool est intact",
            )
        # La verification d'invariant precede le push : rien n'est publie si
        # elle echoue. Le commit fabrique en plumbing ne deplace PAS la HEAD
        # du worktree : la poussee vise donc le SHA explicite, jamais `HEAD`
        # (qui designait encore la tete du depot principal -- la poussee
        # aurait publie autre chose que ce que l'on vient de fabriquer).
        push_ref = f"{sha}:refs/heads/{GIT_LEDGER_BRANCH}"
        rc, _, err = _git(["push", remote, push_ref], cwd=worktree)
        if rc != 0:
            return None  # rejet (probablement non-fast-forward) : UN retry au-dessus
        # Belt : le ref distant doit porter NOTRE sha. Un push « reussi » qui
        # publierait autre chose est un echec silencieux du point de vue de
        # l'etat de la flotte -- il est donc refuse ici, explicitement.
        rc, out, err = _git(
            ["ls-remote", remote, f"refs/heads/{GIT_LEDGER_BRANCH}"], cwd=worktree
        )
        if rc != 0:
            raise LedgerError(
                "GIT_PUBLISH_UNVERIFIED",
                f"ls-remote {remote} : {_git_reason(err)} (poussee vers {sha}) ; "
                "la poussee a pu ATTERRIR : relancer publish --git --emit "
                "-- si l'observation est deja sur la branche, ce second essai "
                "la DRAINE (published=false n'est pas une perte)",
            )
        remote_sha = out.split()[0].strip() if out.split() else ""
        if remote_sha != sha:
            raise LedgerError(
                "GIT_PUBLISH_UNVERIFIED",
                f"le ref distant porte {remote_sha!r} et non {sha!r} "
                "(la poussee a publie autre chose que l'observation) ; "
                "relancer publish --git --emit",
            )
        return sha
    finally:
        rc_rm, _, err_rm = _git(
            ["worktree", "remove", "--force", str(worktree)], cwd=repo
        )
        if rc_rm != 0:
            # Le retrait peut echouer (verrou fichier Windows, antivirus) :
            # le worktree fantome et son enregistrement `.git/worktrees/<id>`
            # subsisteraient, et le dossier temporaire est cree sous
            # `repo.parent` -- a la racine du drive en production. `prune`
            # retire l'enregistrement, et l'echec est JOURNALISE : un residu
            # silencieux s'accumulerait a chaque tentative.
            _git(["worktree", "prune"], cwd=repo)
            shutil.rmtree(worktree, ignore_errors=True)
            print(
                f"WARNING worktree remove rc={rc_rm} : {_git_reason(err_rm)} "
                "(prune tente ; un residu peut subsister)",
                file=sys.stderr,
            )
        shutil.rmtree(tmp_root, ignore_errors=True)


def _drain_published(
    spool_dir: Path,
    source: list[dict[str, Any]],
    existing_ids: set[str],
) -> list[str]:
    """Draine du spool les observations DEJA portees par la branche.

    Le drain est la moitie oubliee de la publication : une observation dont
    l'``observation_id`` figure sur la branche est PUBLIEE, qu'elle y soit
    arrivee par ce push-la ou par un push anterieur dont la verification a
    echoue. La laisser dans le spool fait repondre ``UNPOSTED`` au gate pour
    toujours -- et le remede documente (relancer la publication) boucle sur
    un "deja a jour" qui ne draine rien.

    Renvoie les identifiants draines (vide si rien a drainer). Ne leve pas :
    un drain impossible ne doit pas faire perdre le resultat de la
    publication, deja constate.
    """
    drainable = sorted(
        str(obs["observation_id"]) for obs in source
        if str(obs.get("observation_id")) in existing_ids
    )
    if not drainable:
        return []
    try:
        archive_posted(spool_dir, drainable)
    except LedgerError as exc:
        # Un drain impossible ne doit pas faire perdre la publication -- mais
        # il ne doit pas etre SILENT : la distinction "rien a drainer" et
        # "drain impossible" se lit ici, sinon le gate repond UNPOSTED
        # indefiniment sans que rien ne dise pourquoi.
        print(
            f"[debt-ledger] drain impossible ({exc.reason}) : les observations "
            "publiees restent dans le spool ; le gate peut repondre UNPOSTED "
            "autant de fois que le spool n'est pas vide",
            file=sys.stderr,
        )
        return []
    return drainable


def publish_git_ledger(
    *,
    spool_dir: Path,
    repo: Path,
    machine: str,
    remote: str = GIT_LEDGER_REMOTE_DEFAULT,
    emit: bool = False,
    ledger: str = GPU_RESERVATION,
) -> dict[str, Any]:
    """Publie les enveloppes locales sur la branche dediee ; resume du geste.

    Dry-run par defaut (``emit=False``) : rien n'est ecrit, rien n'est pousse.
    Idempotent : toute observation dont l'``observation_id`` figure deja sur la
    branche n'est pas reecrite. La poussee vise ``<remote>:refs/heads/<branch>``,
    jamais ``main`` ; en cas de rejet (deux machines publient en meme temps),
    UN seul retry : re-fetch, reapplication du fichier sur la nouvelle tete
    distante, nouveau commit, nouvelle poussee. Un echec final lève
    ``GIT_PUSH_REJECTED`` -- jamais un succes silencieux.
    """
    canonical = canonical_machine(machine)
    rel = f"{ledger}/{canonical}.jsonl"
    source = [
        parse_observation(obs, ledger)
        for obs in _publishable_observations(spool_dir, ledger=ledger)
    ]
    source_ids = {str(obs["observation_id"]) for obs in source}
    # INVARIANT, CODE et non observation : une machine n'ecrit que dans SON
    # fichier. Une observation dont l'entite porte une autre machine est
    # refusee ici, avant tout commit -- un ecrasement d'autrui ne doit pas
    # pouvoir se produire par une simple ligne de spool.
    for obs in source:
        obs_machine = str((obs.get("entity") or {}).get("machine", ""))
        if obs_machine and obs_machine != canonical:
            raise LedgerError(
                "GIT_PUBLISH_FOREIGN_MACHINE",
                f"observation {obs.get('observation_id')!r} porte la machine "
                f"{obs_machine!r} et serait ecrite dans le fichier de {canonical!r}",
            )
    # La cible est resolue AVANT tout contact reseau : un remote absent ou
    # une cible interdite sont refuses sans qu'une branche soit publiee.
    remote_url = ensure_git_ledger_remote(repo, remote)
    fetch_error = fetch_git_ledger_branch(repo, remote=remote)
    # La branche peut ne pas encore exister sur le remote : le fetch echoue
    # alors que TOUT va bien (premiere publication d'une machine). Le cas est
    # distingue par `ls-remote`, jamais par le texte du stderr.
    fetch_branche_absente = bool(fetch_error) and _branche_absente_du_remote(
        repo, remote=remote
    )
    # La tete est epinglee UNE fois apres le fetch : ce qui est deja publie,
    # l'arbre du commit et son parent viennent du meme sha (finding Hermes 2).
    base_sha = _pin_ledger_base(repo, remote=remote)
    existing_text = (
        _branch_file_text(repo, rel, remote=remote, rev=base_sha) if base_sha else ""
    )
    existing_ids = _published_ids(existing_text)
    to_publish = [obs for obs in source if str(obs["observation_id"]) not in existing_ids]
    summary: dict[str, Any] = {
        "branch": GIT_LEDGER_BRANCH,
        "remote": remote,
        "remote_url": remote_url,
        "target": rel,
        "machine": canonical,
        "to_publish": [str(obs["observation_id"]) for obs in to_publish],
        "already_on_branch": sorted(existing_ids & source_ids),
        "fetch_error": fetch_error,
        "fetch_branche_absente": fetch_branche_absente,
        "published": False,
        "pushed_sha": None,
        "drained": [],
    }
    if not emit:
        return summary
    if not to_publish:
        # Les observations du spool sont DEJA sur la branche : publication
        # rejouee apres un push ATTERRI dont la verification (ls-remote) a
        # echoue, ou course gagnee par un push concurrent portant le meme
        # contenu. Le spool doit alors etre DRAINE -- sinon `check_pending`
        # rend UNPOSTED indefiniment et le remede documente ("relancer
        # publish --git --emit") boucle sur un "deja a jour" qui ne draine
        # rien : le device devient impossible a liberer.
        drained = _drain_published(spool_dir, source, existing_ids)
        if drained:
            summary["drained"] = drained
        return summary
    pushed_sha = _publish_attempt(
        repo=repo, rel=rel, canonical=canonical, ledger=ledger,
        remote=remote, to_publish=to_publish, base_sha=base_sha,
    )
    if pushed_sha is None:
        # Un seul retry : la tete distante a bouge sous nous. On repart de
        # l'arbre RELU apres ce fetch-ci, epingle a nouveau.
        fetch_git_ledger_branch(repo, remote=remote)
        base_sha = _pin_ledger_base(repo, remote=remote)
        existing_text = (
            _branch_file_text(repo, rel, remote=remote, rev=base_sha) if base_sha else ""
        )
        existing_ids = _published_ids(existing_text)
        to_publish = [
            obs for obs in source if str(obs["observation_id"]) not in existing_ids
        ]
        summary["to_publish"] = [str(obs["observation_id"]) for obs in to_publish]
        summary["already_on_branch"] = sorted(existing_ids & source_ids)
        if not to_publish:
            # La course a ete gagnee par un push portant le meme contenu.
            summary["published"] = True
            drained = _drain_published(spool_dir, source, existing_ids)
            if drained:
                summary["drained"] = drained
            return summary
        pushed_sha = _publish_attempt(
            repo=repo, rel=rel, canonical=canonical, ledger=ledger,
            remote=remote, to_publish=to_publish, base_sha=base_sha,
        )
    if pushed_sha is None:
        # Le refus NE perd rien : les observations restent dans le spool local
        # (elles ne sont archivees qu'apres un push reussi). Pour que l'etat de
        # la flotte ne perde pas une observation, le fantome doit etre
        # DETECTABLE : le refus nomme les identifiants retenus, et ils restent
        # lisibles par `spool`.
        retained = [str(obs["observation_id"]) for obs in to_publish]
        raise LedgerError(
            "GIT_PUSH_REJECTED",
            f"push {remote}/{GIT_LEDGER_BRANCH} rejete deux fois (concurrence) ; "
            f"{len(retained)} observation(s) RETENUES dans le spool local "
            f"(published=false) : {', '.join(retained) or '(aucune)'} ; "
            "relancer publish --git --emit",
        )
    published_now = [str(obs["observation_id"]) for obs in to_publish]
    # Aucun spool n'est vide sur la foi d'un code de retour : chaque
    # identifiant draine doit se RETROUVER dans le fichier du commit pousse
    # (celui que ls-remote vient de confirmer comme tete distante). Une
    # observation absente reste dans le spool -- elle sera republiee -- et
    # l'echec est nomme (finding Hermes 2 de la PR #22755).
    on_pushed = _ids_at(repo, pushed_sha, rel, remote=remote)
    missing = sorted(set(published_now) - on_pushed)
    if missing:
        raise LedgerError(
            "GIT_PUBLISH_LOSS",
            f"le commit pousse {pushed_sha} ne porte pas {', '.join(missing)} "
            f"dans {rel} ; spool NON draine (published=false pour ces "
            "observations) ; relancer publish --git --emit",
        )
    summary["published"] = True
    summary["pushed_sha"] = pushed_sha
    # Le ref de suivi local voit immediatement ce qui vient d'etre publie.
    # Compare-and-swap sur la base epinglee : si un autre publieur (ou un
    # fetch) a deja avance le ref, on ne le ramene jamais en arriere.
    expected_old = base_sha if base_sha is not None else "0" * len(pushed_sha)
    _git(["update-ref", _tracking_ref(remote), pushed_sha, expected_old], cwd=repo)
    # Drain du spool local : les ids publies ne doivent plus faire repondre
    # UNPOSTED au gate local (la source de publication inclut les archives).
    #
    # La poussee a ATTERRI et le commit verifie porte TOUTES les observations
    # publiees : l'etat de la flotte EST sur la branche. Un drain qui
    # n'aboutit pas -- une enveloppe a pu disparaitre du spool entre la
    # lecture de la source et l'archivage -- ne doit donc pas faire dire
    # "echec" a une publication reussie : le RESIDUE est nomme, et la
    # verification du commit reste le fait qui fait foi.
    drain = _archive_published_best_effort(spool_dir, published_now)
    summary["drained"] = list(drain.get("moved") or [])
    if drain.get("missing"):
        summary["drain_missing"] = list(drain["missing"])
    return summary


def _archive_published_best_effort(
    spool_dir: Path, observation_ids: Sequence[str]
) -> dict[str, list[str]]:
    """Archive ce qui se resout, nomme ce qui ne se resout pas.

    ``archive_posted`` reste **tout ou rien** -- c'est son contrat, et le
    demi-drain qu'il refuse est justement l'etat qui fait mentir
    ``check_pending``. Mais l'appelant de la publication, lui, a deja
    verifie que la poussee a ATTERRI : un identifiant devenu introuvable
    dans le spool (une enveloppe retiree entre la lecture de la source et
    l'archivage) ne peut plus rien perdre -- l'observation est sur la
    branche. Refuser l'appel entier ferait dire "echec" a une publication
    reussie, et surtout laisserait croire que rien n'a ete publie.

    Renvoie ``{"moved": [...], "already": [...], "missing": [...]}``.
    """
    pending_index = _index_spool(spool_dir, strict=True)
    posted_index = _index_spool(spool_dir / "posted", strict=False)
    resolvable = [
        observation_id
        for observation_id in observation_ids
        if observation_id in pending_index or observation_id in posted_index
    ]
    missing = sorted(set(observation_ids) - set(resolvable))
    outcome: dict[str, list[str]] = {"moved": [], "already": [], "missing": missing}
    if resolvable:
        archived = archive_posted(spool_dir, resolvable)
        outcome["moved"] = list(archived.get("moved") or [])
        outcome["already"] = list(archived.get("already") or [])
    return outcome


def refresh_snapshot_from_branch(
    *,
    ledger: str,
    repo: Path,
    remote: str = GIT_LEDGER_REMOTE_DEFAULT,
    state_dir: Path,
    now: datetime | None = None,
) -> Path:
    """Recalcule le snapshot local (CACHE) depuis la branche dediee, par le meme
    code de fold que ``reduce`` ; retourne le chemin du snapshot ecrit.

    Le snapshot n'est jamais une autorite : la branche est la source primaire,
    ce cache n'existe que pour que ``check_pending --source local`` (et le
    repli ``auto``) trouvent un etat replie sans re-lire git.
    """
    fetch_git_ledger_branch(repo, remote=remote)
    observations, _rejections = observations_from_git_ledger(repo, remote=remote)
    messages = [
        {
            "messageId": str(obs["observation_id"]),
            "author": obs["actor"],
            "createdAt": obs["observed_at"],
            "content": envelope_line(obs),
        }
        for obs in observations
    ]
    export = {
        "schema": EXPORT_SCHEMA,
        "ledger": ledger,
        "window": {"kind": "full", "archives": []},
        "messages": messages,
    }
    baseline_path = state_dir / ledger / "baseline.json"
    baseline = _read_json(baseline_path) if baseline_path.exists() else None
    config = None
    config_path = state_dir / "config.json"
    if config_path.exists():
        config = _read_json(config_path)
    result = reduce_ledger(
        ledger=ledger,
        export=export,
        prior_snapshot=None,
        baseline=baseline,
        now=now,
        config=config,
    )
    base = state_dir / ledger
    with LedgerLock(base / ".reduce.lock"):
        snapshot_path = base / "snapshots" / "snapshot.json"
        write_json_atomic(snapshot_path, result.snapshot)
        write_json_atomic(base / "snapshots" / "summary.json", result.summary)
        _write_text_atomic(base / "snapshots" / "status.md", result.status_text)
    return snapshot_path


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
        fields = resolve_now_sentinels(
            _loads_object(args.fields_json, where="--fields-json"), moment=utcnow()
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
            "fields": fields,
        }
        if args.note:
            raw["note"] = args.note
    warnings: list[str] = []
    observation = parse_observation(raw, args.ledger, warnings=warnings)
    for warning in warnings:
        print(f"WARNING {warning}", file=sys.stderr)
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
        # --dry-run: build and print, never write. The dry-run mode is what
        # makes ``append`` safe to call during agent reasoning -- the agent
        # gets the envelope and the MCP descriptor without side effects.
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
    else:
        # Default path: write into the state-dir's ledger spool when ``init``
        # has run on this state-dir. The spool is the local outbox
        # documented in ``init_ledger_tree``; without it, an append cannot be
        # recovered -- #17927 found that leaving the default to "write
        # nothing" silently broke the local recovery path, so a state-dir that
        # has not been initialised is now refused with a distinct exit code
        # rather than silently producing an unsaved observation.
        default_spool = state_dir / args.ledger / "spool"
        if not default_spool.is_dir():
            raise LedgerError(
                "UNINITIALISED_STATE_DIR",
                f"state-dir {state_dir} has no {args.ledger}/spool/ -- "
                "run `debt_ledger.py init --apply --state-dir <dir>` first, "
                "or pass --dry-run / --out / --out-dir explicitly",
            )
        out_path, created = spool_observation(default_spool, observation)
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


#: CLI parser for the gpu-reservation entity string ``<machine>#gpu<n>``.
_GPU_ENTITY_CLI_RE = re.compile(r"^([\w.-]+)#gpu(\d+)$")


def _parse_entity_string(raw: str, ledger: str) -> dict:
    """Parse a CLI entity string into the dict ``_validate_entity`` accepts.

    The CLI form is the same as ``entity_key``: ``owner/repo#N`` for issue-debt,
    or ``<machine>#gpu<n>`` for gpu-reservation. We translate that into the
    per-ledger field shape, then run it through ``_validate_entity`` so the
    validators stay the single source of truth.
    """
    if ledger == GPU_RESERVATION:
        m = _GPU_ENTITY_CLI_RE.match(raw.strip())
        if not m:
            raise ValueError(
                f"entity {raw!r} does not match '<machine>#gpu<n>' (e.g. 'myia-ai-01#gpu2')"
            )
        return _validate_entity({"machine": m.group(1), "gpu_index": int(m.group(2))}, ledger)
    if ledger == ISSUE_DEBT:
        if "#" not in raw:
            raise ValueError(f"entity {raw!r} does not match 'owner/repo#N'")
        repo, _, n = raw.partition("#")
        return _validate_entity({"repo": repo, "issue": int(n)}, ledger)
    raise ValueError(f"unknown ledger {ledger!r}")


def _print_pending_verdict(
    args: argparse.Namespace,
    verdict: str,
    reason: str,
    now: datetime,
    source: str,
    extra: dict[str, Any] | None = None,
) -> None:
    """Une seule forme de sortie par verdict, quelle que soit la source lue.

    ``extra`` ajoute des champs de DIAGNOSTIC a la sortie JSON (jamais un
    second verdict : le champ ``verdict`` reste le seul que l'appelant lit).
    """
    if args.json_output:
        payload = {
            "verdict": verdict,
            "reason": reason,
            "entity": args.entity,
            "now": format_utc(now),
            "source": source,
        }
        if extra:
            payload.update(extra)
        print(json.dumps(payload))
    else:
        print(f"{verdict}  {args.entity}  {reason}")
        print(f"source={source}")


def _check_pending_snapshot(
    args: argparse.Namespace,
    entity: dict[str, Any],
    now: datetime,
    snapshot_path: Path,
    *,
    source: str,
    fail_closed: bool,
) -> int:
    """Le chemin LOCAL historique : verdict replie depuis le snapshot (un CACHE).

    ``fail_closed`` ne vaut True que pour le repli de ``--source auto`` : sans
    snapshot, AUCUNE source n'est lisible et le verdict nomme l'indisponibilite
    (``UNREADABLE``) au lieu de rendre l'entite libre. Avec ``--source local``
    explicite, le comportement historique est preserve (``NO_OBS``).
    """
    if not snapshot_path.exists():
        verdict, reason = (
            ("UNREADABLE", f"no snapshot at {snapshot_path}")
            if fail_closed
            else ("NO_OBS", f"no snapshot at {snapshot_path}")
        )
        _print_pending_verdict(args, verdict, reason, now, source=source)
        return 1 if fail_closed else 0
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    # A verdict needs the CURRENT state of the entity, and reads several fields
    # off one record -- so it must be fed the merged row, not the per-field
    # checkpoint records (#20077).
    records = record_views_from_snapshot(snapshot, args.ledger)
    verdict, reason = evaluate_gpu_pending(records, entity, now, args.my_lane)
    _print_pending_verdict(args, verdict, reason, now, source=source)
    return GPU_VERDICT_EXIT_CODES.get(verdict, 0)


def _cli_check_pending(args: argparse.Namespace) -> int:
    """Pre-launch gate for a GPU workload.

    Reads the latest state of the entity and returns the verdict the picker
    needs. ``--source`` decides where the state is read from:

      * ``git``   -- the dedicated branch ``ops/gpu-ledger`` (the PRIMARY
                     source): fetch REQUIRED, read by ``git show``, fold,
                     same verdict vocabulary as the local path. A failed
                     fetch is ``UNREADABLE`` even when an older tracking ref
                     is still readable: that ref is reported for diagnosis
                     only (``stale_ref`` in the JSON), it never authorises;
      * ``local`` -- the local snapshot, a CACHE never an authority; this is
                     the historical behaviour, unchanged;
      * ``auto``  -- try ``git``; on an unreachable branch, fall back to the
                     local cache ONLY IF the branch does not exist on the
                     remote (measured by ``ls-remote`` : nothing was ever
                     published, so the cache cannot miss a hold) AND SAY SO
                     in the output (``source=local (branche <remote>/<branch>
                     absente)``). If the branch EXISTS, or the remote is
                     unreachable, the verdict is ``UNREADABLE`` (fail-CLOSED) :
                     a stale cache must not render a device free.

      * UNREADABLE_SPOOL -- un fichier de l'outbox ne peut pas etre lu ; la
                            gate refuse car il pourrait porter un ``held``.
    Verdicts:

      * UNPOSTED   -- the local outbox still holds observations that never
                      reached the ledger; no verdict is trusted until they
                      are posted/published (#22456). This guard fires FIRST,
                      whatever the source.
      * NO_OBS     -- no record; the picker skips the GPU-bound grain.
      * HOLD       -- held by another lane, or by us but outside the window.
      * OK_TO_RUN  -- held by us (holder == --my-lane) and now is in the run
                      window. Without --my-lane, a held device is HOLD.
      * STALE      -- held past expected_end with no release; needs follow-up.
      * RELEASED   -- terminal; the GPU is free to take.
      * UNREADABLE -- NO source was readable (branch unreachable with
                      ``--source git``, or git unreachable AND no local
                      snapshot with ``--source auto``), or the fetch failed
                      and only a possibly stale tracking ref remains.
                      Fail-closed: an unreadable ledger is never a free device.

    Exit codes come from ``GPU_VERDICT_EXIT_CODES`` (single source, mirrored
    by the table of ``docs/coordination/gpu-reservation.md``): 0 for
    OK_TO_RUN, NO_OBS and RELEASED, 1 for HOLD, UNPOSTED, UNREADABLE and
    UNREADABLE_SPOOL (the gate refuses -- an unread ledger is not a free
    device), 2 for STALE (the caller decides).
    2 for STALE (the caller decides whether to refresh or to hold). All exit
    codes are documented in gpu-reservation.md -- a wrapper that maps them
    to skip/hold/escalate lives one layer up.
    """
    if args.ledger != GPU_RESERVATION:
        print(
            f"ERROR: check_pending only supports ledger={GPU_RESERVATION!r}, got {args.ledger!r}",
            file=sys.stderr,
        )
        return 2

    if not args.entity:
        print("ERROR: --entity is required (e.g. 'myia-ai-01#gpu2')", file=sys.stderr)
        return 2

    try:
        entity = _parse_entity_string(args.entity, args.ledger)
    except (ValueError, ObservationError) as exc:
        if isinstance(exc, ObservationError):
            print(f"ERROR {exc.reason}: {exc.detail}", file=sys.stderr)
        else:
            print(f"ERROR entity_mismatch: {exc}", file=sys.stderr)
        return 2

    state_dir = Path(args.state_dir) if args.state_dir else default_state_dir()
    base = state_dir / args.ledger
    snapshot_path = Path(args.snapshot) if args.snapshot else base / "snapshots" / "snapshot.json"

    if args.now is not None:
        now = parse_utc_timestamp(args.now, where="--now")
    else:
        now = utcnow()

    # Un fichier illisible peut porter une réservation : la gate répond un
    # verdict explicite, nomme chaque fichier et refuse le lancement. Ce verdict
    # précède UNPOSTED afin que le défaut à réparer ne soit pas masqué par le
    # décompte des enveloppes saines.
    unreadable = spool_unreadable(base / "spool")
    if unreadable:
        reason = "; ".join(f"{item['path']} ({item['reason']})" for item in unreadable)
        if args.json_output:
            print(json.dumps({
                "verdict": VERDICT_UNREADABLE_SPOOL,
                "reason": reason,
                "entity": args.entity,
                "now": format_utc(now),
            }))
        else:
            print(f"{VERDICT_UNREADABLE_SPOOL}  {args.entity}  {reason}")
        return GPU_VERDICT_EXIT_CODES[VERDICT_UNREADABLE_SPOOL]

    # An observation still sitting in the local outbox never reached the
    # ledger, so a verdict reduced from any source is blind to it: the gate
    # answers "RELEASED" with the aplomb of a measurement while a live hold
    # waits in the spool, and two lanes launch on the same device (#22456).
    # Name the unread state instead of answering around it -- FIRST, whatever
    # the source: an unread outbox invalidates the verdict before git is read.
    spooled = spool_status(base / "spool")[args.ledger]
    if spooled["pending"]:
        reason = (
            f"{spooled['pending']} observation(s) still pending in {base / 'spool'} "
            f"(oldest {spooled['oldest_observed_at'] or 'unknown'}) -- post them "
            "(debt_ledger.py flush, or publish --git --emit) before trusting any verdict"
        )
        if args.json_output:
            print(json.dumps({
                "verdict": VERDICT_UNPOSTED,
                "reason": reason,
                "entity": args.entity,
                "pending": spooled["pending"],
                "now": format_utc(now),
                "source": "local (outbox non vide)",
            }))
        else:
            print(f"{VERDICT_UNPOSTED}  {args.entity}  {reason}")
            print("source=local (outbox non vide)")
        return GPU_VERDICT_EXIT_CODES[VERDICT_UNPOSTED]

    source = getattr(args, "source", "auto") or "auto"
    if source == "local":
        return _check_pending_snapshot(
            args, entity, now, snapshot_path, source="local", fail_closed=False
        )

    # --source git, ou auto qui tente git d'abord.
    repo = Path(args.repo) if args.repo else default_repo_root()
    unavailable: str | None = None
    fetch_error: str | None = None
    # Etat de la branche DISTANTE : "absent" (elle n'existe pas : rien n'a
    # jamais ete publie), "exists" (elle existe : elle peut porter le hold
    # d'une autre machine), "unknown" (le remote est injoignable : on ne peut
    # rien affirmer). Mesure par le CODE DE SORTIE de `ls-remote` -- jamais
    # par le texte de stderr, qui est localise et dont le message distingue
    # "ref absent" de "reseau coupe" par une phrase, pas par un code.
    remote_state = "unknown"
    if repo is None or not repo.exists():
        unavailable = "aucun depot git lisible (git rev-parse --show-toplevel a echoue)"
    else:
        try:
            ensure_git_ledger_remote(repo, args.remote)
        except LedgerError as exc:
            # Cible non configuree, ou cible interdite : la source PRIMAIRE est
            # illisible. Le repli "auto" sur le cache local exige de pouvoir
            # affirmer que la branche n'a JAMAIS ete publiee -- ce qu'on ne
            # peut pas ici -> UNREADABLE, fail-CLOSED (un device ne se libere
            # pas parce que la cible de reference est mal configuree).
            unavailable = f"{exc.reason}: {exc.detail}"
            remote_state = "unknown"
            _print_pending_verdict(
                args,
                "UNREADABLE",
                f"cible de publication inutilisable : {unavailable}",
                now,
                source=f"git (cible inutilisable : {unavailable})",
            )
            return GPU_VERDICT_EXIT_CODES[VERDICT_UNREADABLE]
        fetch_error = fetch_git_ledger_branch(repo, remote=args.remote)
        if not git_ledger_ref_available(repo, remote=args.remote):
            unavailable = (
                fetch_error
                or f"branche {args.remote}/{GIT_LEDGER_BRANCH} absente"
            )
            rc_ls, out_ls, err_ls = _git(
                ["ls-remote", args.remote, f"refs/heads/{GIT_LEDGER_BRANCH}"],
                cwd=repo,
            )
            if rc_ls == 0:
                remote_state = "exists" if out_ls.strip() else "absent"
            else:
                remote_state = "unknown"
        else:
            observations, _rejections = observations_from_git_ledger(
                repo, remote=args.remote
            )
            records = [
                record_from_observation(obs, f"git:{GIT_LEDGER_BRANCH}")
                for obs in observations
            ]
            verdict, reason = evaluate_gpu_pending(records, entity, now, args.my_lane)
            if fetch_error:
                # Le fetch a echoue : le ref de suivi local n'est que le DERNIER
                # ETAT CONNU de la branche, pas son etat present. Un hold publie
                # depuis par une autre lane y est invisible, et ce ref rendrait
                # RELEASED (ou OK_TO_RUN) sur un device deja repris -- le double
                # lancement exact que ce gate existe pour empecher (PR #22755,
                # finding Hermes 3). Le ref est donc lu pour le DIAGNOSTIC (le
                # verdict qu'il porterait est nomme) mais il n'autorise rien :
                # UNREADABLE, fail-CLOSED, comme une branche illisible.
                rc_sha, out_sha, _ = _git(
                    ["rev-parse", "--short", _tracking_ref(args.remote)], cwd=repo
                )
                stale_sha = out_sha.strip() if rc_sha == 0 else "?"
                _print_pending_verdict(
                    args,
                    "UNREADABLE",
                    f"fetch impossible : {fetch_error} ; le dernier ref local "
                    f"({stale_sha}) dirait {verdict} ({reason}) -- lecture "
                    "PERIMEE, diagnostic seulement : elle n'autorise aucun "
                    "lancement (fail-CLOSED)",
                    now,
                    source=(
                        f"git (fetch impossible : {fetch_error} ; dernier ref "
                        "local lu pour diagnostic seulement)"
                    ),
                    extra={
                        "stale_ref": {
                            "sha": stale_sha,
                            "verdict": verdict,
                            "reason": reason,
                        }
                    },
                )
                return GPU_VERDICT_EXIT_CODES[VERDICT_UNREADABLE]
            _print_pending_verdict(args, verdict, reason, now, source="git")
            return GPU_VERDICT_EXIT_CODES.get(verdict, 0)

    # Branche git injoignable.
    if source == "git":
        _print_pending_verdict(
            args,
            "UNREADABLE",
            f"source git indisponible : {unavailable}",
            now,
            source=f"git (indisponible : {unavailable})",
        )
        return GPU_VERDICT_EXIT_CODES[VERDICT_UNREADABLE]
    # auto : repli sur le cache local -- mais SEULEMENT quand la branche
    # n'existe PAS (mesure par `ls-remote`). Un cache perime n'a pas le
    # droit d'autoriser un lancement : si la branche existe (elle porte
    # peut-etre le hold d'une autre machine) ou si le remote est injoignable
    # (on ne peut rien affirmer), le cache -- anterieur -- ne repond pas a la
    # place de la source primaire. C'est le double-reservation exact que ce
    # transport doit empecher.
    if remote_state != "absent":
        _print_pending_verdict(
            args,
            "UNREADABLE",
            f"git indisponible : {unavailable} ; la branche "
            f"{args.remote}/{GIT_LEDGER_BRANCH} "
            + ("EXISTE" if remote_state == "exists" else "est INCONNUE")
            + " : elle peut porter le hold d'une autre machine, que le cache "
            "local (anterieur) ne montre pas. Fail-CLOSED.",
            now,
            source=f"git (indisponible : {unavailable})",
        )
        return GPU_VERDICT_EXIT_CODES[VERDICT_UNREADABLE]
    # La branche n'existe pas : rien n'a jamais ete publie, aucun hold
    # n'existe nulle part : le cache local peut repondre.
    return _check_pending_snapshot(
        args,
        entity,
        now,
        snapshot_path,
        source=f"local (branche {args.remote}/{GIT_LEDGER_BRANCH} absente)",
        fail_closed=True,
    )


def _cli_publish(args: argparse.Namespace) -> int:
    """Publie le spool local vers la branche dediee (dry-run par defaut).

    Conforme a la discipline de ``flush`` : sans ``--emit``, rien n'est ecrit
    et rien n'est pousse ; la sortie montre ce qui serait publie, vers quoi,
    et ce qui est deja sur la branche. Apres une publication reussie, le
    snapshot local (un CACHE) est recalcule depuis la branche.
    """
    if not args.git:
        print(
            "ERROR: publish requires --git (seul transport : la branche dediee)",
            file=sys.stderr,
        )
        return 2
    if args.ledger != GPU_RESERVATION:
        print(
            f"ERROR: publish --git ne supporte que ledger={GPU_RESERVATION!r}",
            file=sys.stderr,
        )
        return 2
    state_dir = Path(args.state_dir) if args.state_dir else default_state_dir()
    assert_local_output(state_dir, what="state directory")
    spool_dir = Path(args.out_dir) if args.out_dir else state_dir / args.ledger / "spool"
    repo = Path(args.repo) if args.repo else default_repo_root()
    if repo is None or not repo.exists():
        raise LedgerError(
            "NO_GIT_REPO", "aucun depot git trouve pour publier (passez --repo <chemin>)"
        )
    machine = args.machine or (os.environ.get("COMPUTERNAME") or os.environ.get("HOSTNAME") or "")
    moment = parse_utc_timestamp(args.now, where="--now") if args.now else None
    summary = publish_git_ledger(
        spool_dir=spool_dir,
        repo=repo,
        machine=machine,
        remote=args.remote,
        emit=args.emit,
        ledger=args.ledger,
    )
    if args.emit and summary["published"]:
        summary["snapshot"] = str(
            refresh_snapshot_from_branch(
                ledger=args.ledger,
                repo=repo,
                remote=args.remote,
                state_dir=state_dir,
                now=moment,
            )
        )
    if args.json:
        print(json.dumps(summary, ensure_ascii=False, indent=2))
    else:
        branch_target = f"{summary['remote']}/{summary['branch']} : {summary['target']}"
        if args.emit:
            if summary["published"]:
                print(f"PUBLISHED {len(summary['to_publish'])} observation(s) -> {branch_target}")
            else:
                print(f"NOTHING TO PUBLISH -> {branch_target} (deja a jour)")
        else:
            print(f"DRY-RUN publish {args.ledger} -> {branch_target}")
            for observation_id in summary["to_publish"]:
                print(f"  {observation_id}")
            print(
                f"to publish: {len(summary['to_publish'])} ; "
                f"already on branch: {len(summary['already_on_branch'])}"
            )
            print("(dry-run -- rien ecrit, rien pousse ; pass --emit pour publier)")
        if summary["fetch_error"]:
            if summary.get("fetch_branche_absente"):
                # Cas NORMAL de la premiere publication : le remote est
                # joignable et la branche n'existe pas encore. Le fetch
                # « echoue » parce qu'il n'y a rien a fetcher -- l'afficher
                # comme une erreur pollue le journal de chaque machine
                # (point mineur de la review Hermes du 2026-10-28).
                print(
                    "branche absente sur le remote (premiere publication) : "
                    "rien a fetcher"
                )
            else:
                print(
                    f"fetch: {summary['fetch_error']} (lecture du dernier ref local)",
                    file=sys.stderr,
                )
        if summary.get("snapshot"):
            print(f"snapshot (cache) refreshed: {summary['snapshot']}")
        if summary.get("drain_missing"):
            missing = summary["drain_missing"]
            print(
                f"drain incomplet : {len(missing)} observation(s) sont sur la "
                "branche mais ne se resolvent plus dans le spool local : "
                + ", ".join(missing[:10])
                + ("..." if len(missing) > 10 else ""),
                file=sys.stderr,
            )
    return 0


def _cli_spool_status(args: argparse.Namespace) -> int:
    if args.out_dir:
        spool_dirs = [Path(args.out_dir)]
    else:
        state_dir = Path(args.state_dir) if args.state_dir else default_state_dir()
        # Default path: mirror ``_cli_append`` -- a state-dir that has not run
        # ``init --apply`` for ANY LEDGER has no per-ledger spool anywhere, and
        # we must refuse rather than silently report ``pending=0``. A typo'd
        # ``--state-dir`` (or any directory the agent has never built) is the
        # precise trap we close here -- see #18006, suite de #17940.
        # ``init`` is one-ledger-at-a-time, so a state-dir initialised for one
        # LEDGER but not another is *not* uninitialised -- we only refuse when
        # NO ledger has a spool dir.
        if not any((state_dir / ledger / "spool").is_dir() for ledger in LEDGERS):
            raise LedgerError(
                "UNINITIALISED_STATE_DIR",
                f"state-dir {state_dir} has no <ledger>/spool/ for any ledger -- "
                "run `debt_ledger.py init --apply --state-dir <dir>` first, "
                "or pass --out-dir explicitly to inspect an arbitrary dir",
            )
        spool_dirs = [state_dir / ledger / "spool" for ledger in LEDGERS]
    unreadable: list[dict[str, str]] = []
    status = {ledger: {"pending": 0, "oldest_observed_at": None} for ledger in LEDGERS}
    for spool_dir in spool_dirs:
        unreadable.extend(spool_unreadable(spool_dir))
        counts = spool_status(spool_dir)
        for ledger, row in counts.items():
            status[ledger]["pending"] += row["pending"]
            if row["oldest_observed_at"] is not None and (
                status[ledger]["oldest_observed_at"] is None
                or row["oldest_observed_at"] < status[ledger]["oldest_observed_at"]
            ):
                status[ledger]["oldest_observed_at"] = row["oldest_observed_at"]
    for ledger, row in status.items():
        print(f"{ledger}: pending={row['pending']} oldest_observed_at={row['oldest_observed_at'] or '-'}")
    if unreadable:
        for item in unreadable:
            print(f"UNREADABLE_SPOOL: {item['path']} ({item['reason']})", file=sys.stderr)
        return 1
    return 0


def _manifest_ids(path: Path) -> list[str]:
    payload = _read_json(path)
    calls = payload.get("calls") if isinstance(payload, dict) else None
    if not isinstance(calls, list):
        raise LedgerError(
            "INVALID_MANIFEST", f"{path}: expected an object carrying a 'calls' list"
        )
    ids: list[str] = []
    for entry in calls:
        if not isinstance(entry, dict) or not entry.get("observation_id"):
            raise LedgerError(
                "INVALID_MANIFEST", f"{path}: every call needs an observation_id"
            )
        ids.append(str(entry["observation_id"]))
    return ids


def _cli_flush(args: argparse.Namespace) -> int:
    """Drain the local outbox towards the ledger's dashboard.

    The transport is an MCP call made by an agent, not a subprocess, so this
    command has two halves and neither is optional. Without ``--mark-posted``
    it prints the batch to post and moves nothing (dry-run). With it, it
    archives the ids the agent has actually posted -- which is what lets a
    later ``check_pending`` trust the ledger again instead of reporting a
    backlog it cannot see (#22456).
    """
    ledger = args.ledger
    if args.out_dir:
        spool_dir = Path(args.out_dir)
    else:
        state_dir = Path(args.state_dir) if args.state_dir else default_state_dir()
        spool_dir = state_dir / ledger / "spool"
    pending = spool_pending(spool_dir, ledger=ledger)
    manifest = flush_manifest(ledger, pending)

    if args.mark_posted or args.mark_posted_from:
        ids = list(args.mark_posted or [])
        if args.mark_posted_from:
            ids.extend(_manifest_ids(Path(args.mark_posted_from)))
        outcome = archive_posted(spool_dir, ids)
        remaining = spool_status(spool_dir)[ledger]
        if args.json:
            print(
                json.dumps(
                    {**manifest, "archived": outcome, "remaining": remaining},
                    ensure_ascii=False,
                    indent=2,
                )
            )
        else:
            print(f"posted: moved={len(outcome['moved'])} already={len(outcome['already'])}")
            print(
                f"{ledger}: pending={remaining['pending']} "
                f"oldest_observed_at={remaining['oldest_observed_at'] or '-'}"
            )
        return 0

    if args.emit:
        target = Path(args.emit)
        assert_local_output(target, what="--emit")
        _write_text_atomic(target, json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")
    if args.json:
        print(json.dumps(manifest, ensure_ascii=False, indent=2))
    else:
        for call in manifest["calls"]:
            print(f"{call['observed_at']}  {call['observation_id']}")
        print(f"{ledger}: pending={manifest['count']} (dry-run -- nothing archived)")
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

    spool = sub.add_parser("spool", parents=[common], help="inspect the local observation outbox")
    spool.add_argument("--status", action="store_true", required=True, help="count pending envelopes")
    spool.add_argument("--out-dir", help="inspect the same local spool dir used by append")
    spool.set_defaults(func=_cli_spool_status)

    flush = sub.add_parser(
        "flush",
        parents=[common],
        help="drain the local outbox (dry-run; --mark-posted archives what was posted)",
    )
    flush.add_argument("--ledger", choices=list(LEDGERS), default=GPU_RESERVATION)
    flush.add_argument("--out-dir", help="inspect this spool dir instead of the state-dir one")
    flush.add_argument("--emit", help="write the postable batch to this local JSON file")
    flush.add_argument(
        "--mark-posted",
        nargs="+",
        metavar="ID",
        help="archive these observation ids, already posted on the dashboard",
    )
    flush.add_argument(
        "--mark-posted-from",
        metavar="MANIFEST",
        help="archive every observation id of a manifest written by --emit",
    )
    flush.add_argument("--json", action="store_true", help="emit the manifest as JSON")
    flush.set_defaults(func=_cli_flush)

    publish = sub.add_parser(
        "publish",
        parents=[common],
        help=(
            "publish the local envelopes to the git ledger branch "
            f"{GIT_LEDGER_BRANCH} (dry-run; --emit publishes)"
        ),
    )
    publish.add_argument("--ledger", choices=list(LEDGERS), default=GPU_RESERVATION)
    publish.add_argument(
        "--git",
        action="store_true",
        help="git transport on the dedicated branch (required; the only transport)",
    )
    publish.add_argument("--emit", action="store_true", help="publish for real (default is dry-run)")
    publish.add_argument(
        "--out-dir", help="publish from this spool dir instead of the state-dir one"
    )
    publish.add_argument(
        "--repo",
        help="git repository to publish from (default: the repository of this script)",
    )
    publish.add_argument(
        "--remote",
        default=GIT_LEDGER_REMOTE_DEFAULT,
        help=(
            "remote git qui porte la reference du registre GPU "
            f"(defaut : {GIT_LEDGER_REMOTE_DEFAULT} -> {GIT_LEDGER_REPO_URL}, "
            "depot PRIVE et dedie) ; la cible reste un parametre, mais le "
            "depot de travail public est refuse"
        ),
    )
    publish.add_argument(
        "--machine",
        help="target machine file (default: canonical name of this host)",
    )
    publish.add_argument("--json", action="store_true", help="emit the summary as JSON")
    publish.set_defaults(func=_cli_publish)

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
    check_pending = sub.add_parser(
        "check_pending",
        parents=[common],
        help="pre-launch gate for a GPU workload (gpu-reservation only)",
    )
    check_pending.add_argument(
        "--ledger", choices=list(LEDGERS), default=GPU_RESERVATION
    )
    check_pending.add_argument(
        "--entity", required=True,
        help="'<machine>#gpu<n>' for gpu-reservation (e.g. 'myia-ai-01#gpu2')",
    )
    check_pending.add_argument(
        "--my-lane",
        help="the calling lane ('machine:workspace'); without it no ownership "
        "can be proven and a held device is always HOLD (never OK_TO_RUN)",
    )
    check_pending.add_argument(
        "--source",
        choices=["auto", "git", "local"],
        default="auto",
        help=(
            "where the verdict reads from: 'git' = branche dediee "
            f"{GIT_LEDGER_BRANCH} (source PRIMAIRE) ; 'local' = snapshot local "
            "(un CACHE, jamais une autorite, comportement historique) ; "
            "'auto' (defaut) = git ; repli sur le cache local UNIQUEMENT si "
            "le fetch a reussi et que la branche n'existe pas (rien n'a donc "
            "jamais ete publie) ; fetch en echec = UNREADABLE (fail-CLOSED)"
        ),
    )
    check_pending.add_argument(
        "--repo",
        help="git repository to read the ledger branch from (default: this script's repository)",
    )
    check_pending.add_argument(
        "--remote",
        default=GIT_LEDGER_REMOTE_DEFAULT,
        help=(
            "remote git qui porte la reference du registre GPU "
            f"(defaut : {GIT_LEDGER_REMOTE_DEFAULT} -> {GIT_LEDGER_REPO_URL})"
        ),
    )
    check_pending.add_argument(
        "--snapshot", help="path to a prior snapshot JSON; defaults to the local state dir",
    )
    check_pending.add_argument(
        "--json", dest="json_output", action="store_true",
        help="emit a JSON object instead of 'VERDICT entity reason'",
    )
    check_pending.set_defaults(func=_cli_check_pending)

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
