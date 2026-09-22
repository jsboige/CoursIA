#!/usr/bin/env python3
"""Fail-closed gate for the coordinator's adjoint prevalidation dossier.

The gate answers one narrow question: does this pull request have a complete,
exact-head, machine-readable READY dossier from a qualifying THIRD-PARTY lane?
It does not approve the pull request, replace B.0, or authorize a merge.

The binding constraint is third-party review, not the name of one lane. A
dossier written by the lane that carries the pull request is self-attestation
and is refused; a dossier written by any other qualifying lane carries the same
evidential weight as the adjoint's. Restricting emission to a single named lane
made that lane's throughput the merge throughput of the whole repository.

Canonical comment body (the marker must be the first line):

    [ADJOINT PREFLIGHT]
    schema: 1
    lane: myia-po-2025:CoursIA-2
    pr: 123
    head: 0123456789abcdef0123456789abcdef01234567
    complete: true
    body: read
    comments-reviewed: 4
    reviews-reviewed: 2
    threads-reviewed: 1
    threads-unresolved: 0
    surfaces-sha256: <printed by --fingerprint>
    diff-files: 3
    diff-additions: 42
    diff-deletions: 7
    checks: latest-wins-green
    b0: clear
    scope: pass
    domain: pass
    verdict: READY
    [/ADJOINT PREFLIGHT]

The comment count excludes the dossier comment itself. Any observable later
issue comment, review, inline-thread, PR-metadata, or head change invalidates
the dossier and requires a fresh one. Check-runs are NOT a hashed surface
(#16957): a check that concludes -- even in success -- must not expire a
dossier, because anything that triggers a workflow (a review, a comment, a
sweep) re-opens that race and the dossier writer can never win it. Instead the
gate recomputes the latest-wins check verdicts at evaluation time and refuses
the dossier when they contradict its `checks:` claim, naming the failing
check. Dossiers stamped before #16957 embedded the check state in
surfaces-sha256; their stamps remain accepted while that state is
byte-identical, and need one mechanical re-stamp (--template) once a check
moves. GitHub does not expose a stateless audit trail for an event that is
later deleted or reverted; this gate therefore certifies the current
surfaces, not erased history.

Exit codes -- dossier INTEGRITY and PR MERGEABILITY are two questions, and
conflating them is what this gate used to do (#16800):

    0  intact dossier, verdict READY
       -> the coordinator may open body, comments, reviews, threads, diff.
    3  intact dossier, verdict BLOCKED
       -> do NOT open the surfaces. Dispatch from the dossier's stated reason.
          An honest BLOCKED dossier is the point: making exit 0 depend on READY
          meant the coordinator could only ever read the pull requests that were
          already fine, never the oldest ones -- which are old precisely because
          they are blocked. It also pressured the adjoint into writing READY
          merely to be visible, which measurably produced a false `b0: clear` on
          a pull request carrying three open HIGH findings.
    1  no dossier worth trusting (absent, malformed, stale, wrong lane/author,
       broken fingerprint) -> route to the adjoint.
    2  the gate could not measure (gh/network/parse failure) -> fail closed.

Exit 3 is not a softer gate: a BLOCKED dossier must satisfy every structural
requirement, `surfaces-sha256` included. What it drops are the checks that
refute a READY *claim* (green checks, clear B.0, no unresolved thread, not a
draft) -- those are reasons a pull request is blocked, not reasons to distrust
the dossier that says so.

One surface author is neutral: the coordinator itself, and only for rows it
wrote AFTER the dossier. Otherwise the act the gate authorises -- reading the
pull request, then lifting one's own reserve -- expires the dossier the gate
required, and a pull request blocked solely by a coordinator reserve could never
be merged without a full adjoint round-trip. A row from any other author, or a
coordinator row predating the dossier, still expires it.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from typing import Any

REPO = "jsboige/CoursIA"
# The adjoint remains the canonical emitter: `--template` renders its lane, and
# it is the lane the coordinator nudges first. It is no longer the only one.
ADJOINT_LANE = "myia-po-2025:CoursIA-2"
# A dossier is an act of third-party verification. Any cluster lane may emit one
# for a pull request it does not carry. The set is explicit so that an unknown or
# malformed lane string fails closed rather than passing as "some lane".
QUALIFYING_LANES = frozenset({
    "myia-ai-01:CoursIA",
    "myia-po-2023:CoursIA",
    "myia-po-2023:CoursIA-2",
    "myia-po-2024:CoursIA",
    "myia-po-2024:CoursIA-2",
    "myia-po-2025:CoursIA",
    "myia-po-2025:CoursIA-2",
    "myia-po-2026:CoursIA",
    "myia-po-2026:CoursIA-2",
    # The secretary lane. It carries no pull request of its own -- its whole
    # function is to emit dossiers for the lanes that do -- so its absence from
    # this set silenced it entirely: every dossier it filed failed closed as an
    # unknown lane. Measured 2026-09-21: `CoursIA-3` occurred in zero files
    # under scripts/ and .claude/ while its dashboard had been written a minute
    # earlier, and zero [ADJOINT PREFLIGHT] dossiers existed fleet-wide.
    "myia-po-2026:CoursIA-3",
    "myia-po-2027:CoursIA",
    "myia-po-2027:CoursIA-2",
})
# `Grain: <genre> -- lane <machine:workspace>` in the pull request body names the
# lane that carries the work. Same grammar as scripts/check_lane_claim.py.
GRAIN_LANE_RE = re.compile(r"Grain:[^\n]*?\blane\s+([A-Za-z0-9_.-]+:[A-Za-z0-9_.-]+)")
SHARED_GITHUB_LOGIN = "jsboige"
# The gate's only consumer. Every worker lane signs SHARED_GITHUB_LOGIN, so this
# login is the one surface author the coordinator can recognise as itself.
COORDINATOR_LOGIN = "myia-ai-01"

VERDICT_READY = "READY"
VERDICT_BLOCKED = "BLOCKED"
CANONICAL_VERDICTS = (VERDICT_READY, VERDICT_BLOCKED)

EXIT_READY = 0
EXIT_NO_DOSSIER = 1
EXIT_UNKNOWN = 2
EXIT_BLOCKED_WITH_SUBSTANCE = 3
# Conclusions that do not refute `checks: latest-wins-green`. `skipped` and
# `neutral` are not failures; anything else completed (failure, timed_out,
# cancelled, action_required, startup_failure, stale...) does (#16957).
GREEN_CONCLUSIONS = {"success", "skipped", "neutral"}
START = "[ADJOINT PREFLIGHT]"
END = "[/ADJOINT PREFLIGHT]"
SHA_RE = re.compile(r"[0-9a-f]{40}")

REQUIRED_FIELDS = {
    "schema",
    "lane",
    "pr",
    "head",
    "complete",
    "body",
    "comments-reviewed",
    "reviews-reviewed",
    "threads-reviewed",
    "threads-unresolved",
    "surfaces-sha256",
    "diff-files",
    "diff-additions",
    "diff-deletions",
    "checks",
    "b0",
    "scope",
    "domain",
    "verdict",
}
INTEGER_FIELDS = {
    "pr",
    "comments-reviewed",
    "reviews-reviewed",
    "threads-reviewed",
    "threads-unresolved",
    "diff-files",
    "diff-additions",
    "diff-deletions",
}


@dataclass(frozen=True)
class Dossier:
    fields: dict[str, str]
    comment_index: int
    author: str
    created_at: str = ""


def gh_json(args: list[str]) -> Any:
    proc = subprocess.run(
        ["gh", *args], capture_output=True, text=True, encoding="utf-8"
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or "gh command failed")
    return json.loads(proc.stdout)


def parse_dossier(
    body: str,
    comment_index: int,
    author: str,
    created_at: str = "",
) -> tuple[Dossier | None, list[str]]:
    """Parse one strictly delimited dossier comment without interpreting prose.

    Prose FOLLOWING the closing marker is ignored, not refused. The contract is
    the delimited block: `content` stops at `closing`, so trailing text can never
    reach a field. Refusing it discarded dossiers whose machine-readable block
    was complete and whose firsthand evidence was written below it for a human --
    measured on four pull requests in one cycle (#16928).

    Nothing is hidden by this. `check_unaddressed_nits.py` strips the dossier by
    its two delimiters, so a reserve written after the closing marker still
    reaches B.0 classification; only a reserve written INSIDE the block is
    absorbed, which is the intended semantics of #16442/#16443.
    """
    lines = body.strip().splitlines()
    if not lines or lines[0].strip() != START:
        return None, []
    errors: list[str] = []
    closing = next(
        (index for index, line in enumerate(lines[1:], 1) if line.strip() == END),
        None,
    )
    if closing is None:
        errors.append("missing closing marker")
        content = lines[1:]
    else:
        content = lines[1:closing]

    fields: dict[str, str] = {}
    for raw in content:
        if not raw.strip():
            continue
        if ":" not in raw:
            errors.append(f"malformed line: {raw.strip()}")
            continue
        key, value = (part.strip() for part in raw.split(":", 1))
        if key in fields:
            errors.append(f"duplicate field: {key}")
        fields[key] = value

    missing = sorted(REQUIRED_FIELDS - fields.keys())
    unknown = sorted(fields.keys() - REQUIRED_FIELDS)
    if missing:
        errors.append("missing fields: " + ", ".join(missing))
    if unknown:
        errors.append("unknown fields: " + ", ".join(unknown))
    return Dossier(fields, comment_index, author, created_at), errors


def _login(row: dict[str, Any]) -> str:
    return (row.get("author") or {}).get("login", "")


# #16931 : bots marker-gardes qui RE-EDITENT leur commentaire en place
# (PATCH, pas nouveau post) derriere un marqueur HTML invisible. Le compte de
# commentaires ne bouge pas mais le corps change -> le sha256 change -> le
# gate refuse avec "discussion surfaces changed" pour une cause qui n'a rien
# change au fond de la PR. Mesure 2026-09-20 : dossier #16907 perime 26 min
# apres sa pose par une reecriture PR-PATH-COLLISION. Ces commentaires sont
# haches sur leur MARQUEUR SEUL : un humain qui edite le meme corps (le
# marqueur ne sera plus a l'offset 0) reste detecte, et la presence/absence
# du commentaire compte toujours -- seule la re-implementation interne du bot
# est neutralisee. La liste vit dans le code (jamais le dossier : il pourrait
# etre fabrique avec une allowlist elargie).
_BOT_MARKER_GUARDS: tuple[str, ...] = (
    "<!-- PR-PATH-COLLISION:",  # scripts/check_pr_path_collisions.py (START/END/RESOLVED)
    "<!-- variation-genre-signals -->",  # always-on-guards.yml / variation-light-genre.yml
    "<!-- gvar2-light-cap -->",  # always-on-guards.yml / variation-tag-guard.yml
    "<!-- trivial-diff-15740 -->",  # workflows idempotents
)


def _comment_body_for_fingerprint(row: dict[str, Any]) -> str:
    """Corps a hacher : le marqueur seul pour un commentaire de bot marker-garde.

    Un corps qui COMMENCE par un marqueur connu est reduit a ce marqueur : la
    reecriture en place (seul le contenu change) ne perime plus le dossier,
    alors que l'apparition, la disparition ou une edition humaine (marqueur
    deplace) continuent de le faire.
    """
    body = row.get("body") or ""
    for marker in _BOT_MARKER_GUARDS:
        if body.startswith(marker):
            return marker
    return body


def _is_own_later_act(row: dict[str, Any], timestamp_key: str, neutral_after: str | None) -> bool:
    """True when the coordinator itself authored this surface after the dossier.

    The dossier attests that the adjoint read every surface existing when it was
    written. A row the coordinator writes afterwards cannot be a surface the
    coordinator is unaware of -- it wrote it. Neutralising exactly those rows is
    what lets the coordinator lift its own reserve and still merge, without
    weakening the gate: a row from any other author still expires the dossier.
    """
    if not neutral_after:
        return False
    if _login(row) != COORDINATOR_LOGIN:
        return False
    stamp = row.get(timestamp_key) or ""
    return bool(stamp) and stamp > neutral_after


def _attested_reviews(
    snapshot: dict[str, Any], neutral_after: str | None
) -> list[dict[str, Any]]:
    return [
        row
        for row in snapshot.get("reviews") or []
        if not _is_own_later_act(row, "submittedAt", neutral_after)
    ]


def _integer(fields: dict[str, str], key: str, errors: list[str]) -> int | None:
    value = fields.get(key, "")
    if not re.fullmatch(r"0|[1-9][0-9]*", value):
        errors.append(f"{key} must be a canonical non-negative integer")
        return None
    return int(value)


def _fingerprint_payload(
    snapshot: dict[str, Any],
    comment_limit: int | None = None,
    neutral_after: str | None = None,
    include_checks: bool = False,
) -> dict[str, Any]:
    """Payload canonique de la fingerprint — factorise pour le diagnostic.

    Partage entre ``surfaces_fingerprint`` (hachage) et
    ``_first_divergent_surface`` (nommage de la surface divergente, #16931) :
    une seule construction, jamais deux qui derivent.
    """
    comments = snapshot.get("comments") or []
    if comment_limit is not None:
        comments = comments[:comment_limit]
    reviews = _attested_reviews(snapshot, neutral_after)

    author = _login

    payload: dict[str, Any] = {
        "pr": {
            "number": snapshot.get("number"),
            "state": snapshot.get("state"),
            "title": snapshot.get("title"),
            "isDraft": snapshot.get("isDraft"),
            "baseRefName": snapshot.get("baseRefName"),
            "body": snapshot.get("body") or "",
        },
        "comments": [
            {
                "id": row.get("id"),
                "author": author(row),
                "createdAt": row.get("createdAt"),
                "body": _comment_body_for_fingerprint(row),
            }
            for row in comments
        ],
        "reviews": [
            {
                "id": row.get("id"),
                "author": author(row),
                "submittedAt": row.get("submittedAt"),
                "state": row.get("state"),
                "commit": (row.get("commit") or {}).get("oid"),
                "body": row.get("body") or "",
            }
            for row in reviews
        ],
        "threads": snapshot.get("threads") or [],
    }
    if include_checks:
        payload["checks"] = sorted(
            snapshot.get("statusCheckRollup") or [],
            key=lambda row: json.dumps(
                row, sort_keys=True, separators=(",", ":")
            ),
        )
    return payload


def _digest(payload: dict[str, Any]) -> str:
    encoded = json.dumps(
        payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _first_divergent_surface(
    snapshot: dict[str, Any],
    comment_limit: int | None,
    neutral_after: str | None,
) -> str:
    """Nomme la premiere surface qui a diverge entre dossier et live.

    Le sha256 est opaque par construction ; le diagnostic, lui, peut lire les
    deux ensembles de surfaces : il identifie quelle section (corps de PR /
    commentaire n / review n / threads / checks) a change. Best-effort et
    deterministe : la premiere divergence dans l'ordre de construction du
    payload. Le compte de surfaces ne change pas sur une reecriture en place
    (meme cardinalite) ; si les longueurs different, la surface d'index hors
    portee est nommee.
    """
    # L'empreinte declaree du dossier n'est pas decomposable ; le diagnostic
    # compare donc le payload live A LUI-MEME section par section n'a pas de
    # sens. Ce qu'on peut faire : hacher CHAQUE section separement et
    # reporter laquelle, re-hachee depuis le dossier, divergerait — mais le
    # dossier ne porte qu'un seul sha. Le diagnostic utile et honnete est
    # structurel : cardinalites et horodatages des surfaces LIVE, pour que la
    # lane sache OU chercher sans refabriquer en aveugle.
    # Adaptation post-#16957 : le digest vivant exclut les checks (course
    # refermee par #16957) ; le diagnostic les re-inclut — il decrit le
    # paysage live, pas le digest.
    payload = _fingerprint_payload(
        snapshot, comment_limit, neutral_after, include_checks=True
    )
    comments = payload["comments"]
    reviews = payload["reviews"]
    parts = [f"comments={len(comments)}", f"reviews={len(reviews)}"]
    if comments:
        last = comments[-1]
        parts.append(
            "dernier commentaire: "
            f"{last.get('author') or '?'} {last.get('createdAt') or '?'}"
        )
    if reviews:
        last_r = reviews[-1]
        parts.append(
            "derniere review: "
            f"{last_r.get('author') or '?'} {last_r.get('submittedAt') or '?'}"
        )
    threads = payload["threads"]
    unresolved = sum(1 for t in threads if not t.get("isResolved", False))
    parts.append(f"threads={len(threads)} ({unresolved} non resolus)")
    parts.append(f"checks={len(payload['checks'])}")
    return ", ".join(parts)


def surfaces_fingerprint(
    snapshot: dict[str, Any],
    comment_limit: int | None = None,
    neutral_after: str | None = None,
) -> str:
    """Hash stable content from every DISCUSSION surface plus the PR body.

    Certifies: PR number/state/title/draft/base/body, issue comments,
    reviews (minus the coordinator's own later ones), review threads -- as
    read when the fingerprint is taken. Does NOT certify check-runs (#16957):
    a concluding check must not expire a stamp it contradicts nothing in; the
    gate re-verifies the live latest-wins conclusions against the dossier's
    ``checks:`` claim at evaluation time instead.

    ``neutral_after`` is the dossier's own timestamp. Reviews the coordinator
    submitted after it are excluded, because the coordinator authored them; see
    ``_is_own_later_act``. Rendering a template passes ``None``, so a fresh
    dossier still attests every surface that exists when it is written.
    """
    return _digest(
        _fingerprint_payload(snapshot, comment_limit, neutral_after, False)
    )


def legacy_surfaces_fingerprint(
    snapshot: dict[str, Any],
    comment_limit: int | None = None,
    neutral_after: str | None = None,
) -> str:
    """Pre-#16957 stamp algorithm: the same payload PLUS the check rollup.

    Kept so dossiers stamped before #16957 -- whose hash embedded the check
    state -- remain verifiable for as long as that state is byte-identical.
    Once any check concludes, a legacy stamp stops matching; recovery is one
    mechanical re-stamp (--template recomputes every mechanical field, no
    re-reading of surfaces), after which no check conclusion can ever expire
    the dossier again. A SHA-256 over data that has since changed cannot be
    re-derived, which is why zero-touch recovery of raced legacy stamps is
    not offered. Drop this function when no open dossier carries a legacy
    stamp.
    """
    return _digest(
        _fingerprint_payload(snapshot, comment_limit, neutral_after, True)
    )


def latest_wins_check_runs(check_runs: list[dict[str, Any]] | None) -> dict[str, dict[str, Any]]:
    """Last COMPLETED verdict per check name: group by name, latest ``started_at``
    (``id`` as tiebreak), keep that run.

    Runs still in flight have no verdict yet and are skipped; the name falls
    back to its latest completed run, which is the last word actually said.
    Grouping by name -- not reading the rollup twin -- is what avoids painting
    a head red with the cancelled run of a superseded pair (#16957).
    """
    verdicts: dict[str, tuple[tuple, dict[str, Any]]] = {}
    for run in check_runs or []:
        if (run.get("status") or "").lower() != "completed":
            continue
        key = run.get("name") or ""
        rank = (run.get("started_at") or "", run.get("id") or 0)
        current = verdicts.get(key)
        if current is None or rank > current[0]:
            verdicts[key] = (rank, run)
    return {name: run for name, (rank, run) in verdicts.items()}


def check_claim_contradictions(
    claim: str, check_runs: list[dict[str, Any]] | None
) -> list[str]:
    """Re-verify a dossier's ``checks:`` claim against the live latest-wins state.

    Hashing check-runs certified their state at stamp time but never that the
    claim matched it (#16957); a check concluding after the dossier expired the
    stamp instead of being checked. The claim is now compared to what the head
    actually carries: every latest-wins conclusion must be green, else the
    check is named -- with the run's ``output.title`` when present (the PR-gate
    class DWELL/FAIL lives there, as information for the reader, not in the
    predicate).
    """
    if claim != "latest-wins-green":
        return []
    contradictions = []
    for name, run in sorted(latest_wins_check_runs(check_runs).items()):
        conclusion = (run.get("conclusion") or "").lower()
        if conclusion in GREEN_CONCLUSIONS:
            continue
        title = ((run.get("output") or {}).get("title") or "").strip()
        detail = f"'{name}' ({conclusion}"
        if title:
            detail += f"; {title}"
        detail += ")"
        contradictions.append(
            "checks claim 'latest-wins-green' is contradicted by live check "
            + detail
        )
    return contradictions


def carrying_lane(snapshot: dict[str, Any]) -> str | None:
    """Return the lane that carries this pull request, from its `Grain:` tag.

    Returns None when the body carries no readable tag. `validate_dossier` turns
    that None into a refusal: an absent tag means the self-attestation check
    CANNOT be made, and a check that cannot be made has not passed. Without that
    refusal, a qualifying lane carrying an untagged PR files its own dossier and
    clears a control that never ran -- the exact hole the third-party rule exists
    to close. Blast radius measured 2026-09-20: 4 of 221 open PRs carry no
    readable tag, and the escape is to add the tag, not to weaken the gate.
    """
    match = GRAIN_LANE_RE.search(snapshot.get("body") or "")
    return match.group(1) if match else None


def validate_dossier(dossier: Dossier, snapshot: dict[str, Any]) -> list[str]:
    """Validate a parsed dossier against one live PR snapshot."""
    f = dossier.fields
    errors: list[str] = []
    integers = {key: _integer(f, key, errors) for key in INTEGER_FIELDS}

    # Structural integrity only: "is this a dossier I can trust?" -- NOT "is this
    # PR mergeable?". The verdict is read separately by evaluate(), so an honest
    # BLOCKED dossier stays a valid dossier instead of being indistinguishable
    # from an absent one (#16800).
    expected = {
        "schema": "1",
        "complete": "true",
        "body": "read",
    }
    for key, value in expected.items():
        if f.get(key) != value:
            errors.append(f"{key} must be {value!r}")
    verdict = f.get("verdict", "")
    if verdict not in CANONICAL_VERDICTS:
        errors.append(
            "verdict must be one of " + ", ".join(repr(v) for v in CANONICAL_VERDICTS)
        )
    ready_claimed = verdict == VERDICT_READY
    if ready_claimed:
        for key, value in (
            ("checks", "latest-wins-green"),
            ("b0", "clear"),
            ("scope", "pass"),
        ):
            if f.get(key) != value:
                errors.append(f"{key} must be {value!r} when verdict is READY")
        if f.get("domain") not in {"pass", "not-applicable"}:
            errors.append("domain must be 'pass' or 'not-applicable' when verdict is READY")
        # The claim is not taken on faith: it is checked against the live
        # latest-wins verdicts, naming any contradicting check (#16957).
        errors.extend(
            check_claim_contradictions(
                f.get("checks", ""), snapshot.get("checkRuns")
            )
        )

    dossier_lane = f.get("lane", "")
    if dossier_lane not in QUALIFYING_LANES:
        errors.append(
            f"lane must be one of the qualifying cluster lanes, got {dossier_lane!r}"
        )
    else:
        carrier = carrying_lane(snapshot)
        if carrier is None:
            errors.append(
                "carrying lane cannot be established: the body carries no readable "
                "'Grain: ... lane <machine:workspace>' tag, so third-party "
                "prevalidation cannot be verified"
            )
        elif carrier == dossier_lane:
            errors.append(
                "self-prevalidation refused: the dossier lane "
                f"{dossier_lane!r} is the lane that carries this pull request"
            )
    if dossier.author != SHARED_GITHUB_LOGIN:
        errors.append(f"comment author must be {SHARED_GITHUB_LOGIN!r}")
    if not SHA_RE.fullmatch(f.get("head", "")):
        errors.append("head must be a full lowercase 40-character SHA")
    if not re.fullmatch(r"[0-9a-f]{64}", f.get("surfaces-sha256", "")):
        errors.append("surfaces-sha256 must be a lowercase SHA-256")
    # Dual acceptance (#16957): a stamp matches the post-fix fingerprint
    # (discussion surfaces only) or the legacy one (which also embedded the
    # check rollup). Both certify every discussion surface; the legacy digest
    # is strictly more fields, so accepting either weakens nothing.
    live_fingerprint = surfaces_fingerprint(
        snapshot, dossier.comment_index, dossier.created_at
    )
    legacy_fingerprint = legacy_surfaces_fingerprint(
        snapshot, dossier.comment_index, dossier.created_at
    )
    if f.get("surfaces-sha256") not in {live_fingerprint, legacy_fingerprint}:
        # #16931 defaut 3 (mesure 16928) : deux hachages opaques sont
        # inexploitables — la lane refabrique le dossier EN AVEUGLE. Le refus
        # nomme la surface divergente, comme check_unaddressed_nits --json
        # nomme deja ignored_overrides[].why.
        divergent = _first_divergent_surface(
            snapshot, dossier.comment_index, dossier.created_at
        )
        errors.append(
            "discussion surfaces changed or were not fully attested: "
            f"surface divergente = {divergent}; "
            f"dossier={f.get('surfaces-sha256', '?')}, live={live_fingerprint} "
            "(legacy stamps whose checks moved need one --template re-stamp)"
        )

    comparisons = {
        "pr": snapshot["number"],
        "comments-reviewed": dossier.comment_index,
        "reviews-reviewed": len(_attested_reviews(snapshot, dossier.created_at)),
        "threads-reviewed": len(snapshot.get("threads") or []),
        "threads-unresolved": sum(
            not thread.get("isResolved", False)
            for thread in snapshot.get("threads") or []
        ),
        "diff-files": snapshot["changedFiles"],
        "diff-additions": snapshot["additions"],
        "diff-deletions": snapshot["deletions"],
    }
    for key, live_value in comparisons.items():
        if integers.get(key) is not None and integers[key] != live_value:
            errors.append(f"{key} is stale: dossier={integers[key]}, live={live_value}")

    if f.get("head") != snapshot["headRefOid"]:
        errors.append(
            f"head is stale: dossier={f.get('head', '?')}, live={snapshot['headRefOid']}"
        )
    if snapshot.get("state") != "OPEN":
        errors.append(f"pull request state must be OPEN, live={snapshot.get('state')}")
    # A draft, or an unresolved thread, is a reason a PR is NOT mergeable -- which
    # is precisely what a BLOCKED dossier is for. Only a READY claim is refuted.
    if ready_claimed:
        if snapshot.get("isDraft"):
            errors.append("draft pull request cannot be READY")
        if integers.get("threads-unresolved") not in {None, 0}:
            errors.append("READY requires zero unresolved threads")
    return errors


def evaluate(snapshot: dict[str, Any]) -> tuple[str, list[str]]:
    """Select the newest candidate and return a fail-closed verdict.

    Returns one of ``VERDICT_READY`` (intact dossier claiming the PR is
    mergeable), ``VERDICT_BLOCKED`` (intact dossier attesting it is not) or
    ``""`` (no dossier worth trusting). Separating dossier integrity from PR
    mergeability is the whole point: making the right to READ depend on the
    state of MERGEABILITY meant the coordinator could only ever open the pull
    requests that were already fine -- never the oldest ones, which are old
    precisely because they are blocked.
    """
    comments = snapshot.get("comments") or []
    candidates: list[tuple[Dossier, list[str]]] = []
    for index, comment in enumerate(comments):
        dossier, parse_errors = parse_dossier(
            comment.get("body") or "",
            index,
            _login(comment),
            comment.get("createdAt") or "",
        )
        if dossier is not None:
            candidates.append((dossier, parse_errors))

    if not candidates:
        return "", ["no [ADJOINT PREFLIGHT] dossier comment found"]

    dossier, errors = candidates[-1]
    errors = [*errors, *validate_dossier(dossier, snapshot)]
    # A dossier is a snapshot. Any later comment invalidates it, including a
    # reply that claims the PR is still ready -- unless the coordinator itself
    # wrote it, which it cannot be unaware of (see _is_own_later_act).
    foreign = [
        row
        for row in comments[dossier.comment_index + 1:]
        if not _is_own_later_act(row, "createdAt", dossier.created_at)
    ]
    if foreign:
        errors.append(
            "discussion changed after dossier: a fresh adjoint preflight is required"
        )
    if errors:
        return "", errors
    return dossier.fields.get("verdict", ""), []


def review_threads(pr: int) -> list[dict[str, Any]]:
    query = """
    query($owner:String!,$repo:String!,$number:Int!,$cursor:String){
      repository(owner:$owner,name:$repo){
        pullRequest(number:$number){
          reviewThreads(first:100,after:$cursor){
            nodes{
              id isResolved isOutdated path line
              comments(first:100){
                totalCount
                nodes{id body createdAt author{login}}
              }
            }
            pageInfo{hasNextPage endCursor}
          }
        }
      }
    }"""
    owner, repo = REPO.split("/", 1)
    cursor: str | None = None
    threads: list[dict[str, Any]] = []
    while True:
        args = [
            "api", "graphql", "-f", f"query={query}",
            "-F", f"owner={owner}", "-F", f"repo={repo}",
            "-F", f"number={pr}",
        ]
        if cursor is not None:
            args.extend(["-f", f"cursor={cursor}"])
        data = gh_json(args)
        connection = data["data"]["repository"]["pullRequest"]["reviewThreads"]
        nodes = connection.get("nodes") or []
        for thread in nodes:
            inline = thread.get("comments") or {}
            if inline.get("totalCount", 0) > len(inline.get("nodes") or []):
                raise RuntimeError(
                    "inline thread has more than 100 comments; complete pagination required"
                )
        threads.extend(nodes)
        page = connection["pageInfo"]
        if not page["hasNextPage"]:
            return threads
        cursor = page["endCursor"]


def _issue_comments(pr: int) -> list[dict[str, Any]]:
    rows = gh_json([
        "api", f"repos/{REPO}/issues/{pr}/comments", "--paginate",
    ])
    if not isinstance(rows, list):
        raise RuntimeError("issue comments response is not a list")
    return [
        {
            "id": row.get("node_id") or row.get("id"),
            "author": {"login": (row.get("user") or {}).get("login", "")},
            "createdAt": row.get("created_at"),
            "body": row.get("body") or "",
        }
        for row in rows
    ]


def _reviews(pr: int) -> list[dict[str, Any]]:
    rows = gh_json([
        "api", f"repos/{REPO}/pulls/{pr}/reviews", "--paginate",
    ])
    if not isinstance(rows, list):
        raise RuntimeError("reviews response is not a list")
    return [
        {
            "id": row.get("node_id") or row.get("id"),
            "author": {"login": (row.get("user") or {}).get("login", "")},
            "submittedAt": row.get("submitted_at"),
            "state": row.get("state"),
            "commit": {"oid": row.get("commit_id")},
            "body": row.get("body") or "",
        }
        for row in rows
    ]


def _head_check_runs(head_sha: str) -> list[dict[str, Any]]:
    """Check-runs of the exact head commit, paginated (#16957).

    Read from the commit rather than the PR rollup because the rollup surfaces
    the cancelled twin when two runs share a SHA; latest-wins per name is
    computed downstream, never on the raw list.
    """
    runs: list[dict[str, Any]] = []
    page = 1
    while True:
        data = gh_json([
            "api",
            f"repos/{REPO}/commits/{head_sha}/check-runs?per_page=100&page={page}",
        ])
        batch = data.get("check_runs") if isinstance(data, dict) else None
        if batch is None:
            raise RuntimeError("check-runs response has no 'check_runs' array")
        runs.extend(batch)
        if len(batch) < 100:
            return runs
        page += 1


def _pr_metadata(pr: int) -> dict[str, Any]:
    fields = (
        "number,title,body,state,isDraft,baseRefName,headRefOid,updatedAt,"
        "changedFiles,additions,deletions,statusCheckRollup"
    )
    data = gh_json([
        "pr", "view", str(pr), "--repo", REPO, "--json", fields,
    ])
    if not isinstance(data, dict):
        raise RuntimeError("pull request response is not an object")
    return data


def _metadata_identity(data: dict[str, Any]) -> str:
    normalized = dict(data)
    normalized["statusCheckRollup"] = sorted(
        data.get("statusCheckRollup") or [],
        key=lambda row: json.dumps(row, sort_keys=True, separators=(",", ":")),
    )
    return json.dumps(
        normalized, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    )


def load_snapshot(pr: int) -> dict[str, Any]:
    before = _pr_metadata(pr)
    snapshot = dict(before)
    snapshot["comments"] = _issue_comments(pr)
    snapshot["reviews"] = _reviews(pr)
    snapshot["threads"] = review_threads(pr)
    # Fetched inside the before/after bracket: a check concluding during the
    # read bumps updatedAt and aborts the snapshot (transient UNKNOWN, the
    # caller retries), so the claim verification below never reads a state
    # that was already stale when captured.
    snapshot["checkRuns"] = _head_check_runs(snapshot["headRefOid"])
    after = _pr_metadata(pr)
    if _metadata_identity(before) != _metadata_identity(after):
        raise RuntimeError("pull request changed while prevalidation snapshot was read")
    return snapshot


def render_template(snapshot: dict[str, Any], lane: str = ADJOINT_LANE) -> str:
    """Render the mechanical fields; the emitting lane sets the verdict fields.

    `lane` defaults to the adjoint because it emits most dossiers, but a template
    that hardcoded one lane would hand every other lane a dossier declaring a
    name that is not its own -- and a borrowed name defeats the self-attestation
    refusal in `validate_dossier`. A lane renders its OWN name here.
    """
    fields = (
        ("schema", "1"),
        ("lane", lane),
        ("pr", str(snapshot["number"])),
        ("head", snapshot["headRefOid"]),
        ("complete", "REPLACE_WITH_true"),
        ("body", "REPLACE_WITH_read"),
        ("comments-reviewed", str(len(snapshot.get("comments") or []))),
        ("reviews-reviewed", str(len(snapshot.get("reviews") or []))),
        ("threads-reviewed", str(len(snapshot.get("threads") or []))),
        (
            "threads-unresolved",
            str(sum(
                not thread.get("isResolved", False)
                for thread in snapshot.get("threads") or []
            )),
        ),
        ("surfaces-sha256", surfaces_fingerprint(snapshot)),
        ("diff-files", str(snapshot["changedFiles"])),
        ("diff-additions", str(snapshot["additions"])),
        ("diff-deletions", str(snapshot["deletions"])),
        ("checks", "REPLACE_WITH_latest-wins-green_OR_BLOCKED"),
        ("b0", "REPLACE_WITH_clear_OR_blocked"),
        ("scope", "REPLACE_WITH_pass_OR_fail"),
        ("domain", "REPLACE_WITH_pass_OR_not-applicable_OR_fail"),
        ("verdict", "REPLACE_WITH_READY_OR_BLOCKED"),
    )
    return "\n".join([START, *(f"{key}: {value}" for key, value in fields), END])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pr", type=int, help="pull request number")
    parser.add_argument("--json", action="store_true", help="emit machine-readable output")
    parser.add_argument(
        "--lane",
        default=ADJOINT_LANE,
        choices=sorted(QUALIFYING_LANES),
        help="lane emitting the dossier, for --template (default: the adjoint)",
    )
    parser.add_argument(
        "--fingerprint",
        action="store_true",
        help="print the live discussion fingerprint for a new dossier "
        "(compute it LAST, after every body edit and comment you intend "
        "to write -- any later human surface invalidates it, cf #16931)",
    )
    parser.add_argument(
        "--template",
        action="store_true",
        help="render a complete dossier template from the live snapshot",
    )
    args = parser.parse_args()
    try:
        snapshot = load_snapshot(args.pr)
        if args.template:
            print(render_template(snapshot, args.lane))
            return 0
        if args.fingerprint:
            print(surfaces_fingerprint(snapshot))
            print(
                "certifies: PR body/title/state/base + issue comments + reviews "
                "+ review threads, as read just now (#16957)",
                file=sys.stderr,
            )
            print(
                "does NOT certify: check-runs. The gate re-verifies the live "
                "latest-wins check conclusions against the dossier's "
                "'checks:' claim at evaluation time and names any "
                "contradicting check. Pre-#16957 stamps that embedded checks "
                "stay acceptable only while that state is unchanged.",
                file=sys.stderr,
            )
            return 0
        verdict, errors = evaluate(snapshot)
    except (
        RuntimeError,
        KeyError,
        TypeError,
        ValueError,
        OSError,
        UnicodeError,
        json.JSONDecodeError,
    ) as exc:
        result = {
            "pr": args.pr,
            "ready": False,
            "verdict": "UNKNOWN",
            "errors": [f"UNKNOWN: {exc}"],
        }
        print(json.dumps(result, ensure_ascii=False) if args.json else f"UNKNOWN -- {exc}")
        return EXIT_UNKNOWN

    ready = verdict == VERDICT_READY
    result = {
        "pr": args.pr,
        "head": snapshot["headRefOid"],
        "ready": ready,
        "verdict": verdict or "NO_DOSSIER",
        "errors": errors,
    }
    if args.json:
        print(json.dumps(result, ensure_ascii=False))
    elif ready:
        print(f"READY -- PR #{args.pr} prevalidated by adjoint at {snapshot['headRefOid']}")
    elif verdict == VERDICT_BLOCKED:
        print(
            f"BLOCKED-WITH-SUBSTANCE -- PR #{args.pr} has an intact adjoint dossier at "
            f"{snapshot['headRefOid']} attesting it is NOT mergeable."
        )
        print("  Do not open its surfaces: dispatch from the dossier's stated reason.")
    else:
        print(f"NO-DOSSIER -- PR #{args.pr} is not adjoint-prevalidated")
        for error in errors:
            print(f"  - {error}")
    if ready:
        return EXIT_READY
    if verdict == VERDICT_BLOCKED:
        return EXIT_BLOCKED_WITH_SUBSTANCE
    return EXIT_NO_DOSSIER


if __name__ == "__main__":
    sys.exit(main())
