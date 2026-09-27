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

The `b0:` claim is re-verified the same way: when a dossier claims READY
with `b0: clear`, the gate runs the B.0 organ (`check_unaddressed_nits.py`)
and refuses the dossier if the organ still finds an unlifted remark, naming
each one. A green gate therefore no longer hides a red B.0. It still does not
dispense with reading the surfaces: the organ only sees its markers, and who
lifted a remark, when, and on what substance are read by hand (CLAUDE.md §B.0).

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

Cas FROZEN (rc 3 aussi) : un dossier READY portant une PR d'une campagne
gelee par un veto user (#17040) reste refuse -- ni le dossier ni B.0 ne
lisent un veto pose sur une issue. Le gate le lit au verdict via le module
partage ``frozen_campaigns`` (dispatch a la lane auteure, pas de merge).

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
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from typing import Any

try:
    import gh_identity
    import check_unaddressed_nits
except ImportError:  # charge via importlib dans les tests (hors scripts/)
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import gh_identity  # type: ignore[no-redef]
    import check_unaddressed_nits  # type: ignore[no-redef]

# Campagnes gelees par veto user (#17040) : definition PARTAGEE avec
# merge_ready dans scripts/coordination/frozen_campaigns.py. Ce gate ne peut
# pas importer merge_ready (merge_ready importe deja ce gate), les deux
# importent le module : un seul lecteur du veto, jamais deux qui derivent.
_COORDINATION_DIR = os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "coordination"
)
if _COORDINATION_DIR not in sys.path:
    sys.path.insert(0, _COORDINATION_DIR)
from frozen_campaigns import frozen_umbrella_exclusion  # noqa: E402

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
# The four contract fields that must sit at their READY value for a dossier to
# claim the pull request is mergeable (see validate_dossier, which enforces them
# exactly when `verdict: READY`). Their COMPLEMENT on an intact dossier is the
# attested reason -- and it is what the gate used to throw away: the rule tells
# the coordinator to "dispatch from the dossier's stated reason" (#17290) while
# exit 3 published an `errors: []` that is empty BY CONSTRUCTION, the dossier
# being intact. Order is the contract's own, so two dossiers blocked for the
# same reason render identically and the dispatch is groupable.
BLOCKING_FIELDS = (
    ("checks", ("latest-wins-green",)),
    ("b0", ("clear",)),
    ("scope", ("pass",)),
    ("domain", ("pass", "not-applicable")),
)
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

# #17039 -- Le predicat de "reserve vivante" n'est pas une liste de tokens :
# il est confie a scripts/check_unaddressed_nits.classify (meme semantique
# que B.0, encagement inclus). Reduire la detection a une seconde liste
# duplique CONCERN_MARKERS + SEVERITY_GLYPHS + BLOCK_VERDICTS tout en
# ignorant l'encagement, ce qui faisait perimer une levee ecrite dans la
# forme sure (le dos de la PR note que la duplication est une dette --
# dette reglee). Pas de second marqueur-statique ici.


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


# #17818 : la PREMIERE POSE d'un commentaire consultatif de bot marker-garde
# apres le dossier. #16931 avait neutralise la reecriture en place, mais une
# pose neuve comptait comme commentaire etranger : l'arrivee d'une PR voisine
# (qui declenche l'organe PR-PATH-COLLISION sur les README partages) perimait
# le dossier sans que le fond de la PR bouge. Mesure 2026-09-25 : dossiers de
# #17781 et #17797 perimes a 13:02Z par la pose consultative du bot seul.
# Ces quatre organes sont consultatifs par construction (« l'organe rend
# visible, il ne bloque pas »). Le login mesure est "github-actions[bot]"
# (suffixe [bot] reserve aux comptes d'app GitHub : un humain ne peut pas le
# porter) et l'AUTEUR compte, pas le texte seul -- un tiers qui recopie le
# marqueur perime toujours le dossier.
BOT_ADVISORY_LOGIN = "github-actions[bot]"


def _is_bot_advisory_pose(row: dict[str, Any]) -> bool:
    """True pour la premiere pose d'un commentaire consultatif de bot marker-garde.

    Neutralise la row dans le decompte des commentaires posterieurs au
    dossier. Predicate conjonctif : auteur ET marqueur en tete de corps -- la
    disparition du commentaire, une edition humaine (marqueur deplace) ou un
    tiers recopiant le marqueur restent detectes.
    """
    if _login(row) != BOT_ADVISORY_LOGIN:
        return False
    body = row.get("body") or ""
    return any(body.startswith(marker) for marker in _BOT_MARKER_GUARDS)


def _review_body_has_reserve_marker(author: str, body: str) -> bool:
    """True quand, en substance, cette review pose une reserve vivante.

    #17039 (et la revue de ai-01 sur #17693) : le predicat n'est pas une
    liste de tokens en dur. Il est delegue a ``check_unaddressed_nits.classify``
    -- la meme semantique que B.0, encagement inclus : une levee qui nomme le
    verdict qu'elle leve, encage (`backticks`, `« »`, bloc de code), reste
    neutre ; la meme phrase avec le token nu perime le dossier. C'est la
    forme prevue par ``pr-review-discipline.md`` ("repondre a une reserve --
    la forme sure", #17071) ; la centralisation ferme la boucle que la
    duplication avait rouverte cote gate (#16840 fondateur).

    Le cas mixte (une review qui leve ET pose une reserve) reste resolu
    cote EMISSION (consigne #16731 : le coordinateur ne melange jamais les
    deux sur la meme surface) : ``classify`` rend la valeur observee, pas
    une moyenne. Un verdict nu emetteur reste un verdict nu ; un narrateur
    encage reste un narrateur.
    """
    if not body:
        return False
    try:
        verdict = check_unaddressed_nits.classify(author, body)
    except Exception:
        return False  # fail-CLOSED sur dependance externe : on neutralise, on ne perime pas
    return verdict is not None


def _is_own_later_act(
    row: dict[str, Any],
    timestamp_key: str,
    neutral_after: str | None,
    *,
    row_kind: str = "comment",
) -> bool:
    """True when the coordinator itself authored this surface after the dossier.

    The dossier attests that the adjoint read every surface existing when it was
    written. A row the coordinator writes afterwards cannot be a surface the
    coordinator is unaware of -- it wrote it. Neutralising exactly those rows is
    what lets the coordinator lift its own reserve and still merge, without
    weakening the gate: a row from any other author still expires the dossier.

    Note (#16883): the coordinator account ``myia-ai-01`` and the shared worker
    sign-in ``jsboige`` both author coordinator-side actions on this gate's
    only consumer (cf. lane-claim protocol and the merged-account mandate).
    A neutralisation scoped to ``COORDINATOR_LOGIN`` alone misses every
    coordinator action posted under the shared sign-in -- the very loop
    measured on #16840. We accept either login as the coordinator's voice.

    #17039 -- ``row_kind`` precise le contrat de neutralisation :
    - "comment" : neutralise inconditionnellement (comportement historique).
    - "review" : neutralise UNIQUEMENT si la review NE pose PAS une reserve
      vivante. La detection est confiee a ``check_unaddressed_nits.classify``
      (voir commentaire de la fonction) -- un verdict Hermes nu, un glyphe
      🟡/🔴, un verdict **BLOCKED**, ou tout verdict qui resistre a
      l'encagement continuera de perimer le dossier. Une levee ecrite dans
      la forme sure (verdict encage) reste neutre.
    """
    if not neutral_after:
        return False
    author = _login(row)
    if author not in (COORDINATOR_LOGIN, SHARED_GITHUB_LOGIN):
        return False
    if row_kind == "review" and _review_body_has_reserve_marker(author, row.get("body") or ""):
        return False
    stamp = row.get(timestamp_key) or ""
    return bool(stamp) and stamp > neutral_after


def _attested_reviews(
    snapshot: dict[str, Any], neutral_after: str | None
) -> list[dict[str, Any]]:
    return [
        row
        for row in snapshot.get("reviews") or []
        if not _is_own_later_act(row, "submittedAt", neutral_after, row_kind="review")
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


def b0_claim_contradictions(claim: str, result: dict[str, Any] | None) -> list[str]:
    """Re-verify a dossier's ``b0: clear`` claim against the live B.0 organ.

    The ``checks:`` claim has been re-verified since #16957; ``b0:`` was
    still taken on faith, and a READY dossier could attest ``b0: clear`` on a
    pull request the organ blocks. Measured on 2026-09-24: two READY dossiers
    (#16955 and #16987) declared ``b0: clear`` while ``check_unaddressed_nits.py``
    exited 1 on an unlifted Hermes reserve. Only the coordinator's separate B.0
    run caught them, and the gate's ``exit 0`` looked like a green light. Like
    the checks claim, the b0 claim is now compared with what the organ measures
    at evaluation time, and every unlifted remark is named.

    ``result`` is the dict returned by ``check_unaddressed_nits.analyse_pr``.
    A claim other than ``clear`` is not refuted here, because a BLOCKED dossier
    may say so.
    """
    if claim != "clear" or not result or not result.get("blocked"):
        return []
    blocking = list(result.get("blocking") or [])
    named = "; ".join(
        f"{row.get('kind', '?')} by {row.get('author', '?')} via {row.get('src', '?')}"
        for row in blocking[:5]
    )
    if len(blocking) > 5:
        named += f" (+{len(blocking) - 5} more)"
    return [
        "b0 claim 'clear' is contradicted by the live B.0 organ "
        f"(check_unaddressed_nits.py): {len(blocking)} unlifted remark(s)"
        + (f" -- {named}" if named else "")
    ]


def probe_b0(pr: int) -> dict[str, Any]:
    """Run the B.0 organ on ``pr``. A failure to measure is fail-closed.

    The import is lazy because the probe runs only for a dossier that claims
    READY: BLOCKED and absent dossiers never load the organ. A failure to
    import it is a failure to measure like any other -- it surfaces as
    ``RuntimeError``, which ``main`` reports as UNKNOWN (exit 2), never as a
    traceback.
    """
    try:
        try:
            import check_unaddressed_nits
        except ImportError:  # charge via importlib dans les tests (hors scripts/)
            sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
            import check_unaddressed_nits
        return check_unaddressed_nits.analyse_pr(pr)
    except Exception as exc:  # noqa: BLE001 -- any failure means "not measured"
        raise RuntimeError(f"B.0 organ could not measure PR #{pr}: {exc}") from exc


def refute_ready_b0(
    pr: int,
    verdict: str,
    dossier: Dossier | None,
    probe: Any = None,
) -> tuple[str, list[str], Dossier | None]:
    """Demote a READY verdict whose ``b0: clear`` claim the organ refutes.

    The demotion is to "no dossier worth trusting" (exit 1), the same outcome
    as a contradicted ``checks:`` claim: a dossier that attests a false
    ``clear`` cannot be trusted on its other fields either. Only READY is
    probed, so the organ adds no API cost to BLOCKED or absent dossiers.
    """
    if verdict != VERDICT_READY or dossier is None:
        return verdict, [], dossier
    refuted = b0_claim_contradictions(
        dossier.fields.get("b0", ""), (probe or probe_b0)(pr)
    )
    if refuted:
        return "", refuted, None
    return verdict, [], dossier


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


def is_out_of_fleet(snapshot: dict[str, Any]) -> bool:
    """True when the pull request is carried by no fleet lane at all.

    Both conditions, mirroring the `tag_required` exemption (#17713/#17715,
    `variation_tag_required.py`): the head branch starts with ``claude/`` AND
    the body declares « Hors flotte ». Either alone is not out of fleet -- a
    fleet lane renaming its branch or copying the marker stays inside the
    third-party rule (#17791 acceptance 3).
    """
    head_ref = snapshot.get("headRefName") or ""
    return head_ref.startswith("claude/") and "Hors flotte" in (
        snapshot.get("body") or ""
    )


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
    elif is_out_of_fleet(snapshot):
        # #17791 -- a maintainer cloud session (`claude/*` + « Hors flotte »)
        # carries no fleet lane: CLAUDE.md ('À qui ce fichier s'adresse') exempts
        # it from the Grain tag, so the third-party rule has no carrier to
        # compare against. Every qualifying lane is third-party by construction,
        # and the self-attestation check below is unreachable for it.
        pass
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
        # A pull request that changes zero files has nothing to squash, whatever
        # its genre, domain or author. This is not a judgement on smallness --
        # `check_trivial_diff.py` owns that, and deliberately lets a two-line
        # critical fix through (#15740). It is the absence of a deliverable.
        # Measured on #16975/#16976 (2026-09-22): both carried an INTACT dossier
        # declaring `diff-files: 0` and `verdict: READY`, so the gate returned 0
        # and authorised a merge that would have closed a grain having delivered
        # nothing (G.3). Only B.0, holding an unrelated morphological reserve,
        # happened to stop it. A dossier asserting READY over an empty diff is
        # self-contradictory, which is exactly what "no dossier worth trusting"
        # means -- hence the existing rc=1 path, not a new one. A BLOCKED dossier
        # over an empty diff stays intact: it attests, correctly, non-mergeability.
        if snapshot.get("changedFiles") == 0:
            errors.append("READY requires a non-empty diff: 0 files changed")
    return errors


def evaluate_with_dossier(
    snapshot: dict[str, Any],
) -> tuple[str, list[str], Dossier | None]:
    """Select the newest candidate and return a fail-closed verdict.

    Returns one of ``VERDICT_READY`` (intact dossier claiming the PR is
    mergeable), ``VERDICT_BLOCKED`` (intact dossier attesting it is not) or
    ``""`` (no dossier worth trusting), plus the dossier that produced the
    verdict -- ``None`` whenever the verdict is ``""``. Separating dossier
    integrity from PR mergeability is the whole point: making the right to READ
    depend on the state of MERGEABILITY meant the coordinator could only ever
    open the pull requests that were already fine -- never the oldest ones,
    which are old precisely because they are blocked.

    The third element is what makes the verdict ACTIONABLE. On
    ``VERDICT_BLOCKED`` the ``errors`` list is empty by construction -- the
    dossier is intact, that is what exit 3 means -- so the reason the gate read
    has to travel separately or not at all (#17290).
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
        return "", ["no [ADJOINT PREFLIGHT] dossier comment found"], None

    dossier, errors = candidates[-1]
    errors = [*errors, *validate_dossier(dossier, snapshot)]
    # A dossier is a snapshot. Any later comment invalidates it, including a
    # reply that claims the PR is still ready -- unless the coordinator itself
    # wrote it, which it cannot be unaware of (see _is_own_later_act), or it
    # is the first pose of a consultative marker-guarded bot comment, which
    # attests nothing about the PR's substance (see _is_bot_advisory_pose).
    foreign = [
        row
        for row in comments[dossier.comment_index + 1:]
        if not _is_own_later_act(row, "createdAt", dossier.created_at)
        and not _is_bot_advisory_pose(row)
    ]
    if foreign:
        errors.append(
            "discussion changed after dossier: a fresh adjoint preflight is required"
        )
    if errors:
        return "", errors, None
    return dossier.fields.get("verdict", ""), [], dossier


def evaluate(snapshot: dict[str, Any]) -> tuple[str, list[str]]:
    """The verdict and the reason, without the dossier (the historical shape).

    Kept as the callers' view so the gate's contract does not move under them;
    ``evaluate_with_dossier`` is the same computation plus what #17290 exposes.
    """
    verdict, errors, _ = evaluate_with_dossier(snapshot)
    return verdict, errors


def blocking_fields(dossier: Dossier) -> list[str]:
    """The attested fields that are NOT at their READY value -- the reason.

    A ``BLOCKED`` dossier may legitimately have none of them: `validate_dossier`
    constrains these four only when the dossier CLAIMS ready, so an honest
    blocked dossier can declare `checks: latest-wins-green` and carry its reason
    in prose. This returns ``[]`` then -- it names the fields that block, and
    never invents one to fill the silence.
    """
    fields = dossier.fields
    return [
        key for key, ready_values in BLOCKING_FIELDS
        if fields.get(key, "") not in ready_values
    ]


def dossier_payload(dossier: Dossier) -> dict[str, Any]:
    """Every field the gate READ, plus where it read it.

    This publishes what `parse_dossier` already parsed: the dossier contract
    itself is unchanged, no field is added to what an emitting lane must write.
    """
    payload: dict[str, Any] = dict(dossier.fields)
    payload["author"] = dossier.author
    payload["created_at"] = dossier.created_at
    payload["comment_index"] = dossier.comment_index
    return payload


def build_result(
    pr: int,
    snapshot: dict[str, Any],
    verdict: str,
    errors: list[str],
    dossier: Dossier | None,
) -> dict[str, Any]:
    """The ``--json`` payload, built without touching the network.

    The `dossier` block rides ONLY with a verdict the gate accepted. A refused
    dossier must keep reading as refused: exposing the attested reason must not
    make a PR whose fingerprint is broken look prevalidated -- the negative
    control of #17290.
    """
    result: dict[str, Any] = {
        "pr": pr,
        "head": snapshot["headRefOid"],
        "ready": verdict == VERDICT_READY,
        "verdict": verdict or "NO_DOSSIER",
        "errors": errors,
        "out_of_fleet": is_out_of_fleet(snapshot),
    }
    if dossier is not None and verdict:
        result["dossier"] = dossier_payload(dossier)
        result["blocking_fields"] = blocking_fields(dossier)
    return result


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


def _pr_metadata(pr: int, *, with_rollup: bool) -> dict[str, Any]:
    # Scalar fields come from REST (`repos/.../pulls/N`) so the shared GraphQL
    # quota only pays for the check rollup below. Keys keep the exact shape
    # `gh pr view --json` produced, so fingerprints and the identity bracket
    # stay byte-compatible with dossiers stamped before this change.
    row = gh_json(["api", f"repos/{REPO}/pulls/{pr}"])
    if not isinstance(row, dict):
        raise RuntimeError("pull request response is not an object")
    state = row.get("state") or ""
    data: dict[str, Any] = {
        "number": row.get("number"),
        "title": row.get("title"),
        "body": row.get("body") or "",
        # REST renders state lowercase and folds MERGED into "closed";
        # `gh pr view` rendered uppercase with a distinct MERGED state, and
        # the fingerprint payload hashes this field verbatim.
        "state": "MERGED" if row.get("merged") else state.upper(),
        "isDraft": row.get("draft"),
        "baseRefName": (row.get("base") or {}).get("ref"),
        "headRefOid": (row.get("head") or {}).get("sha"),
        # Rides for the frozen-campaign check only (merge_ready reads it via
        # the same shared module). NOT in the fingerprint payload, which uses
        # explicit keys -- adding this field must not change surfaces-sha256.
        "headRefName": (row.get("head") or {}).get("ref"),
        "updatedAt": row.get("updated_at"),
        "changedFiles": row.get("changed_files"),
        "additions": row.get("additions"),
        "deletions": row.get("deletions"),
    }
    if with_rollup:
        # The check rollup has no REST equivalent, so it stays on GraphQL
        # as a single-field query instead of the former twelve-field one.
        rollup = gh_json([
            "pr", "view", str(pr), "--repo", REPO,
            "--json", "statusCheckRollup",
        ])
        if not isinstance(rollup, dict):
            raise RuntimeError("pull request response is not an object")
        data["statusCheckRollup"] = rollup.get("statusCheckRollup")
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
    before = _pr_metadata(pr, with_rollup=True)
    snapshot = dict(before)
    snapshot["comments"] = _issue_comments(pr)
    snapshot["reviews"] = _reviews(pr)
    snapshot["threads"] = review_threads(pr)
    # Fetched inside the before/after bracket: a check concluding during the
    # read bumps updatedAt and aborts the snapshot (transient UNKNOWN, the
    # caller retries), so the claim verification below never reads a state
    # that was already stale when captured. The B.0 probe (`probe_b0`) is NOT
    # in this bracket: it runs after, and only on a READY dossier. A remark
    # posted between the snapshot and the probe therefore makes the organ
    # contradict a `b0: clear` claim -- a conservative refusal, which a rerun
    # names as a changed discussion surface.
    snapshot["checkRuns"] = _head_check_runs(snapshot["headRefOid"])
    after = _pr_metadata(pr, with_rollup=True)
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
    # Warn-fort + poursuite (pas d'abort) : l'echec BRUYANT est porte par le
    # helper, gh_identity --whoami et detect_shared_login.py ; fermer l'organe
    # sur une lane sans compte machine (#17418 Phase B/C) arreterait les
    # dossiers pendant la transition.
    try:
        gh_identity.pin_gh_token()
    except gh_identity.GhIdentityError as exc:
        print(f"GH-IDENTITY (WARN, poursuite sous compte actif): {exc}", file=sys.stderr)
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
        verdict, errors, dossier = evaluate_with_dossier(snapshot)
        if not errors:
            verdict, errors, dossier = refute_ready_b0(args.pr, verdict, dossier)
    except (
        RuntimeError,
        KeyError,
        TypeError,
        ValueError,
        OSError,
        UnicodeError,
        json.JSONDecodeError,
    ) as exc:
        errors = [f"UNKNOWN: {exc}"]
        # #17418 Phase A : un rc=2 par rate-limit ne doit plus se lire comme
        # « pas de dossier » (rc=1). La banniere nomme la cause et la
        # remediation — c'est la confusion des deux qui a coute ~3 h de merge.
        if gh_identity.is_rate_limit_error(str(exc)):
            banner = gh_identity.rate_limit_banner(str(exc))
            print(banner, file=sys.stderr)
            errors.append(banner)
        result = {
            "pr": args.pr,
            "ready": False,
            "verdict": "UNKNOWN",
            "errors": errors,
        }
        print(json.dumps(result, ensure_ascii=False) if args.json else f"UNKNOWN -- {exc}")
        return EXIT_UNKNOWN

    # Veto user sur campagne gelee (#17040) : un dossier READY n'autorise pas
    # a merger une PR gelee. Le veto ne vit sur AUCUNE surface que le dossier
    # couvre -- le gate le lit au moment de se prononcer, via le module
    # partage frozen_campaigns (meme lecteur que merge_ready). Applique
    # seulement au verdict READY : un dossier refuse ou BLOCKED est deja non
    # mergeable, le gel n'y ajoute rien.
    frozen_reason = None
    if verdict == VERDICT_READY:
        frozen_reason = frozen_umbrella_exclusion(
            snapshot.get("title"),
            snapshot.get("body"),
            snapshot.get("headRefName"),
        )
    ready = verdict == VERDICT_READY and frozen_reason is None
    result = build_result(args.pr, snapshot, verdict, errors, dossier)
    if frozen_reason is not None:
        # Le dossier reste intact et publie : ce que le gate refuse est le
        # MERGE, pas la lecture de la PR -- meme action documentee que rc=3.
        result["ready"] = False
        result["verdict"] = "FROZEN"
        result["frozen"] = frozen_reason
    if args.json:
        print(json.dumps(result, ensure_ascii=False))
    elif frozen_reason is not None:
        print(
            f"FROZEN -- PR #{args.pr} belongs to a frozen campaign "
            f"({frozen_reason}); do not merge, dispatch to the lane author."
        )
    elif ready:
        print(f"READY -- PR #{args.pr} prevalidated by adjoint at {snapshot['headRefOid']}")
        if is_out_of_fleet(snapshot):
            print(
                "  note: hors-flotte PR (claude/* + 'Hors flotte'): no fleet "
                "lane carries it, any qualifying lane is third-party (#17791)"
            )
    elif verdict == VERDICT_BLOCKED:
        print(
            f"BLOCKED-WITH-SUBSTANCE -- PR #{args.pr} has an intact adjoint dossier at "
            f"{snapshot['headRefOid']} attesting it is NOT mergeable."
        )
        print("  Do not open its surfaces: dispatch from the dossier's stated reason.")
        attested = ", ".join(
            f"{key}={dossier.fields.get(key, '')}" for key, _ in BLOCKING_FIELDS
        )
        blocked = ",".join(blocking_fields(dossier)) or "none named by the contract"
        print(f"  attested reason: {attested} (blocking: {blocked})")
    else:
        print(f"NO-DOSSIER -- PR #{args.pr} is not adjoint-prevalidated")
        for error in errors:
            print(f"  - {error}")
    if frozen_reason is not None:
        return EXIT_BLOCKED_WITH_SUBSTANCE
    if ready:
        return EXIT_READY
    if verdict == VERDICT_BLOCKED:
        return EXIT_BLOCKED_WITH_SUBSTANCE
    return EXIT_NO_DOSSIER


if __name__ == "__main__":
    sys.exit(main())
