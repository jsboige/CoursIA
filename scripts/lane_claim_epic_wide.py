#!/usr/bin/env python3
r"""Epic-wide-claim labeler -- piste 1 of #12156 (advisory organ).

## Why this exists

Issue #12156 measured the mechanism that pushes the fleet toward META: an
``[CLAIMED]`` without a ``paths:`` clause is epic-wide BY DESIGN on a unitary
issue (the correct fail-CLOSED default), but on an UMBRELLA it produces the
opposite of what the umbrella exists for -- one holder, every other lane
excluded, the EPIC advancing no faster. The picker itself says "pioche ou cree
un SOUS-grain dedans, ne claim pas l'EPIC entier", yet nothing signals the
pattern once it has happened. Measured 2026-09-11 with this organ against
``origin/main``: 1 of 41 open EPIC issues locked epic-wide (#15062 -- a
scoped-looking claim whose every glob is dead, lifted per #10958). An earlier
manual count of 3 (#15062, #14366, #12205) had used ``blocking_lanes``, the
wrong predicate: #14366 and #12205 hold scoped or stale claims and do not
lock.

Piste 1 of the issue asks for exactly this organ: an ADVISORY that labels (or
comments on) an issue carrying an epic-wide claim on an umbrella, reminding
the scoped form. It signals, it never blocks.

## What it does

For each OPEN issue classified as an umbrella, detect whether the umbrella is
held by another lane's ACTIVE, effectively-epic-wide claim, and:

  - apply the ``epic-wide-claim`` label + ONE marker-anchored comment (posted
    only when absent, so at most one comment per lock episode);
  - RETRACT the label when the lock clears (hysteresis, revisable);
  - respect a human retraction of the label as a verdict that STICKS (#14307,
    same semantics as ``candidate_delivered.py``): the latest label event by a
    non-bot actor being an ``unlabeled`` suppresses re-posing. A human who
    re-poses the label hands control back to the sweep.

## Why this cannot over-fire the way lane-claim-conflict did (#10395)

The retired ``lane-claim-conflict`` PR label fired on a text heuristic and
landed on protocol-conform PRs. This organ's predicate is not a heuristic: it
reuses the SAME reducer (``check_lane_claim.compute_active_claims``), the SAME
umbrella classifier (``_is_umbrella_issue``), the SAME stale rule, the SAME
dead-glob witness walk (``_git_tracked_files`` + ``_empty_scope_in``) and the
SAME effectively-epic-wide predicate (``paths is None`` / dead globs) that
``check_lane_claim._run_check`` uses to compute ``epic_wide_on_umbrella``. A
parity test replays synthetic payloads through BOTH and asserts agreement --
including the dead-glob lift case (an organ that skipped the tracked walk
under-reported #15062; that exact case is now pinned by a test). No competing
regex for ``[CLAIMED]`` lives in this file.

## Run locally

    python scripts/lane_claim_epic_wide.py --dry-run       # log only
    python scripts/lane_claim_epic_wide.py                 # apply (CI)
    python scripts/lane_claim_epic_wide.py --json          # verdict JSON

Exit code is ALWAYS 0 (advisory) except 2 on caller error: the actionable
payload is the label set, never the green conclusion (same contract as
``candidate_delivered.py``).
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Iterable

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_lane_claim as clc  # noqa: E402

LABEL_DEFAULT = "epic-wide-claim"
LABEL_COLOR = "b60205"  # red -- "umbrella locked, other lanes excluded"
LABEL_DESC = (
    "Umbrella held by an active UNSCOPED [CLAIMED] -- other lanes excluded; "
    "scope the claim with a paths: clause (#12156)"
)

# Sentinel perspective: a lane that never holds a claim, so every active claim
# on the issue is an "other" from the audit's point of view.
AUDIT_LANE = "advisory:epic-wide-audit"

MARKER = "<!-- lane-claim-epic-wide-advisory -->"


# --------------------------------------------------------------------------- #
#  Pure analysis (no network) -- unit-tested                                  #
# --------------------------------------------------------------------------- #


def locking_claims(
    payload: dict,
    stale_threshold: float | None = 48.0,
    now: datetime | None = None,
    tracked: list[str] | None = None,
) -> list[dict]:
    r"""Claims that lock ``payload``'s umbrella epic-wide. [] when they don't.

    Mirrors the ``epic_wide_on_umbrella`` branch of
    ``check_lane_claim._run_check`` (same reducer, same stale rule, same
    effectively-epic-wide predicate) but returns PER-CLAIM detail so the
    comment can name the holder(s).

    ``tracked`` is the repo's tracked-file list (``git ls-files``), used to
    attach the #10958 dead-glob witness exactly where ``_run_check`` attaches
    it: BEFORE the reducer, on every scoped event. Without it a scoped claim
    with an entirely-dead scope (the #15062 shape -- a `paths:` clause whose
    every glob matches zero tracked files) is NOT lifted to epic-wide and the
    organ under-reports. ``tracked is None`` degrades like a failed walk: no
    witness, no lift (the reducer-direct path of the reference organ).
    """
    now = now or datetime.now(timezone.utc)
    if not clc._is_umbrella_issue(payload):
        return []
    events = clc._sort_events(payload)
    # Same gesture as _run_check (~line 2261): attach empty_scope BEFORE the
    # reducer so the effectively-epic-wide predicate can read the witness.
    if tracked is not None:
        for ev in events:
            if ev.get("paths"):
                ev["empty_scope"] = clc._empty_scope_in(ev["paths"], tracked)
    active, _unattributed = clc.compute_active_claims(events)
    others: list = []
    for lane, ev in sorted(active.items()):
        if lane == AUDIT_LANE:
            continue
        age = clc._claim_age_hours(ev.created_at, now)
        if stale_threshold is not None and age is not None and age >= stale_threshold:
            continue  # stale: does not lock (measured on #12156 itself, 260 h)
        others.append((lane, ev, age))
    if not others:
        return []
    effectively_wide = all(
        (ev.get("paths") is None)
        or clc._claim_scope_effectively_epic_wide(ev)
        or bool(getattr(ev, "scope_declared_off_marker", False))
        for _lane, ev, _age in others
    )
    if not effectively_wide:
        return []
    return [
        {
            "lane": lane,
            "claimed_at": ev.created_at,
            "age_hours": round(age, 1) if age is not None else None,
            "url": ev.url,
            "by": ev.author,
        }
        for lane, ev, age in others
    ]


def classify(
    payload: dict,
    stale_threshold: float | None = 48.0,
    now: datetime | None = None,
    tracked: list[str] | None = None,
) -> tuple[str, list[dict]]:
    """``("locked", claims)`` or ``("clear", [])`` for one open umbrella issue."""
    claims = locking_claims(payload, stale_threshold=stale_threshold, now=now,
                            tracked=tracked)
    return ("locked", claims) if claims else ("clear", [])


def comment_body(findings: list[dict], label: str) -> str:
    """The one marker-anchored reminder comment posted per lock episode."""
    lines = [
        MARKER,
        f"[advisory {label}] Cette umbrella est verrouillee **epic-wide** "
        f"(label `{label}`, issue #12156 piste 1 -- signale, ne bloque pas).",
        "",
        "Un `[CLAIMED]` sans clause `paths:` a une portee epic-wide : il exclut "
        "**toutes** les autres lanes de l'issue entiere. Sur une umbrella, le "
        "protocole demande un SOUS-grain, pas un claim integral -- la forme "
        "attendue :",
        "",
        "```",
        "[CLAIMED] lane <machine:workspace> -- paths: <glob1>, <glob2>",
        "```",
        "",
        "Claims actifs tenus epic-wide a l'instant de ce balayage :",
        "",
        "| Lane | Claim depuis | Age (h) |",
        "|---|---|---|",
    ]
    for f in findings:
        lines.append(f"| `{f['lane']}` | {f['claimed_at']} | {f['age_hours']} |")
    lines += [
        "",
        "Le label se retire de lui-meme des que le verrou se leve (claim scoped, "
        "released ou perime). Une retraction humaine du label est un verdict et "
        "tient (#14307).",
    ]
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
#  Human-retraction semantics (#14307) -- mirrors candidate_delivered.py       #
# --------------------------------------------------------------------------- #


def _is_bot(actor: str) -> bool:
    return (actor or "").endswith("[bot]")


def human_retraction(label_events: list[dict] | None) -> dict | None:
    r"""Latest label event by a non-bot actor, iff it is a removal.

    Bot events are ignored: the sweep's own retractions are hysteresis, not
    verdicts. A human's latest action being a POSE hands control back.
    """
    human = [e for e in (label_events or []) if not _is_bot(e.get("actor", ""))]
    if not human:
        return None
    latest = max(human, key=lambda e: e.get("created_at") or "")
    return latest if latest.get("event") == "unlabeled" else None


# --------------------------------------------------------------------------- #
#  gh wiring (injectable for tests)                                           #
# --------------------------------------------------------------------------- #

GhJson = Callable[[list[str]], object]


def _gh_json(args: list[str]) -> object:
    proc = subprocess.run(["gh", *args], capture_output=True, text=True,
                          encoding="utf-8")
    if proc.returncode != 0:
        raise RuntimeError(
            f"gh failed ({proc.returncode}): {proc.stderr.strip() or proc.stdout.strip()}"
        )
    out = (proc.stdout or "").strip()
    return json.loads(out) if out else None


def list_open_epic_issues(repo: str, gh: GhJson = _gh_json) -> list[dict]:
    return gh(["issue", "list", "--repo", repo, "--state", "open",
               "--label", "EPIC", "--limit", "200",
               "--json", "number,title"]) or []


def issue_payload(repo: str, number: int, gh: GhJson = _gh_json) -> dict:
    return gh(["issue", "view", str(number), "--repo", repo,
               "--json", "number,title,labels,comments"]) or {}


def label_events(repo: str, number: int, label: str, gh: GhJson = _gh_json) -> list[dict]:
    r"""``(un)labeled`` events for ``label`` on one issue (issues events API)."""
    events = gh(["api", f"repos/{repo}/issues/{number}/events?per_page=100"]) or []
    return [
        {"event": e.get("event"), "actor": (e.get("actor") or {}).get("login", ""),
         "created_at": e.get("created_at")}
        for e in events
        if e.get("event") in ("labeled", "unlabeled")
        and (e.get("label") or {}).get("name") == label
    ]


def has_marker_comment(payload: dict) -> bool:
    return any(MARKER in (c.get("body") or "") for c in payload.get("comments") or [])


def ensure_label(repo: str, name: str, dry_run: bool, gh: GhJson = _gh_json) -> None:
    if dry_run:
        return
    gh(["label", "create", name, "--repo", repo,
        "--color", LABEL_COLOR, "--description", LABEL_DESC, "--force"])


def apply_label(repo: str, number: int, name: str, dry_run: bool, gh: GhJson = _gh_json) -> None:
    if dry_run:
        return
    gh(["issue", "edit", str(number), "--repo", repo, "--add-label", name])


def remove_label(repo: str, number: int, name: str, dry_run: bool, gh: GhJson = _gh_json) -> None:
    if dry_run:
        return
    gh(["issue", "edit", str(number), "--repo", repo, "--remove-label", name])


def post_comment(repo: str, number: int, body: str, dry_run: bool, gh: GhJson = _gh_json) -> None:
    if dry_run:
        return
    gh(["issue", "comment", str(number), "--repo", repo, "--body", body])


def has_label(payload: dict, name: str) -> bool:
    return any(
        (lab.get("name") if isinstance(lab, dict) else lab) == name
        for lab in payload.get("labels") or []
    )


# --------------------------------------------------------------------------- #
#  Driver                                                                     #
# --------------------------------------------------------------------------- #


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default=None)
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--json", action="store_true", help="verdict JSON one line per issue")
    ap.add_argument("--label", default=LABEL_DEFAULT)
    ap.add_argument("--sleep", type=float, default=1.0)
    ap.add_argument("--stale-threshold", type=float, default=48.0,
                    help="hours after which a claim no longer locks (default 48)")
    ap.add_argument("--limit", type=int, default=0, help="cap issues scanned (0 = all)")
    args = ap.parse_args(argv)

    repo = args.repo
    if not repo:
        try:
            repo = _gh_json(["repo", "view", "--json", "nameWithOwner"])["nameWithOwner"]
        except Exception as exc:
            print(f"ERROR: cannot resolve repo: {exc}", file=sys.stderr)
            return 2

    try:
        issues = list_open_epic_issues(repo)
    except Exception as exc:
        print(f"ERROR: listing EPIC issues failed: {exc}", file=sys.stderr)
        return 2
    if args.limit:
        issues = issues[: args.limit]

    # One git walk for the whole sweep (the #10958 dead-glob witness). None on
    # failure -> no witness, no lift: same degrade as the reference organ.
    tracked = clc._git_tracked_files()
    if tracked is None:
        print("WARN: git ls-files walk failed -- dead-glob lift disabled "
              "(scoped claims with an entirely-dead scope will NOT be "
              "reported this run)", file=sys.stderr)

    summary = []
    for it in issues:
        number = it.get("number")
        try:
            payload = issue_payload(repo, number)
            events = label_events(repo, number, args.label)
        except Exception as exc:  # gh hiccup -- skip, do not crash the sweep
            print(f"WARN: #{number} skipped ({exc})", file=sys.stderr)
            continue
        verdict, findings = classify(payload, stale_threshold=args.stale_threshold,
                                     tracked=tracked)
        labeled = has_label(payload, args.label)
        entry = {"issue": number, "title": it.get("title"), "verdict": verdict,
                 "claims": findings, "was_labeled": labeled}
        if verdict == "locked":
            if human_retraction(events):
                entry["action"] = "skip-human-retraction"
            else:
                ensure_label(repo, args.label, args.dry_run)
                if not labeled:
                    apply_label(repo, number, args.label, args.dry_run)
                    entry["action"] = "label-applied"
                else:
                    entry["action"] = "label-kept"
                if not has_marker_comment(payload):
                    post_comment(repo, number, comment_body(findings, args.label),
                                 args.dry_run)
                    entry["comment"] = "posted"
        elif labeled:
            remove_label(repo, number, args.label, args.dry_run)
            entry["action"] = "label-retracted"
        else:
            entry["action"] = "noop"
        summary.append(entry)
        if args.json:
            print(json.dumps(entry, ensure_ascii=False))
        else:
            claims = ", ".join(f"{f['lane']}({f['age_hours']}h)" for f in findings)
            print(f"#{number} {verdict.upper():6s} {entry['action']:22s} {claims}")
        time.sleep(args.sleep)

    locked = [e for e in summary if e["verdict"] == "locked"]
    print(f"EPIC scanned={len(summary)} locked={len(locked)} "
          f"(advisory -- exit 0 whatever the count)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
