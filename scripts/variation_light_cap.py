#!/usr/bin/env python3
"""Detect G-VAR-2 cap-reached: a 2nd+ LIGHT PR merged the same day for a lane.

G-VAR-2 (variation-protocol.md) caps the protocol at **one LIGHT PR per lane
per day, all LIGHT sub-categories confounded** (guard, doc, refs, ... share a
single budget). It is the only gate of the protocol that is **cross-PR** -- it
needs to know what the lane has ALREADY merged today -- so until now it was
counted by hand by the coordinator, who merged a 2nd LIGHT twice in one cycle
(issue #8964: measured firsthand on the 2026-07-30 wave). This tool makes the
fact VISIBLE (advisory, exit 0), it does not block.

Input: a JSON array of the day's merged PRs, each `{number, body, mergedAt}`,
produced by:

    gh pr list --state merged --search 'merged:<YYYY-MM-DD>' \
        --json number,body,mergedAt

Modes
-----
  --replay <file>      Acceptance-test mode (#8964): for every LIGHT PR in the
                       dataset, report whether it is cap-reached (a LIGHT of the
                       same lane merged EARLIER today). Prints a table + a JSON
                       summary on stdout. The replay over the 2026-07-30 wave
                       must flag #8951 (2nd LIGHT of myia-po-2023:CoursIA) and
                       NOT flag #8909 / #8910 / #8913 (each the 1st LIGHT of its
                       lane).

  --check-pr <N>       CI mode (the current PR): report whether PR <N> would be
                       cap-reached given the already-merged PRs in <file>.
                       Emits machine-readable fields for the workflow to label
                       and comment: `cap_reached`, `lane`, `consumed_by` (the
                       earlier LIGHT that spent the budget, with its merge time).

Parsing
-------
Bodies are read as FULL TEXT, never line-by-line. The line-by-line bug measured
hand counted "18/38 untagged" when the true figure was "2/38": the tag is often
on the 2nd+ line of a multi-line body, and a per-line scan misses it (#8964).

Agnostic to separator and case (#8938): the three shapes observed in the wild
all parse identically after markdown noise is stripped --

    Grain: LIGHT/guard -- lane myia-po-2023:CoursIA      (em-dash)
    **Grain:** LIGHT/guard - lane myia-ai-01:CoursIA     (bold, hyphen)
    `Grain: LIGHT/refs` . **Lane:** myia-po-2024:CoursIA-2  (backticks, middot)

Exit 0 always (advisory).
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# --- parsing ---------------------------------------------------------------

# Markdown noise to strip before matching: asterisks (bold) and backticks.
# Mirrors the workflow's `tr -d '*\`'` so the two stay in lockstep.
_NOISE = str.maketrans({"*": "", "`": ""})

# `Grain:` (case-insensitive) then TIER / GENRE. TIER is the word before `/`.
_GRAIN_TIER_RE = re.compile(r"Grain:\s*([A-Za-z]+)\s*/", re.IGNORECASE)

# `lane` (case-insensitive), optional colon, whitespace, then machine:workspace.
# machine = myia-po-2024 (letters, digits, dot, underscore, hyphen); workspace
# likewise (CoursIA-2). Captured as the single token "<machine>:<workspace>".
_LANE_RE = re.compile(
    r"lane:?\s+([A-Za-z0-9._-]+:[A-Za-z0-9._-]+)", re.IGNORECASE
)


def parse_grain(body: str) -> dict | None:
    """Extract {tier, lane} from a PR body, full-text + separator-agnostic.

    Returns None when no `Grain:` line is found. `tier` is upper-cased
    (LIGHT/MED/DEEP) or None if the TIER could not be read. `lane` is the
    "<machine>:<workspace>" string or None.
    """
    if not body:
        return None
    flat = body.translate(_NOISE)
    tier_m = _GRAIN_TIER_RE.search(flat)
    if not tier_m:
        return None
    lane_m = _LANE_RE.search(flat)
    return {
        "tier": tier_m.group(1).upper(),
        "lane": lane_m.group(1) if lane_m else None,
    }


# --- requalification (coordinator override of the declared tag) ------------

# variation-protocol says the DECLARED `Grain:` tag is not self-executing: the
# coordinator re-qualifies it at merge (up: a declared LIGHT read as MED on the
# strength of the diff; down: a declared DEEP read as LIGHT). Until #8970 that
# decision lived only in a dashboard post -- invisible to this job, which then
# flagged legitimately re-qualified work (1 FP / 2 flags on the 2026-07-30
# wave: #8930, re-qualified LIGHT->MED, was still flagged CAP-REACHED).
#
# The channel is a GitHub LABEL applied at merge -- `grain-requalified:<TIER>`
# -- machine-readable, leaves the worker's body intact, cheap to query
# (`gh pr list --json ...,labels` adds the field to the SAME call, no extra
# quota). A present label OVERRIDES the declared tier for counting, in BOTH
# directions: up-qualification spares the LIGHT budget, down-qualification
# consumes it (the symmetric case #8970 asks for). The LANE is structural
# (the worker's workspace) and is never re-qualified -- it still comes from
# the declared body.
_REQUAL_LABEL_RE = re.compile(
    r"grain-requalified:\s*(LIGHT|MED|DEEP)", re.IGNORECASE
)


def label_names(pr: dict) -> list[str]:
    """Flatten a PR's `labels` field to a list of names.

    Robust to the two shapes `gh ... --json labels` can return: a list of
    strings (names) or a list of objects `{name, color, ...}` (the default).
    """
    out: list[str] = []
    for lab in pr.get("labels") or []:
        if isinstance(lab, str):
            out.append(lab)
        elif isinstance(lab, dict):
            name = lab.get("name")
            if name:
                out.append(name)
    return out


def effective_tier(body: str | None, labels: list[str]) -> str | None:
    """The TIER that counts for G-VAR-2.

    A `grain-requalified:<TIER>` label (if present) OVERRIDES the declared
    `Grain:` tag, in both directions -- up (LIGHT->MED spares the budget) and
    down (DEEP->LIGHT consumes it). Returns the declared tier when no
    requalification label is present, or None when neither is readable.
    """
    for lab in labels:
        m = _REQUAL_LABEL_RE.search(lab)
        if m:
            return m.group(1).upper()
    g = parse_grain(body or "")
    return g["tier"] if g else None


# --- cap logic -------------------------------------------------------------

def light_cap_status(merged_prs: list[dict], target_lane: str) -> dict:
    """Given the day's ALREADY-MERGED PRs, is a NEW LIGHT of `target_lane`
    cap-reached?

    CI semantics: the current PR is OPEN (not yet merged), so it is NOT in
    `merged_prs`. If the lane already has >= 1 LIGHT merged today, the current
    PR would be the 2nd -> cap-reached. Returns {cap_reached, consumed_by}
    where consumed_by is the earliest merged LIGHT of that lane (the one that
    spent the budget), or None.

    A PR counts as a LIGHT for the budget iff its EFFECTIVE tier (#8970
    requalification) is LIGHT: a declared LIGHT re-qualified up to MED does
    NOT spend it, a declared DEEP re-qualified down to LIGHT DOES.
    """
    earlier_lights = []
    for pr in merged_prs:
        labels = label_names(pr)
        if effective_tier(pr.get("body", ""), labels) != "LIGHT":
            continue
        # lane is structural -- never re-qualified; it still comes from the body.
        g = parse_grain(pr.get("body", ""))
        if not g or g["lane"] != target_lane:
            continue
        earlier_lights.append(pr)
    if not earlier_lights:
        return {"cap_reached": False, "consumed_by": None}
    # earliest merged LIGHT of the lane = the one that consumed the budget
    earlier_lights.sort(key=lambda p: p.get("mergedAt", ""))
    first = earlier_lights[0]
    return {
        "cap_reached": True,
        "consumed_by": {
            "number": first.get("number"),
            "mergedAt": first.get("mergedAt"),
        },
    }


def replay(merged_prs: list[dict]) -> list[dict]:
    """For every LIGHT PR in the set, decide cap_reached against the FULL set.

    A LIGHT is cap-reached iff a LIGHT of its OWN lane merged strictly EARLIER
    (earlier mergedAt). The first LIGHT of each lane is never cap-reached.
    Returns the list sorted by mergedAt (chronological replay).
    """
    lights = []
    for pr in merged_prs:
        labels = label_names(pr)
        if effective_tier(pr.get("body", ""), labels) != "LIGHT":
            continue
        g = parse_grain(pr.get("body", ""))
        if not g or not g["lane"]:
            continue
        lights.append({**pr, "_tier": "LIGHT", "_lane": g["lane"]})
    lights.sort(key=lambda p: p.get("mergedAt", ""))
    # one pass: per lane, the first seen (chronologically) is the budget owner
    seen_lane: dict[str, int] = {}
    out = []
    for pr in lights:
        lane = pr["_lane"]
        owner = seen_lane.get(lane)
        cap = owner is not None
        out.append({
            "number": pr.get("number"),
            "lane": lane,
            "mergedAt": pr.get("mergedAt"),
            "cap_reached": cap,
            "consumed_by": owner,
        })
        if owner is None:
            seen_lane[lane] = pr.get("number")
    return out


# --- CLI -------------------------------------------------------------------

def _load(path: str) -> list[dict]:
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(data, list):
        sys.exit(f"--replay/--check-pr expects a JSON array, got {type(data).__name__}")
    return data


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--replay", metavar="FILE",
                   help="JSON array of the day's merged PRs (the counting set)")
    g = p.add_mutually_exclusive_group(required=True)
    g.add_argument("--replay-mode", action="store_true",
                   help="acceptance-test mode: report cap_reached for every "
                        "LIGHT in the --replay set")
    g.add_argument("--check-pr", metavar="N", type=int,
                   help="CI mode: assess PR <N> (the current open PR) against "
                        "the --replay merged set")
    p.add_argument("--body", metavar="TEXT",
                   help="--check-pr only: body of the current PR (the open PR "
                        "is not in the merged set, so its tag is read here)")
    p.add_argument("--body-file", metavar="FILE",
                   help="--check-pr only: path to a file holding the current "
                        "PR body (alternative to --body)")
    p.add_argument("--labels-file", metavar="FILE",
                   help="--check-pr only: JSON array of the current PR's labels "
                        "(so a requalification label on the open PR is honored; "
                        "symmetric to the requalification read on merged PRs)")
    args = p.parse_args(argv)

    if not args.replay:
        p.error("--replay FILE (the merged-PR set) is required")

    merged = _load(args.replay)

    if args.check_pr is not None:
        # CI mode: the current PR is OPEN, so its body is NOT in the merged set.
        body = None
        if args.body is not None:
            body = args.body
        elif args.body_file:
            body = Path(args.body_file).read_text(encoding="utf-8")
        if body is None:
            p.error("--check-pr requires --body or --body-file")
        cur_labels: list[str] = []
        if args.labels_file:
            # Tolerate a missing/empty file (treat as no labels) rather than
            # crash: the CI workflow always writes valid JSON (`gh pr view` or
            # a `printf '[]'` fallback), but a manual invocation should not
            # hard-fail on an absent file.
            lpath = Path(args.labels_file)
            raw = []
            if lpath.exists() and lpath.read_text(encoding="utf-8").strip():
                try:
                    raw = json.loads(lpath.read_text(encoding="utf-8"))
                except json.JSONDecodeError:
                    raw = []
            # accept [str] or [{name}] (label_names handles objects via a dict)
            cur_labels = label_names({"labels": raw})
        # Effective tier (#8970): a requalification label overrides the declared
        # one. Only an EFFECTIVE LIGHT is assessed against the cap.
        eff = effective_tier(body, cur_labels)
        if eff != "LIGHT":
            print(json.dumps({"cap_reached": False, "reason": f"not LIGHT (effective {eff})"}))
            return 0
        g = parse_grain(body)
        if not g or not g["lane"]:
            print(json.dumps({"cap_reached": False, "reason": "no lane in tag"}))
            return 0
        status = light_cap_status(merged, g["lane"])
        print(json.dumps({
            "pr": args.check_pr,
            "lane": g["lane"],
            **status,
        }))
        return 0

    # replay mode: the acceptance test
    rows = replay(merged)
    flagged = [r for r in rows if r["cap_reached"]]
    print(f"LIGHT PRs replayed: {len(rows)} | cap-reached: {len(flagged)}")
    print(f"{'PR':>7}  {'lane':<28} {'mergedAt':<21} cap")
    for r in rows:
        mark = "CAP-REACHED" if r["cap_reached"] else "ok"
        print(f"  #{r['number']:<5} {r['lane']:<28} {r['mergedAt']:<21} {mark}"
              + (f"  (consumed by #{r['consumed_by']})" if r["cap_reached"] else ""))
    print(json.dumps({"rows": rows}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
