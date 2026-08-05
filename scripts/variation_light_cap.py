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

# SHARED extractor: see scripts/variation_tags.py. The cap organe and the
# guard workflow MUST speak the same dialect of "what counts as a Grain: tag"
# -- a guard and an organe that disagree silently is the worst failure mode
# (issue #9485: 13/34 merges on the 2026-08-05 lot carried no readable tag
# because the cap organe and the guard each had their own, narrower parser).
# We delegate to the shared module and keep only the SHAPE this organe needs
# ({tier, lane}), dropping the GENRE that the cap does not consume.

from variation_tags import extract_tag as _extract_tag


def parse_grain(body: str) -> dict | None:
    """Extract {tier, lane} from a PR body, full-text + separator-agnostic.

    Thin wrapper over the shared extractor `scripts/variation_tags.py`. The
    cap organe consumes only TIER and LANE; the GENRE is computed by the
    extractor and dropped here. Returns None when no Grain: tag is found
    in any of the four recognized forms (inline / no-colon / header-form /
    blockquote-or-list-form), and {tier, lane} otherwise. `lane` may be None
    when the declared tag omits it (DEEP/MED known limitation: past month of
    pull runs, every PR declared a lane -- a missing lane is a §3 defect,
    not a parse failure).
    """
    tag = _extract_tag(body)
    if tag is None:
        return None
    return {"tier": tag.get("tier"), "lane": tag.get("lane")}


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

# G-VAR-2 is a RATIO, not an absolute cap (2026-07-31, user sign-off).
#
# The old `1 LIGHT/lane/day` scored a 1-PR lane and a 19-merge/13-DEEP lane
# identically -- the second is the OPPOSITE of monoculture and was sanctioned
# the same. A cap blind to throughput does not measure monoculture, it caps
# throughput. Worse, it MANUFACTURES the duplicate work it claims to save:
# #8961 (the strip->update ordering doc) sat held for a day; during that hold
# the doc never reached `main`, and two other sessions rewrote it (#8983,
# #8996, closed as duplicates) -- ~98 lines written three times.
#
# Budget = max(1, lane_grains_merged_today // 3). A lane merging 1-3 grains
# keeps EXACTLY the old ceiling of one LIGHT (the small-lane case was never
# the problem); a lane merging 19 gets six. The floor is what makes this a
# strict relaxation: no lane is worse off than under the absolute cap.
LIGHT_RATIO_DIVISOR = 3


def light_budget(lane_grain_count: int) -> int:
    """LIGHT allowance for a lane that merged `lane_grain_count` grains today.

    `max(1, n // 3)`: floor of 1 so a low-output lane keeps the old ceiling,
    then one extra LIGHT per full slice of 3 grains.
    """
    return max(1, lane_grain_count // LIGHT_RATIO_DIVISOR)


def _lane_of(pr: dict) -> str | None:
    """Declared lane of a PR, or None when untagged.

    The lane is STRUCTURAL (the worker's workspace) and is never re-qualified:
    it always comes from the body, even when a `grain-requalified:` label
    overrides the tier. An untagged PR has no lane, so it cannot be attributed
    -- it counts neither as a LIGHT nor in any lane's denominator.
    """
    g = parse_grain(pr.get("body", "") or "")
    return g["lane"] if g else None


def unattributed(merged_prs: list[dict]) -> list[dict]:
    """PRs the organ could NOT attribute to any lane (no readable `Grain:` tag).

    These are invisible to every count above: absent from each lane's
    numerator AND denominator. That is the right arithmetic -- guessing a lane
    would be worse -- but it must never be reported as a clean day. An audit
    that says `cap-reached: 0` over a set where most PRs landed here has
    measured nothing; the summary prints this count so the two cannot be
    confused (#9465).
    """
    return [pr for pr in merged_prs if _lane_of(pr) is None]


def lane_grains(merged_prs: list[dict], target_lane: str) -> list[dict]:
    """Every merged PR attributed to `target_lane`, ANY tier.

    This is the ratio's denominator: DEEP and MED grains are what EARN the
    LIGHT budget, so they must be counted, not just the LIGHTs.
    """
    return [pr for pr in merged_prs if _lane_of(pr) == target_lane]


def lane_lights(merged_prs: list[dict], target_lane: str) -> list[dict]:
    """Merged PRs of `target_lane` whose EFFECTIVE tier is LIGHT (#8970).

    A declared LIGHT re-qualified up to MED does NOT spend the budget; a
    declared DEEP re-qualified down to LIGHT DOES.
    """
    out = []
    for pr in merged_prs:
        if _lane_of(pr) != target_lane:
            continue
        if effective_tier(pr.get("body", ""), label_names(pr)) != "LIGHT":
            continue
        out.append(pr)
    return out


def light_cap_status(merged_prs: list[dict], target_lane: str) -> dict:
    """Given the day's ALREADY-MERGED PRs, would a NEW LIGHT of `target_lane`
    exceed its budget?

    CI semantics: the current PR is OPEN (not yet merged), so it is NOT in
    `merged_prs`. It is nonetheless counted in the denominator (`+ 1`): the
    candidate is itself a grain of the day. Counting it is deliberately
    conservative early in the day -- it stops a lane front-loading LIGHTs at
    02:00 against a throughput it has not produced yet.

    Returns {cap_reached, budget, spent, lane_grains, consumed_by} where
    consumed_by is the earliest merged LIGHT of the lane (kept for the
    workflow's message), or None.
    """
    grains = lane_grains(merged_prs, target_lane)
    lights = lane_lights(merged_prs, target_lane)
    budget = light_budget(len(grains) + 1)  # +1 = the open candidate
    lights.sort(key=lambda p: p.get("mergedAt", ""))
    reached = len(lights) >= budget
    first = lights[0] if lights else None
    return {
        "cap_reached": reached,
        "budget": budget,
        "spent": len(lights),
        "lane_grains": len(grains) + 1,
        "consumed_by": (
            {"number": first.get("number"), "mergedAt": first.get("mergedAt")}
            if reached and first else None
        ),
    }


def replay(merged_prs: list[dict]) -> list[dict]:
    """For every LIGHT PR in the set, decide cap_reached against the FULL set.

    The day is over here (audit path), so each lane's denominator is KNOWN:
    its budget is `max(1, lane_grains // 3)` over the whole set. The k-th LIGHT
    of a lane (chronological, 1-based) is cap-reached iff `k > budget`. Under a
    budget of 1 this reduces exactly to the old rule -- the first LIGHT of each
    lane is never flagged.

    Returns the list sorted by mergedAt (chronological replay).
    """
    # denominator per lane: ALL attributed grains, any tier (they earn budget)
    grains_by_lane: dict[str, int] = {}
    for pr in merged_prs:
        lane = _lane_of(pr)
        if lane:
            grains_by_lane[lane] = grains_by_lane.get(lane, 0) + 1

    lights = []
    for pr in merged_prs:
        lane = _lane_of(pr)
        if not lane:
            continue
        if effective_tier(pr.get("body", ""), label_names(pr)) != "LIGHT":
            continue
        lights.append({**pr, "_tier": "LIGHT", "_lane": lane})
    lights.sort(key=lambda p: p.get("mergedAt", ""))

    # one pass: per lane, the k-th LIGHT spends the k-th unit of budget
    spent: dict[str, list[int]] = {}
    out = []
    for pr in lights:
        lane = pr["_lane"]
        budget = light_budget(grains_by_lane.get(lane, 0))
        prior = spent.setdefault(lane, [])
        cap = len(prior) >= budget
        out.append({
            "number": pr.get("number"),
            "lane": lane,
            "mergedAt": pr.get("mergedAt"),
            "cap_reached": cap,
            "budget": budget,
            "lane_grains": grains_by_lane.get(lane, 0),
            # the LIGHT that spent the last budget unit, for the message
            "consumed_by": prior[-1] if cap and prior else None,
        })
        if not cap:
            prior.append(pr.get("number"))
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
        g = parse_grain(body)
        # UNASSESSABLE vs ASSESSED (#9465). `cap_reached: false` must mean one
        # thing only: "assessed, and within budget". A body with no readable
        # tag, or a tag without a lane, is not an exemption -- it is a
        # measurement the organ could not take, and reporting it as `false`
        # made the gate green precisely where it was blind. `null` is the
        # third state; the caller (variation-tag-guard.yml) compares against
        # "True", so this stays advisory and no CI behaviour changes.
        if eff is None or not g:
            print(json.dumps({
                "cap_reached": None,
                "reason": "unassessable -- no Grain: tag in body",
            }))
            return 0
        if eff != "LIGHT":
            # A KNOWN non-LIGHT tier is a genuine assessment, lane or not: a
            # MED/DEEP grain never spends the LIGHT budget. Only the lane's
            # denominator suffers, and that is `unattributed`'s business.
            print(json.dumps({"cap_reached": False, "reason": f"not LIGHT (effective {eff})"}))
            return 0
        if not g["lane"]:
            # An effective LIGHT with no lane is the one case where the tier is
            # known and the answer still cannot be computed: the budget is
            # per-lane, so without a lane there is no denominator to compare to.
            print(json.dumps({
                "cap_reached": None,
                "reason": "unassessable -- effective LIGHT but no lane in tag",
            }))
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
    blind = unattributed(merged)
    print(f"LIGHT PRs replayed: {len(rows)} | cap-reached: {len(flagged)}"
          f" | unattributed: {len(blind)}/{len(merged)}")
    if blind:
        # Without this line a day whose PRs are all untagged prints exactly
        # like a clean day (#9465): `replayed: 0 | cap-reached: 0`.
        print(f"  WARNING: {len(blind)} of {len(merged)} merged PRs carry no "
              f"readable `Grain:` tag -- they are counted in NO lane, so the "
              f"figures above measure only the tagged remainder.")
        print("  unattributed: "
              + ", ".join(f"#{pr.get('number')}" for pr in blind))
    print(f"{'PR':>7}  {'lane':<28} {'mergedAt':<21} cap")
    for r in rows:
        mark = "CAP-REACHED" if r["cap_reached"] else "ok"
        print(f"  #{r['number']:<5} {r['lane']:<28} {r['mergedAt']:<21} {mark}"
              + (f"  (consumed by #{r['consumed_by']})" if r["cap_reached"] else ""))
    print(json.dumps({
        "rows": rows,
        "unattributed": [pr.get("number") for pr in blind],
    }, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    sys.exit(main())
