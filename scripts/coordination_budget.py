#!/usr/bin/env python3
"""Aggregate `Grain:` tags of merged PRs into a per-lane budget table (#9859).

THE cross-lane view the coordinator counted by hand: for each lane that merged
at least one grain over the window, how many DEEP / MED / LIGHT landed, what is
the LIGHT budget (the G-VAR-2 ratio `max(1, grains//3)`), how much is consumed,
and which genres are adjacent -- the signals of monoculture (R6) and of idle
provisioning (a lane with 4 LIGHT and 0 DEEP says "coordinator did not stock
substance", variation-protocol S4).

Reuse, not duplicate (the issue's explicit mandate):
  - `grain_tag.parse_grain_tag`      -- the single tolerant Grain-tag reader (#9485)
  - `variation_light_cap.effective_tier` -- tier AFTER `grain-requalified:` override (#8970)
  - `variation_light_cap.label_names`    -- robust labels flatten (str | dict)
  - `variation_light_cap.light_budget`   -- the G-VAR-2 ratio `max(1, n//3)`

Input
-----
  --days N            Live mode (default 7): shell out to
                      `gh pr list --state merged --search 'merged:>=YYYY-MM-DD>'
                      --json number,title,body,mergedAt,labels`. Requires `gh`
                      auth on the repo.
  --replay <file>     Acceptance-test mode: read a JSON array of PRs from a
                      file. Same shape as the `gh` output. Used by the test
                      suite (synthetic bodies) and reusable for offline audits.

Output
------
A table (markdown) of lanes x tiers + budget + consumed + genre adjacency,
then an anomalies block: PRs with no tag, PRs with a tag but no lane, and
same-genre LIGHT adjacency within a lane (the G-VAR-3 monoculture smell). Exit
0 always (advisory, like variation_light_cap).
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

# Shared readers -- never re-implement the tag or the requalification, or the
# two views drift (the exact bug grain_tag.py was extracted to fix, #9485).
from grain_tag import parse_grain_tag  # noqa: E402
from variation_light_cap import (  # noqa: E402
    effective_tier,
    label_names,
    light_budget,
)

# Lane attribution uses the same reader the cap organ uses. A PR with a Grain
# tag but `lane: None` is a real defect (variation-tag-lane-missing); counted
# in anomalies, never silently assigned.
DEFAULT_DAYS = 7


def _lane_of(pr: dict) -> str | None:
    """Declared lane of a PR, or None. Same reader as variation_light_cap."""
    g = parse_grain_tag(pr.get("body", "") or "")
    return g["lane"] if g else None


def _genre_of(pr: dict) -> str | None:
    """Declared genre of a PR, or None (independent of tier requalification)."""
    g = parse_grain_tag(pr.get("body", "") or "")
    return g["genre"] if g else None


# --- input -----------------------------------------------------------------


def load_prs_replay(path: str) -> list[dict]:
    """Read merged PRs from a JSON file (acceptance-test / offline mode)."""
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(data, list):
        raise ValueError(f"{path}: expected a JSON array of PR objects")
    return data


def load_prs_days(days: int, repo: str | None = None) -> list[dict]:
    """Query merged PRs of the last `days` days via `gh`.

    The `merged:>=YYYY-MM-DD` search qualifier keeps the payload to the window
    (no client-side filtering of a long history). `labels` is requested so
    `effective_tier` can see a `grain-requalified:` override.
    """
    since = (datetime.now(timezone.utc) - timedelta(days=days)).strftime(
        "%Y-%m-%d"
    )
    cmd = [
        "gh",
        "pr",
        "list",
        "--state",
        "merged",
        f"--search=merged:>={since}",
        "--limit",
        "300",
        "--json",
        "number,title,body,mergedAt,labels",
    ]
    if repo:
        cmd[1:1] = ["-R", repo]
    try:
        out = subprocess.check_output(cmd, text=True, encoding="utf-8")
    except FileNotFoundError:
        print(
            "::error::`gh` CLI not found on PATH; use --replay for offline mode.",
            file=sys.stderr,
        )
        return []
    except subprocess.CalledProcessError as exc:
        print(f"::error::gh query failed (exit {exc.returncode}).", file=sys.stderr)
        return []
    return json.loads(out) if out.strip() else []


# --- aggregation -----------------------------------------------------------


def aggregate(prs: list[dict]) -> dict[str, dict]:
    """Build the per-lane row from the merged PRs.

    Each row carries the counts by EFFECTIVE tier (a re-qualified LIGHT->MED
    moves out of LIGHT, #8970), the total grains (the ratio denominator), the
    LIGHT budget + consumed, the set of genres seen, and the lane's LIGHTs
    kept in merge order for adjacency detection.
    """
    rows: dict[str, dict] = {}
    for pr in prs:
        lane = _lane_of(pr)
        if lane is None:
            continue  # untagged or lane-missing -> anomalies, not a row
        row = rows.setdefault(
            lane,
            {
                "DEEP": 0,
                "MED": 0,
                "LIGHT": 0,
                "total": 0,
                "genres": set(),
                "lights": [],  # (mergedAt, genre) in merge order
            },
        )
        tier = effective_tier(pr.get("body", ""), label_names(pr))
        genre = _genre_of(pr)
        if tier in ("DEEP", "MED", "LIGHT"):
            row[tier] += 1
        row["total"] += 1
        if genre:
            row["genres"].add(genre)
        if tier == "LIGHT":
            row["lights"].append((pr.get("mergedAt") or "", genre))
    # derive budget + consumed once the counts are final
    for row in rows.values():
        row["budget"] = light_budget(row["total"])
        row["consumed"] = row["LIGHT"]
        row["over"] = row["LIGHT"] - row["budget"]
    return rows


# --- anomalies -------------------------------------------------------------


def detect_anomalies(
    prs: list[dict], known_lanes: list[str] | None = None
) -> list[str]:
    """Signals that must be reported even when the table looks clean.

    - no tag at all (variation-tag-missing): a merged PR the protocol is blind to.
    - tag present, lane missing (variation-tag-lane-missing): unattributable.
    - same-genre LIGHT adjacency within a lane (G-VAR-3 monoculture smell).
    - idle lane: a `--known-lanes` entry with zero grains on the window. Only
      checked when a canonical lane list is supplied -- without it, the script
      cannot know which lanes SHOULD have produced.
    """
    anom: list[str] = []
    no_tag: list[int] = []
    no_lane: list[int] = []
    for pr in prs:
        g = parse_grain_tag(pr.get("body", "") or "")
        num = pr.get("number", "?")
        if g is None:
            no_tag.append(num)
        elif g["lane"] is None:
            no_lane.append(num)
    if no_tag:
        anom.append(
            f"no Grain tag on {len(no_tag)} merged PR(s): #{', #'.join(map(str, no_tag))} "
            "(variation-tag-missing; invisible to every count)"
        )
    if no_lane:
        anom.append(
            f"Grain tag but no lane on {len(no_lane)} PR(s): #{', #'.join(map(str, no_lane))} "
            "(variation-tag-lane-missing; unattributable)"
        )
    # same-genre LIGHT adjacency (G-VAR-3): two consecutive LIGHTs of the SAME
    # genre in a lane, in merge order. A single repeat is a smell, not a block.
    rows = aggregate(prs)
    for lane, row in sorted(rows.items()):
        lights = sorted(row["lights"], key=lambda x: x[0])
        for (t1, g1), (t2, g2) in zip(lights, lights[1:]):
            if g1 and g1 == g2:
                anom.append(
                    f"lane {lane}: two consecutive LIGHT/{g1} "
                    f"(G-VAR-3 monoculture smell)"
                )
                break  # one report per lane is enough
    if known_lanes:
        idle = [ln for ln in known_lanes if ln not in rows]
        for ln in idle:
            anom.append(
                f"lane {ln}: 0 grain on the window (idle; coordinator did not "
                "stock substance, variation-protocol S4)"
            )
    return anom


# --- rendering -------------------------------------------------------------


def render_table(rows: dict[str, dict]) -> str:
    """Markdown table of the per-lane budget. Numbers are computed, never hard-coded."""
    if not rows:
        return "_(no attributed grains on the window)_"
    header = (
        "| Lane | DEEP | MED | LIGHT | total | budget | consumed | genres |\n"
        "|------|-----:|----:|------:|------:|-------:|---------:|--------|\n"
    )
    lines = []
    # sort by total desc so the most active lane reads first
    for lane, row in sorted(rows.items(), key=lambda kv: -kv[1]["total"]):
        genres = ", ".join(sorted(row["genres"])) or "-"
        over = ""
        if row["over"] > 0:
            over = f"  (+{row['over']} over)"
        lines.append(
            f"| {lane} | {row['DEEP']} | {row['MED']} | {row['LIGHT']} | "
            f"{row['total']} | {row['budget']} | {row['consumed']}{over} | {genres} |"
        )
    return header + "\n".join(lines)


def render_anomalies(anom: list[str]) -> str:
    if not anom:
        return "_no anomaly detected_"
    return "\n".join(f"- {a}" for a in anom)


# --- CLI -------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="Aggregate Grain: tags of merged PRs into a per-lane "
        "budget table (variation-protocol overview, #9859)."
    )
    src = p.add_mutually_exclusive_group()
    src.add_argument(
        "--days",
        type=int,
        default=DEFAULT_DAYS,
        help=f"live mode: query the last N days of merged PRs via gh "
        f"(default {DEFAULT_DAYS})",
    )
    src.add_argument(
        "--replay",
        metavar="FILE",
        help="offline/acceptance mode: read merged PRs from a JSON file",
    )
    p.add_argument(
        "-R",
        "--repo",
        default=None,
        help="repo for the gh query (default: gh's current repo resolution)",
    )
    p.add_argument(
        "--known-lanes",
        metavar="LANES",
        default=None,
        help="comma-separated canonical lane list (machine:workspace) to "
        "check for idle lanes",
    )
    p.add_argument(
        "--json",
        action="store_true",
        help="emit the aggregation as JSON (machine-readable) instead of a table",
    )
    args = p.parse_args(argv)

    if args.replay:
        prs = load_prs_replay(args.replay)
    else:
        prs = load_prs_days(args.days, repo=args.repo)

    rows = aggregate(prs)
    known = (
        [s.strip() for s in args.known_lanes.split(",") if s.strip()]
        if args.known_lanes
        else None
    )
    anom = detect_anomalies(prs, known_lanes=known)

    if args.json:
        # sets are not JSON-serializable; render as sorted lists
        payload = {
            lane: {**{k: v for k, v in row.items() if k != "genres"}, "genres": sorted(row["genres"])}
            for lane, row in rows.items()
        }
        print(json.dumps({"rows": payload, "anomalies": anom}, ensure_ascii=False, indent=2))
        return 0

    win = f"last {args.days} day(s)" if not args.replay else f"{args.replay}"
    untagged = len(prs) - sum(r["total"] for r in rows.values())
    print(f"## Coordination budget -- {win}\n")
    print(f"_{len(prs)} merged PR(s), {untagged} unattributed._\n")
    print(render_table(rows))
    print(f"\n### Anomalies\n\n{render_anomalies(anom)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
