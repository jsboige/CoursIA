#!/usr/bin/env python3
r"""fetch_merged_prs_since.py -- fetch merged PRs merged since a date (date-sliced).

## Why

The G-VAR-3 adjacency guard resolves a lane's REAL predecessor from the merged
sequence (`variation_adjacency_guard.py --merged-prs-file`). When this fetch
returns nothing, the caller's `|| rm -f` degrades the guard to the frozen
`prev:` field the worker wrote themselves -- so G-VAR-3 stops measuring what
actually merged and starts measuring a declaration. That degradation is silent
by construction: the guard still runs, still passes or blocks, and nothing in
its output says which axis it used unless you read `prev_source`.

Two distinct mechanisms have produced that degradation:

1. **#12636** -- `gh pr list --limit 100` orders by CREATION date, so a
   low-activity lane's grain merged days ago fell out of the batch. Fixed by
   searching on `merged:>=` (merge-time).

2. **This file, until 2026-08-29** -- the fix for (1) paginated with
   `gh pr list ... --page N`. **`gh pr list` has no `--page` flag** (it belongs
   to `gh api`). Every real invocation therefore raised `CalledProcessError`,
   emitted nothing, and fell back to `declared` -- measured that day on 5/5
   sampled PRs (#12459, #13473, #13472, #13465, #13456), i.e. repo-wide, for
   the whole life of the script. The three unit tests all injected a fake
   `run`, so the argv was never once executed against a real `gh`.

## Why date slices rather than a bigger --limit

`--search` goes through GitHub's search API, which caps a result set at **1000**
server-side. Measured 2026-08-29: `--limit 1000` and `--limit 1500` both return
exactly 1000, while the real 21-day window held **2289** merged PRs. A single
call therefore cannot cover the window, and the 1289 it drops are the OLDEST --
precisely where a quiet lane's predecessor lives. Raising `--limit` looks like a
fix and reproduces the original bug.

Slicing the window by date keeps every request under the cap using only flags
that exist. Measured slice occupancy at `SLICE_DAYS = 3` over 2026-08-08..29:
275 / 340 / 403 / 379 / 310 / 227 / 296 -- max 403, i.e. 2.5x headroom. A slice
that comes back AT the cap is halved and retried; a one-day slice still at the
cap raises rather than truncating, because a silent truncation here is
indistinguishable from a healthy fetch.

## Output

A single JSON array on stdout:

    [{"number": 123, "body": "...", "mergedAt": "2026-08-24T09:32:39Z"}, ...]

## Usage

    python3 scripts/ci/fetch_merged_prs_since.py --days 21 > /tmp/merged_prs.json
    python3 scripts/ci/fetch_merged_prs_since.py --since 2026-08-01 > /tmp/merged_prs.json
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import date, timedelta

# GitHub's search API caps a result set at 1000 items. Measured 2026-08-29:
# `gh pr list --search "merged:>=..." --limit 1000` and `--limit 1500` both
# return exactly 1000. A batch of this size is therefore NOT a measurement --
# it is the cap, and it hides everything past it.
SEARCH_RESULT_CAP = 1000

# Width of one query window. 3 days keeps the busiest observed slice (403) at
# ~40% of the cap. Slices are halved on demand, so this is a starting point,
# not a throughput assumption.
SLICE_DAYS = 3

# Borne de transport d'une tranche (#19643). L'appelant du picker attrape
# explicitement subprocess.TimeoutExpired (pick_idle_grain.py, fetch_visits) --
# mais cette plomberie restait morte : sans `timeout=` ici, un `gh` ralenti
# (secondary rate limit, backoff silencieux) suspendait le tirage entier sans
# borne. 120 s couvre genereseument une tranche observee a quelques secondes ;
# au-dela, la tranche echoue et l'appelant rend « affluence non mesuree »
# (jamais un zero de mesure presente comme zero d'affluence, #19209) -- le
# picker degraded vaut mieux qu'un picker pendu qui fabrique des faux
# diagnostics chez l'agent appelant (mesure 2026-10-07 : trois runs tues au
# timeout de l'outil, un faux « pend » poste avant la mesure qui l'a falsifiee).
GH_TIMEOUT_SECONDS = 120

# Ancrage FIXE de la grille de tranches (#19236). Une grille ancree a `since`
# se decale d'un jour a chaque appel (`since` avance avec la date du jour) :
# des cles de cache par tranche ne vivraient alors qu'un jour. En alignant
# les bornes interieures sur un multiple de `slice_days` depuis une date
# fixe, la tranche [b, b+3) garde la MEME cle d'un jour a l'autre -- une
# tranche passee, immuable une fois la journee close, reste servie par le
# cache au lieu d'etre re-telechargee chaque matin. Seul
# `(jour - SLICE_ANCHOR).days % slice_days` compte : n'importe quelle date
# fixe convient.
SLICE_ANCHOR = date(2026, 1, 5)

DEFAULT_DAYS = 21

# Champs demandes par defaut. Les appelants qui n'ont besoin que du corps et de
# la date gardent ce jeu : `files` est le champ le plus cher de l'API (il porte
# la liste des fichiers touches), et le demander pour rien paie le cout sans la
# donnee. Un appelant qui a besoin des fichiers (le tapis, via `family_of`)
# passe `fields=` explicitement.
DEFAULT_FIELDS = "number,body,mergedAt"


def since_date(days: int) -> str:
    """Return the ISO cutoff ``today - days``."""
    return (date.today() - timedelta(days=days)).isoformat()


def run_gh(since: str, until: str, fields: str = DEFAULT_FIELDS) -> list[dict]:
    """One date slice of merged PRs, ``[since, until)`` on MERGE time.

    Uses only flags `gh pr list` actually has -- `--search` and `--limit`.
    Injected as ``run`` by the tests; `test_run_gh_argv_is_accepted_by_gh`
    executes this exact argv against the real binary, which is the control
    the `--page` regression escaped for its whole life.

    Bounded by ``GH_TIMEOUT_SECONDS`` (#19643) : sans borne, un `gh` ralenti
    pendait chaque tranche indefiniment -- l'appelant du picker attrape
    ``TimeoutExpired`` sans que rien ne puisse jamais le lever.
    """
    out = subprocess.run(
        [
            "gh", "pr", "list",
            "--state", "merged",
            "--search", f"merged:>={since} merged:<{until}",
            "--limit", str(SEARCH_RESULT_CAP),
            "--json", fields,
        ],
        capture_output=True, text=True, encoding="utf-8", errors="replace", check=True,
        timeout=GH_TIMEOUT_SECONDS,
    )
    return json.loads(out.stdout)


def aligned_boundaries(start: date, end: date, slice_days: int):
    """Base slices covering ``[start, end)``, interior edges on fixed anchors.

    The FIRST slice may be partial ``[start, b)`` where ``b`` is the first
    boundary AFTER ``start`` aligned on ``SLICE_ANCHOR`` (no partial slice
    when ``start`` is already aligned); the following ones are aligned
    ``[b, b + k)``; the LAST is clipped at ``end``. Coverage is identical to
    a grid anchored at ``start`` -- only the position of interior edges
    changes, and that position is what makes a slice key stable from one day
    to the next (#19236).
    """
    k = max(1, slice_days)
    offset = (start - SLICE_ANCHOR).days % k
    aligned = start + timedelta(days=k if offset == 0 else k - offset)
    cur = start
    while cur < end:
        stop = min(aligned, end)
        yield cur, stop
        cur = stop
        aligned = cur + timedelta(days=k)


def fetch(since: str, run=None, slice_days: int = SLICE_DAYS,
          today: date | None = None, fields: str = DEFAULT_FIELDS) -> list[dict]:
    """Walk ``[since, tomorrow)`` in date slices and merge them into one list.

    ``run`` is dependency-injected for tests -- a two-argument callable
    ``(since, until) -> list[dict]``. When it is omitted, the real fetch is
    bound to ``fields`` (so an injected fake keeps its two-argument contract).

    A slice that returns exactly ``SEARCH_RESULT_CAP`` items was truncated by
    the search API: it is halved and retried, and a one-day slice still at the
    cap raises -- returning it would silently drop merges and hand the caller a
    partial sequence that looks complete.

    Since #19236, interior slice edges are anchored on ``SLICE_ANCHOR`` (cf
    ``aligned_boundaries``) so a given past slice keeps the same
    ``(since, until)`` bounds across days -- the caller caches per slice, and
    a grid anchored at ``since`` would re-key every entry once a day.
    """
    if run is None:
        run = lambda s, u: run_gh(s, u, fields)  # noqa: E731
    start = date.fromisoformat(since)
    end = (today or date.today()) + timedelta(days=1)
    acc: list[dict] = []
    seen: set[int] = set()
    for base_cur, bound in aligned_boundaries(start, end, slice_days):
        cur = base_cur
        while cur < bound:
            width = min(max(1, slice_days), (bound - cur).days)
            while True:
                nxt = cur + timedelta(days=width)
                batch = run(cur.isoformat(), nxt.isoformat())
                if len(batch) < SEARCH_RESULT_CAP or width == 1:
                    break
                width = max(1, width // 2)
            if len(batch) >= SEARCH_RESULT_CAP:
                raise RuntimeError(
                    f"fetch_merged_prs_since: the single day {cur.isoformat()} "
                    f"returned {len(batch)} PRs, at the search cap of "
                    f"{SEARCH_RESULT_CAP}. The window cannot be sliced any finer, "
                    "so the result would be silently truncated -- failing instead."
                )
            for pr in batch:
                n = pr.get("number")
                if n is not None and n not in seen:
                    seen.add(n)
                    acc.append(pr)
            cur = nxt
    return acc


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--days", type=int, default=None,
                   help=f"fetch PRs merged within the last N days (default {DEFAULT_DAYS})")
    p.add_argument("--since", metavar="YYYY-MM-DD", default=None,
                   help="fetch PRs merged on or after this date (overrides --days)")
    args = p.parse_args(argv)

    if args.since:
        since = args.since
    else:
        since = since_date(args.days if args.days is not None else DEFAULT_DAYS)

    try:
        prs = fetch(since)
    except (subprocess.CalledProcessError, json.JSONDecodeError, OSError,
            RuntimeError, ValueError) as e:
        print(f"fetch_merged_prs_since: {e}", file=sys.stderr)
        return 1

    # Windows stdout est cp1252 -- forcer UTF-8 (UnicodeEncodeError sinon, #15184).
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    json.dump(prs, sys.stdout, ensure_ascii=False)
    print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
