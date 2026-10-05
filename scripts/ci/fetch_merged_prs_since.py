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
import hashlib
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

# TTL du cache PAR TRANCHE (#19236). Le cache de fenetre vit au-dessus (une
# seule entree pour tout `[since, tomorrow)`), donc a chaque expiration de
# celui-ci **toutes** les tranches repartaient en appels `gh` live -- 7 min 25 s
# a froid, payees une fois par heure et par lane. Une tranche dont le `until`
# est anterieur ou egal au debut du jour courant est CLOSE : les fusions d'une
# journee passee n'arrivent plus, la re-interroger ne peut rien rapporter. La
# tranche qui contient le jour courant, elle, bouge encore.
PAST_SLICE_TTL_SECONDS = 30 * 24 * 60 * 60
CURRENT_SLICE_TTL_SECONDS = 10 * 60

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
    )
    return json.loads(out.stdout)


def slice_cache_key(since: str, until: str, fields: str) -> str:
    """Cle stable d'une tranche : elle change avec la tranche ET le jeu de champs.

    Le jeu de champs entre dans la cle parce que le meme `[since, until)` ramene
    un payload different selon `--json` (`files` est le champ le plus cher). Deux
    appelants aux besoins differents ne doivent pas se servir mutuellement une
    reponse amputee.
    """
    material = json.dumps(
        {"schema": 1, "slice": [since, until], "fields": fields},
        sort_keys=True, separators=(",", ":"),
    )
    return "slice-" + hashlib.sha256(material.encode("utf-8")).hexdigest()[:24]


def cached_run(run, cache, *, today: date, fields: str, mode: str = "auto",
               past_ttl: float = PAST_SLICE_TTL_SECONDS,
               current_ttl: float = CURRENT_SLICE_TTL_SECONDS):
    """Enveloppe `run` d'un cache **par tranche** (#19236).

    `cache` est duck-type : tout objet exposant
    ``get_or_fetch(key, ttl_seconds, fetch, *, mode=...)`` et rendant un objet
    portant ``.payload``. On ne l'importe pas d'ici -- ce module vit sous
    `scripts/ci/` et la couche de cache sous `scripts/` ; l'injection evite au
    test de dependre d'un `sys.path` commun.

    Le choix de TTL est le coeur du correctif : une tranche dont le `until` est
    anterieur ou egal a `today` est close (les fusions d'une journee passee
    n'arrivent plus), l'autre contient le jour courant et reste courte. La
    comparaison est lexicographique sur des dates ISO, donc exacte.
    """
    today_iso = today.isoformat()

    def wrapped(since: str, until: str) -> list[dict]:
        ttl = past_ttl if until <= today_iso else current_ttl
        result = cache.get_or_fetch(
            slice_cache_key(since, until, fields),
            ttl,
            lambda: run(since, until),
            mode=mode,
        )
        return result.payload

    return wrapped


def fetch(since: str, run=None, slice_days: int = SLICE_DAYS,
          today: date | None = None, fields: str = DEFAULT_FIELDS,
          *, slice_cache=None, slice_cache_mode: str = "auto",
          past_slice_ttl: float = PAST_SLICE_TTL_SECONDS,
          current_slice_ttl: float = CURRENT_SLICE_TTL_SECONDS) -> list[dict]:
    """Walk ``[since, tomorrow)`` in date slices and merge them into one list.

    ``run`` is dependency-injected for tests -- a two-argument callable
    ``(since, until) -> list[dict]``. When it is omitted, the real fetch is
    bound to ``fields`` (so an injected fake keeps its two-argument contract).

    A slice that returns exactly ``SEARCH_RESULT_CAP`` items was truncated by
    the search API: it is halved and retried, and a one-day slice still at the
    cap raises -- returning it would silently drop merges and hand the caller a
    partial sequence that looks complete.
    """
    if run is None:
        run = lambda s, u: run_gh(s, u, fields)  # noqa: E731
    day = today or date.today()
    if slice_cache is not None:
        # Le cache s'installe SOUS la logique de decoupage : le halving d'une
        # tranche saturee continue de s'appliquer, chaque sous-tranche ayant sa
        # propre cle. Un cache pose au-dessus du decoupage figerait la tranche
        # tronquee au lieu de la laisser se scinder.
        run = cached_run(run, slice_cache, today=day, fields=fields,
                         mode=slice_cache_mode, past_ttl=past_slice_ttl,
                         current_ttl=current_slice_ttl)
    start = date.fromisoformat(since)
    end = day + timedelta(days=1)
    acc: list[dict] = []
    seen: set[int] = set()
    cur = start
    while cur < end:
        width = max(1, slice_days)
        while True:
            nxt = min(cur + timedelta(days=width), end)
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
