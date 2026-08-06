#!/usr/bin/env python3
"""Reproducible Lean daily equity data provisioning (Issue #8734 follow-up).

WHY
---
``check_data_freshness.py`` (#8737) DETECTS stale local equity data. The
converter ``yfinance_to_lean_daily.py`` (#8627) WRITES fresh zips from yfinance.
What was missing -- surfaced by ai-01 c.37 (msg-20260728T220240) -- was the
REPRODUCIBLE PROVISIONING STEP that ties them together: a one-command,
idempotent regen pinned by a COMMITTED manifest, with the freshness gate cabled
in as a post-provision guardrail rather than a tool one has to remember to run.

Without this, a shipped quantbook metric (e.g. #8730 TurnOfMonth Sharpe) rests on
data that is gitignored + machine-local -- unreproducible at the merge gate (the
H.4 trap: the coordinator would merge a Sharpe on the faith of the PR body). The
local equity zips live under ``<lean-workspace>/data/equity/usa/daily/`` which is
``.gitignore``-d (line 581), so zero zips are tracked and only the author's
machine holds the fresh bars. This wrapper makes the regen replayable:
``python provision_lean_data.py --universe turn_of_month`` regenerates exactly
the data behind that metric, then PROVES it FRESH via the same gate that would
catch #8734 -- so the PR body can say "provision by <command>, freshness gate
PASS", verifiable by anyone.

WHAT IT DOES
------------
1. Reads a universe spec from ``lean_universes.manifest.json`` (committed
   provenance: tickers + start + regen_date + issue ref -- the "what data
   produced this Sharpe" record).
2. For each ticker: if ``<dest>/<ticker>.zip`` is already FRESH (last bar year
   >= freshness_min_year) and not ``--force``, SKIP (idempotent -- cheap re-run).
   Otherwise download + convert via ``yfinance_to_lean_daily.convert_one``.
3. After writing, runs the freshness GATE on the provisioned tickers -> exit 1 if
   any STALE. The gate is CABLED (not optional), and the canonical manual
   equivalent (``check_data_freshness.py --workspace ... --min-year ...``) is
   printed so the operator sees the exact pre-exec command.

USAGE
-----
    # Provision one universe into the auto-detected lean-workspace
    python scripts/quantconnect/provision_lean_data.py --universe turn_of_month

    # Provision all universes, force re-download even if already fresh
    python scripts/quantconnect/provision_lean_data.py --all --force

    # Custom dest (e.g. a CI sandbox with no lean-workspace)
    python scripts/quantconnect/provision_lean_data.py \\
        --universe ema_cross_alpha --dest /tmp/prov

Env: any Python with ``yfinance`` (coursia-ml-training has 1.5.2). The converter
imports yfinance lazily, so this module + its offline tests import without
network. See #8734, #8737, #8627.
"""
from __future__ import annotations

import argparse
import json
import sys
from datetime import date
from pathlib import Path
from typing import Callable, Optional

# Sibling imports (same dir). check_data_freshness for the gate primitives,
# yfinance_to_lean_daily for the actual download+convert.
from check_data_freshness import find_workspace, scan_zip
from yfinance_to_lean_daily import convert_one

DEFAULT_MANIFEST = Path(__file__).resolve().parent / "lean_universes.manifest.json"
DEFAULT_MIN_YEAR = 2024  # post-2021 forward-fill cutoff (C942-L)


def load_manifest(path: Path) -> dict:
    """Load + structurally validate the universe manifest."""
    path = Path(path)
    if not path.is_file():
        raise FileNotFoundError(f"Manifest not found: {path}")
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("version") != 1:
        raise ValueError(f"Unsupported manifest version: {data.get('version')!r} (expected 1)")
    if "universes" not in data or not isinstance(data["universes"], dict):
        raise ValueError("Manifest missing 'universes' object")
    for name, spec in data["universes"].items():
        if not spec.get("tickers"):
            raise ValueError(f"Universe {name!r} has no 'tickers'")
    return data


def resolve_dest(dest_arg: Optional[Path], workspace_arg: Optional[Path]) -> Path:
    """Resolve the LEAN daily output folder.

    Precedence: explicit --dest > --workspace (<ws>/data/equity/usa/daily) >
    auto-detected lean-workspace (walk up for lean.json + data/).
    """
    if dest_arg is not None:
        return Path(dest_arg)
    if workspace_arg is not None:
        return Path(workspace_arg) / "data" / "equity" / "usa" / "daily"
    ws = find_workspace(Path.cwd())
    if ws is None:
        raise SystemExit(
            "ERROR: no lean-workspace (lean.json + data/) found from cwd; "
            "pass --dest <folder> or --workspace <lean-workspace>."
        )
    return ws / "data" / "equity" / "usa" / "daily"


def is_fresh(zip_path: Path, min_year: int) -> bool:
    """True iff the zip's last bar year >= min_year (presence != freshness, C942-L)."""
    _first, last, _count, _flat_tail = scan_zip(Path(zip_path))
    if last is None:
        return False
    return last.year >= min_year


def provision_universe(
    spec: dict,
    dest: Path,
    force: bool,
    min_year: int,
    converter: Callable[..., int] = convert_one,
) -> list[tuple[str, str, int, Optional[date]]]:
    """Provision one universe's tickers into ``dest``.

    Idempotent: a ticker whose zip is already FRESH is skipped unless ``force``.
    ``converter`` is injected so offline tests avoid the network (default = the
    real yfinance converter). Returns [(ticker, action, bars, last_date)].
    """
    dest = Path(dest)
    dest.mkdir(parents=True, exist_ok=True)
    start = spec.get("start")
    end = spec.get("end")
    results: list[tuple[str, str, int, Optional[date]]] = []
    for ticker in spec["tickers"]:
        zip_path = dest / f"{ticker.lower()}.zip"
        if zip_path.exists() and not force:
            _first, last, count, _flat_tail = scan_zip(zip_path)
            if last is not None and last.year >= min_year:
                print(f"[skip] {ticker}: FRESH (last {last}, {count} bars) -- --force to re-download")
                results.append((ticker, "skip (fresh)", count, last))
                continue
        bars = converter(ticker, dest, start, end, dry_run=False)
        _first, last, _count, _flat_tail = scan_zip(zip_path)
        print(f"[ok]   {ticker}: provisioned {bars} bars (last {last})")
        results.append((ticker, "provisioned", bars, last))
    return results


def run_gate(dest: Path, tickers: list[str], min_year: int) -> list[tuple[str, Optional[date], int, bool]]:
    """Cabled freshness gate over the universe's tickers.

    Returns [(ticker, last_date, rows, stale)]. Missing zip => stale (True).
    Mirrors check_data_freshness.scan_zip semantics scoped to the provisioned set.
    """
    dest = Path(dest)
    rows: list[tuple[str, Optional[date], int, bool]] = []
    for ticker in tickers:
        zip_path = dest / f"{ticker.lower()}.zip"
        if zip_path.exists():
            _first, last, count, _flat_tail = scan_zip(zip_path)
            stale = True if last is None else last.year < min_year
        else:
            last, count = None, 0
            stale = True
        rows.append((ticker, last, count, stale))
    return rows


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Reproducibly provision LEAN daily equity data for a quantbook universe, with a cabled freshness gate.")
    p.add_argument("--universe", help="Universe name from the manifest (e.g. turn_of_month).")
    p.add_argument("--all", action="store_true", help="Provision every universe in the manifest.")
    p.add_argument("--dest", type=Path, help="LEAN daily output folder (default: <lean-workspace>/data/equity/usa/daily).")
    p.add_argument("--workspace", type=Path, help="Lean workspace dir (resolved to <ws>/data/equity/usa/daily).")
    p.add_argument("--force", action="store_true", help="Re-download even if a ticker is already FRESH.")
    p.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST, help="Path to the universe manifest.")
    p.add_argument("--no-fail", action="store_true", help="Exit 0 even if the freshness gate finds STALE tickers.")
    args = p.parse_args(argv)

    if not args.universe and not args.all:
        p.error("provide --universe <name> or --all")

    manifest = load_manifest(args.manifest)
    min_year = manifest.get("freshness_min_year", DEFAULT_MIN_YEAR)

    if args.all:
        unis = manifest["universes"]
    else:
        assert args.universe is not None
        if args.universe not in manifest["universes"]:
            print(f"ERROR: unknown universe {args.universe!r}; known: {list(manifest['universes'])}", file=sys.stderr)
            return 2
        unis = {args.universe: manifest["universes"][args.universe]}

    dest = resolve_dest(args.dest, args.workspace)

    print(f"Manifest : {args.manifest}")
    print(f"Source   : {manifest.get('source')} via {manifest.get('converter')}")
    print(f"Dest     : {dest}")
    print(f"Gate     : freshness_min_year = {min_year} (post-{min_year - 1} forward-fill cutoff, C942-L)")
    print()

    all_tickers: list[str] = []
    for name, spec in unis.items():
        print(f"=== Universe: {name} ({spec.get('issue', '?')}) -- {len(spec['tickers'])} tickers, "
              f"start={spec.get('start')}, regen_date={spec.get('regen_date')} ===")
        provision_universe(spec, dest, args.force, min_year)
        all_tickers.extend(spec["tickers"])
        print()

    # Cabled gate: verify every provisioned ticker is FRESH before trusting a re-exec.
    print("=== Freshness gate (cabled) ===")
    gate_rows = run_gate(dest, sorted(set(t.lower() for t in all_tickers)), min_year)
    print(f"{'Ticker':<10} {'Last':<12} {'Rows':>7}  Status")
    print("-" * 44)
    n_stale = 0
    for ticker, last, count, stale in gate_rows:
        if stale:
            n_stale += 1
        print(f"{ticker:<10} {last.isoformat() if last else 'MISSING':<12} {count:>7}  {'STALE' if stale else 'FRESH'}")
    print()

    ws_for_cmd = args.workspace or (find_workspace(Path.cwd()) or Path("<lean-workspace>"))
    print(f"Manual equivalent: python scripts/quantconnect/check_data_freshness.py "
          f"--workspace {ws_for_cmd} --min-year {min_year} "
          f"--ticker {','.join(sorted(set(t.lower() for t in all_tickers)))}")

    if n_stale and not args.no_fail:
        print(f"\nFAIL: {n_stale}/{len(gate_rows)} ticker(s) STALE post-provision -- data NOT trustworthy for re-exec. See #8734.",
              file=sys.stderr)
        return 1
    print(f"\nOK: all {len(gate_rows)} ticker(s) FRESH -- re-exec ready.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
