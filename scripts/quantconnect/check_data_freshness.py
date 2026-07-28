#!/usr/bin/env python3
"""QuantConnect local data freshness checker (Issue #8734 follow-up).

Pourquoi cet outil existe
-------------------------
L'incident fondateur #8734 (decouvert c.942, po-2024) a revele que TOUS les
equity zips locaux (``lean-workspace/data/equity/usa/daily/``) finissent au
**2021-03-31**, et que Lean ``fillDataForward=True`` (defaut) **forward-fill
silencieusement** 2021-04 -> 2026 avec la valeur CONSTANTE du dernier bar. Le
notebook affiche alors une periode "2015 -> 2025" normale (row-count normal)
mais les ~4-5 dernieres annees sont une **ligne plate** -- ce qui produit des
metriques invalidees (B&H ~0%, direction ~100%) sans aucun signal d'erreur.

Ce defaut a invalide 3 livrables equity (#8714 MERGED, #8730, #8719) executes
honnêtement via la recette Docker canonique mais sur data forward-fillee. Il
complement ``audit_quantbooks_unexec.py`` : celui-ci detecte l'absence
d'EXECUTION des cellules ; le present outil detecte la STAGNATION des donnees
qui les nourrissent -- un notebook peut avoir ``execution_count`` non-null sur
toutes ses cellules et pourtant reposer sur une ligne plate.

Ce qu'il fait (DETECTION, pas correction)
-----------------------------------------
Scanme le dossier ``data/`` d'un Lean workspace (equity / forex / crypto
daily zips), lit chaque zip, extrait la premiere et la derniere date, et
signale tout ticker dont les donnees se terminent **avant un seuil de
fraicheur** (defaut : 6 mois avant aujourd'hui, configurable via
``--months-back`` ou ``--min-year``).

  - **FRESH**  -- dernier bar dans la fenetre de fraicheur.
  - **STALE**  -- dernier bar avant la fenetre -> forward-fill probable si
                  ``fillDataForward=True`` (defaut Lean). A NE PAS faire
                  confiance pour une re-exec quantbook post-seuil.

Exit code 1 si au moins un ticker STALE (gatable en CI / pre-exec). Exit 0
si tout est FRESH ou si ``--no-fail`` est passe.

Usage
-----
    python check_data_freshness.py
    python check_data_freshness.py --workspace /path/to/lean-workspace
    python check_data_freshness.py --asset-class equity --min-year 2025
    python check_data_freshness.py --ticker SPY,QQQ,TLT
    python check_data_freshness.py --months-back 12 --quiet

Operationalise les lecons C941-L (ticker present ?) et C942-L (ticker
CURRENT post-seuil ?) : presence != fraicheur. Verifier AVANT toute re-exec
equity/forex quantbook. See #8734, #8724.
"""
from __future__ import annotations

import argparse
import sys
import zipfile
from datetime import date
from pathlib import Path

try:
    from dateutil.relativedelta import relativedelta  # type: ignore
except Exception:  # dateutil may be absent on a bare runner
    relativedelta = None


# Asset-class -> relative glob of daily zips under <workspace>/data/.
# Crypto layout is vendor/market (e.g. crypto/binance/daily), equity/forex are
# market/resolution (equity/usa/daily, forex/fxcm/daily). We glob generously.
ASSET_CLASS_GLOBS = {
    "equity": ["equity/*/daily/*.zip"],
    "forex": ["forex/*/daily/*.zip"],
    "crypto": ["crypto/*/daily/*.zip"],
}


def parse_qc_date(token: str) -> date | None:
    """Parse a QuantConnect CSV date token ('YYYYMMDD HH:MM' or 'YYYYMMDD')."""
    s = token.strip().split(" ")[0]
    if len(s) == 8 and s.isdigit():
        try:
            return date(int(s[:4]), int(s[4:6]), int(s[6:8]))
        except ValueError:
            return None
    return None


def scan_zip(path: Path) -> tuple[date | None, date | None, int]:
    """Return (first_date, last_date, row_count) for a QC daily zip.

    QC daily zips hold one CSV (named like the ticker) with no header row :
    each line is 'YYYYMMDD HH:MM,o,h,l,c,v'. We read first + last line only
    (cheap, avoids loading multi-GB minute files -- we only scan daily).
    """
    try:
        with zipfile.ZipFile(path) as z:
            names = [n for n in z.namelist() if n.lower().endswith(".csv")]
            if not names:
                return None, None, 0
            raw = z.read(names[0]).decode("utf-8", errors="replace")
    except (zipfile.BadZipFile, OSError):
        return None, None, 0

    lines = [ln for ln in raw.split("\n") if ln.strip()]
    if not lines:
        return None, None, 0

    first = parse_qc_date(lines[0].split(",")[0])
    last = parse_qc_date(lines[-1].split(",")[0])
    return first, last, len(lines)


def find_workspace(start: Path) -> Path | None:
    """Walk up from `start` to find the nearest dir containing lean.json."""
    cur = start.resolve()
    for parent in [cur, *cur.parents]:
        if (parent / "lean.json").exists() and (parent / "data").is_dir():
            return parent
    return None


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    p.add_argument(
        "workspace",
        nargs="?",
        help="Lean workspace dir (contains lean.json + data/). Auto-detected if omitted.",
    )
    p.add_argument("--asset-class", choices=["equity", "forex", "crypto", "all"], default="all")
    p.add_argument("--min-year", type=int, help="Flag tickers whose data ends before Jan 1 of this year.")
    p.add_argument("--months-back", type=int, default=6, help="Freshness window in months (default 6). Ignored if --min-year set.")
    p.add_argument("--ticker", help="Comma-separated tickers to filter (case-insensitive).")
    p.add_argument("--quiet", action="store_true", help="Summary line only.")
    p.add_argument("--no-fail", action="store_true", help="Always exit 0 (report only, do not gate).")
    args = p.parse_args(argv)

    if args.min_year is not None:
        threshold = date(args.min_year, 1, 1)
        threshold_lbl = f"< {args.min_year}-01-01"
    else:
        if relativedelta is not None:
            threshold = date.today() - relativedelta(months=args.months_back)
        else:
            # Bare-runner fallback: approximate months as 30.4 days.
            from datetime import timedelta
            threshold = date.today() - timedelta(days=int(args.months_back * 30.4))
        threshold_lbl = f"> {args.months_back} months old (before {threshold.isoformat()})"

    ws_arg = Path(args.workspace) if args.workspace else Path.cwd()
    ws = find_workspace(ws_arg) if not args.workspace else (ws_arg if (ws_arg / "lean.json").exists() else find_workspace(ws_arg))
    if ws is None:
        print(f"ERROR: no Lean workspace (lean.json + data/) found from {ws_arg}", file=sys.stderr)
        return 2
    data_dir = ws / "data"
    if not data_dir.is_dir():
        print(f"ERROR: {data_dir} has no data/ folder", file=sys.stderr)
        return 2

    classes = list(ASSET_CLASS_GLOBS) if args.asset_class == "all" else [args.asset_class]
    ticker_filter = {t.strip().lower() for t in args.ticker.split(",")} if args.ticker else None

    rows = []  # (asset_class, ticker, first, last, count, stale)
    for cls in classes:
        for pattern in ASSET_CLASS_GLOBS[cls]:
            for zpath in sorted(data_dir.glob(pattern)):
                ticker = zpath.stem.lower()
                # Normalise crypto stems (btcusdt_quote -> btcusdt).
                if cls == "crypto":
                    ticker = ticker.split("_")[0]
                if ticker_filter and ticker not in ticker_filter:
                    continue
                first, last, count = scan_zip(zpath)
                if last is None:
                    continue
                stale = last < threshold
                rows.append((cls, ticker, first, last, count, stale))

    if not rows:
        print(f"No daily zips found under {data_dir} for asset-class={args.asset_class}.")
        return 0

    # Dedupe crypto (quote/trade variants of same pair -> keep the newest last-date).
    dedup = {}
    for cls, ticker, first, last, count, stale in rows:
        key = (cls, ticker)
        if key not in dedup or last > dedup[key][3]:
            dedup[key] = (cls, ticker, first, last, count, stale)
    rows = sorted(dedup.values(), key=lambda r: (r[0], r[1]))

    n_stale = sum(1 for r in rows if r[5])
    n_fresh = len(rows) - n_stale

    if not args.quiet:
        print(f"Lean workspace : {ws}")
        print(f"Data folder    : {data_dir}")
        print(f"Freshness rule : flag tickers ending {threshold_lbl}")
        print()
        print(f"{'Asset':<7} {'Ticker':<12} {'First':<12} {'Last':<12} {'Rows':>7}  Status")
        print("-" * 62)
        for cls, ticker, first, last, count, stale in rows:
            status = "STALE" if stale else "FRESH"
            print(f"{cls:<7} {ticker:<12} {first.isoformat():<12} {last.isoformat():<12} {count:>7}  {status}")
        print("-" * 62)

    by_cls_stale = {}
    for cls, _, _, _, _, stale in rows:
        by_cls_stale[cls] = by_cls_stale.get(cls, 0) + (1 if stale else 0)
    stale_breakdown = ", ".join(f"{c}={n}" for c, n in sorted(by_cls_stale.items()) if n) or "none"

    print(f"Total {len(rows)} ticker(s) : {n_fresh} FRESH, {n_stale} STALE (breakdown: {stale_breakdown}).")
    if n_stale:
        print(f"WARNING: {n_stale} ticker(s) have data ending before the freshness window.")
        print("Lean fillDataForward=True (default) will silently forward-fill these as a")
        print("CONSTANT -> invalidates post-threshold metrics. See #8734.")

    if n_stale and not args.no_fail:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
