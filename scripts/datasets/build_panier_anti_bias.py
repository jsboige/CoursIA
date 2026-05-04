"""
Build anti-bias panier: diversified multi-asset dataset for ML training.

Downloads 22+ symbols across asset classes via yfinance, validates coverage,
and generates a summary CSV + quality report.

Anti-bias policy:
- FORBIDDEN: AAPL, MSFT, GOOG, AMZN, NVDA, TSLA, META (individual FAANG+ tech)
- Required: broad indices, sector ETFs, bonds, commodities, intl, crypto

Usage:
    python scripts/datasets/build_panier_anti_bias.py
    python scripts/datasets/build_panier_anti_bias.py --start 2015-01-01 --interval 1d
    python scripts/datasets/build_panier_anti_bias.py --skip-download  # use cached only
"""

import argparse
import json
import logging
import sys
from datetime import datetime
from pathlib import Path

import pandas as pd

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger(__name__)

DEFAULT_OUTPUT_DIR = "MyIA.AI.Notebooks/QuantConnect/datasets/panier"
DEFAULT_START = "2015-01-01"
DEFAULT_END = datetime.now().strftime("%Y-%m-%d")

# Anti-bias: these symbols are FORBIDDEN in new trainings
FORBIDDEN_SYMBOLS = {"AAPL", "MSFT", "GOOG", "AMZN", "NVDA", "TSLA", "META"}

# Panier definition: diversified multi-asset
PANIER = {
    "us_equity_broad": {
        "SPY": "S&P 500",
        "RSP": "S&P 500 Equal Weight",
        "IWM": "Russell 2000",
    },
    "us_equity_sectors": {
        "XLF": "Financials",
        "XLK": "Technology (broad ETF, not single stock)",
        "XLV": "Healthcare",
        "XLY": "Consumer Discretionary",
        "XLP": "Consumer Staples",
        "XLI": "Industrials",
        "XLU": "Utilities",
        "XLB": "Materials",
        "XLRE": "Real Estate",
        "XLC": "Communication Services",
    },
    "volatility": {
        "VIX": "CBOE Volatility Index (^VIX)",
    },
    "us_bonds": {
        "TLT": "20+ Year Treasury",
        "IEF": "7-10 Year Treasury",
        "SHY": "1-3 Year Treasury",
    },
    "commodities": {
        "GLD": "Gold",
        "USO": "Crude Oil",
        "DBA": "Agriculture",
    },
    "international": {
        "EFA": "Developed Markets ex-US",
        "EEM": "Emerging Markets",
    },
    "crypto": {
        "BTC-USD": "Bitcoin",
        "ETH-USD": "Ethereum",
        "LTC-USD": "Litecoin",
        "XRP-USD": "Ripple",
    },
}

# yfinance ticker format (VIX needs ^VIX prefix)
TICKER_MAP = {
    "VIX": "^VIX",
}


def get_all_symbols() -> list[str]:
    """Get flat list of all panier symbols."""
    symbols = []
    for group in PANIER.values():
        symbols.extend(group.keys())
    return symbols


def get_group(symbol: str) -> str:
    """Get the asset class group for a symbol."""
    for group_name, group_dict in PANIER.items():
        if symbol in group_dict:
            return group_name
    return "unknown"


def download_panier(symbols: list[str], start: str, end: str, interval: str, output_dir: Path, use_cache: bool = True) -> dict[str, Path]:
    """Download all panier symbols via yfinance with caching."""
    try:
        from scripts.datasets.download_yfinance import download
    except ImportError:
        sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))
        from scripts.datasets.download_yfinance import download

    results = {}
    for symbol in symbols:
        yf_symbol = TICKER_MAP.get(symbol, symbol)
        paths = download([yf_symbol], start, end, interval, output_dir, use_cache=use_cache)
        if paths:
            results[symbol] = paths[0]
        else:
            log.warning("No data for %s (yfinance: %s)", symbol, yf_symbol)
    return results


def validate_panier(output_dir: Path, symbols: list[str], start: str, end: str) -> dict:
    """Validate panier coverage and quality."""
    report = {"total_symbols": len(symbols), "validation_date": datetime.now().isoformat()}
    issues = []
    coverage = {}

    for symbol in symbols:
        pattern = f"{symbol.replace('-', '_')}_*.csv"
        matches = list(output_dir.glob(pattern))
        if not matches:
            # Try yfinance-style naming (^VIX -> VIX, ^VIX -> ^VIX)
            yf_symbol = TICKER_MAP.get(symbol, symbol)
            for variant in [yf_symbol.replace('-', '_').replace('^', ''), yf_symbol.replace('-', '_')]:
                pattern2 = f"{variant}_*.csv"
                matches = list(output_dir.glob(pattern2))
                if matches:
                    break

        if not matches:
            issues.append({"symbol": symbol, "issue": "no_data_file"})
            coverage[symbol] = {"status": "missing"}
            continue

        df = pd.read_csv(matches[0], index_col=0, parse_dates=True)
        date_col = df.index.name or "Date"
        n_rows = len(df)
        actual_start = str(df.index.min())
        actual_end = str(df.index.max())
        n_nans = int(df["Close"].isna().sum()) if "Close" in df.columns else -1

        coverage[symbol] = {
            "status": "ok",
            "file": matches[0].name,
            "rows": n_rows,
            "start": actual_start,
            "end": actual_end,
            "nan_close": n_nans,
            "group": get_group(symbol),
        }

        # Check for forbidden symbols in the data
        if symbol in FORBIDDEN_SYMBOLS:
            issues.append({"symbol": symbol, "issue": "FORBIDDEN_SYMBOL"})

    report["coverage"] = coverage
    report["issues"] = issues
    report["num_ok"] = sum(1 for v in coverage.values() if v["status"] == "ok")
    report["num_missing"] = sum(1 for v in coverage.values() if v["status"] == "missing")

    # Group summary
    group_counts = {}
    for sym, info in coverage.items():
        if info["status"] == "ok":
            grp = info.get("group", "unknown")
            group_counts[grp] = group_counts.get(grp, 0) + 1
    report["groups"] = group_counts

    return report


def generate_summary_csv(output_dir: Path, symbols: list[str]) -> Path:
    """Generate a single summary CSV with all symbols' close prices aligned."""
    closes = {}
    for symbol in symbols:
        pattern = f"{symbol.replace('-', '_')}_*.csv"
        matches = list(output_dir.glob(pattern))
        if not matches:
            continue
        df = pd.read_csv(matches[0], index_col=0, parse_dates=True)
        if "Close" in df.columns:
            closes[symbol] = df["Close"]

    if not closes:
        log.warning("No data to generate summary CSV")
        return None

    panel = pd.DataFrame(closes)
    panel.index.name = "Date"
    out_path = output_dir / "panier_close_all.csv"
    panel.to_csv(out_path)
    log.info("Summary CSV: %s (%d rows, %d symbols)", out_path, len(panel), len(panel.columns))
    return out_path


def main():
    parser = argparse.ArgumentParser(description="Build anti-bias multi-asset panier dataset")
    parser.add_argument("--start", default=DEFAULT_START, help="Start date (YYYY-MM-DD)")
    parser.add_argument("--end", default=DEFAULT_END, help="End date (YYYY-MM-DD)")
    parser.add_argument("--interval", default="1d", help="Data interval (default: 1d)")
    parser.add_argument("--output-dir", default=DEFAULT_OUTPUT_DIR, help="Output directory")
    parser.add_argument("--skip-download", action="store_true", help="Use cached files only")
    parser.add_argument("--validate-only", action="store_true", help="Only validate existing files")
    args = parser.parse_args()

    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    symbols = get_all_symbols()
    log.info("Panier: %d symbols across %d asset classes", len(symbols), len(PANIER))

    # Check for forbidden symbols
    forbidden_in_panier = [s for s in symbols if s in FORBIDDEN_SYMBOLS]
    if forbidden_in_panier:
        log.error("FORBIDDEN symbols in panier: %s", forbidden_in_panier)
        sys.exit(1)

    # Download
    if not args.skip_download and not args.validate_only:
        log.info("Downloading panier data: %s → %s, interval=%s", args.start, args.end, args.interval)
        results = download_panier(symbols, args.start, args.end, args.interval, output_dir)
        log.info("Downloaded: %d/%d symbols", len(results), len(symbols))

    # Validate
    report = validate_panier(output_dir, symbols, args.start, args.end)
    log.info("=== Validation Report ===")
    log.info("  OK: %d/%d symbols", report["num_ok"], report["total_symbols"])
    log.info("  Groups: %s", report["groups"])
    if report["issues"]:
        log.warning("  Issues: %s", report["issues"])

    # Generate summary CSV
    summary_path = generate_summary_csv(output_dir, symbols)

    # Save report
    report_path = output_dir / "panier_report.json"
    with open(report_path, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2, default=str)
    log.info("Saved report: %s", report_path)

    # Print summary
    print(f"\n{'='*60}")
    print(f"Anti-Bias Panier Dataset Summary")
    print(f"{'='*60}")
    print(f"Output:      {output_dir}")
    print(f"Symbols:     {report['num_ok']}/{report['total_symbols']} OK")
    print(f"Date range:  {args.start} → {args.end}")
    print(f"Groups:      {report['groups']}")
    if report["issues"]:
        print(f"Issues:      {len(report['issues'])}")
        for iss in report["issues"]:
            print(f"  - {iss['symbol']}: {iss['issue']}")
    if summary_path:
        print(f"Summary CSV: {summary_path}")
    print(f"Report:      {report_path}")

    # Anti-bias declaration
    print(f"\n{'='*60}")
    print(f"ANTI-BIAS DECLARATION")
    print(f"{'='*60}")
    print(f"This panier contains NO individual FAANG+ tech stocks.")
    print(f"Forbidden symbols: {', '.join(sorted(FORBIDDEN_SYMBOLS))}")
    print(f"Approved for: ML/Trading Curriculum SOTA 2026 training")
    print(f"Coverage: {len(PANIER)} asset classes, {report['num_ok']} instruments")


if __name__ == "__main__":
    main()
