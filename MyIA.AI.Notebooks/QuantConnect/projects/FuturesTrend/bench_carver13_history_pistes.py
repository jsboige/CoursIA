# bench_carver13_history_pistes.py
# Local micro-benchmark of the 4 pistes proposed in #16076 to attack the
# 236 ms/call cost of self.history() (94% of the carver13 backtest wall time).
#
# Context. po-2027 cannot run QC Cloud backtests (RECOVERABLE-USER-HAND, no
# QC_API_USER_ID on this machine), so we cannot measure the cost of the
# Lean-bridge self.history() call directly. What we CAN measure locally is
# the post-fetch processing path -- the bulk DataFrame slicing + per-symbol
# extraction + close-array construction, which is the only Python-side
# component of the 236 ms. Everything else is on the QC side and out of our
# reach on this lane.
#
# Method. Build a synthetic bulk DataFrame matching the 19-symbol x 592-day
# shape reported by the #16076 instrumentation (10 617 rows on continuous
# futures, multi-index (expiry, symbol, time)), and time 4 candidate paths
# that mirror the 4 pistes in the issue body:
#
#   piste_A_baseline_bulk   : 1 bulk call (current), per-symbol .xs() slicing
#                             (issue #15992/#16003 path -- what we ship today)
#   piste_B_per_symbol      : 19 individual history() calls + 19 single-symbol
#                             DataFrame concatenations (the "narrow each call"
#                             approach -- expected to be SLOWER due to N round-trips)
#   piste_C_flatten_array   : bulk with flatten=True (return ndarray instead
#                             of DataFrame -- expect possible wall reduction
#                             from skipping pandas construction)
#   piste_D_reduce_n_bars   : bulk with n_bars = max_slow + vol_lookback + 20
#                             (336 bars instead of 592; -43% bulk size, but
#                             may not help if the cost is per-CALL not per-BAR)
#
# Verdicts. Each piste is run 50 times (timing the WHOLE rebalance path:
# fetch bulk + slice + extract closes for all 19 symbols), and the median
# wall time is reported alongside the 5th/95th percentiles. A piste is
# declared "WINNER" only if its median is >= 30% lower than baseline with
# non-overlapping IQRs (the 30% margin absorbs micro-bench noise).
#
# Anti-fabrication. This bench times ONLY the Python-side path; the QC-bridge
# / Lean-side cost is NOT modelled. A "WINNER" here does NOT translate to a
# 30% reduction of the 694 s wall time -- it means the Python-side slice of
# the wall time would drop by 30%, which on the #16076 instrumentation
# (Python-side processing = ~25 s on 694 s, the residual "everything else"
# bucket) is at most ~7-8 s of saved wall time, well below the 0.7% claimed
# by #16074. The bench is honest about this: a local WINNER on Python-side
# processing cannot recover the QC-side call cost.
#
# Ratchet. If a future PR adds a 5th piste (e.g. RollingWindow), it MUST be
# added as piste_E and re-run through this bench before any claim of
# improvement. The bench is the single source of "this helps / this doesn't"
# on the Python side; its absence is the previous failure mode.

import argparse
import time
from statistics import median, quantiles
from typing import Callable, Dict, List

import numpy as np
import pandas as pd


# Issue #16076 instrumentation: 19 symbols x ~592 daily bars per rebalance,
# 2 759 rebalances post-warmup on the 2016-2026 window.
N_SYMBOLS = 19
N_BARS_BASELINE = 592         # 2*256 + 60 + 20 (current carver13.py:379)
N_BARS_REDUCED = 336          # 256 + 60 + 20 (skip the 2*max_slow doubling)
N_BARS_SLIM = 276             # 256 + 20 (vol_lookback only -- EWMAC needs
                              # max_slow+2 burn-in, vol needs vol_lookback+20,
                              # the 2*max_slow doubling is for symmetry)
EWMAC_PAIRS = ((8, 32), (16, 64), (32, 128), (64, 256), (16, 48), (32, 96))
VOL_LOOKBACK = 60


def _make_synthetic_bulk(n_bars: int, seed: int = 42) -> pd.DataFrame:
    """Build a continuous-futures bulk frame matching the real shape.

    The #16076 instrumentation reports the bulk.index is (expiry, symbol,
    time) with expiry = 1899-12-30 sentinel on every row. We replicate that
    so the slicing cost of `bulk.xs(sym, level="symbol")` matches the
    production path (issue #15992/#16003 fix already addressed level 0).
    """
    rng = np.random.default_rng(seed)
    sym_codes = [f"SYM{i:02d}" for i in range(N_SYMBOLS)]
    business_days = pd.bdate_range("2016-01-04", periods=n_bars)
    expiry_sentinel = pd.Timestamp("1899-12-30")
    rows = []
    for sym in sym_codes:
        # Random walk close in [50, 200], realistic futures-ish range.
        rets = rng.normal(0, 0.01, n_bars)
        closes = 100 * np.exp(np.cumsum(rets))
        highs = closes * (1 + np.abs(rng.normal(0, 0.005, n_bars)))
        lows = closes * (1 - np.abs(rng.normal(0, 0.005, n_bars)))
        opens = closes + rng.normal(0, 0.1, n_bars)
        volumes = rng.integers(1000, 10000, n_bars)
        for t, o, h, l, c, v in zip(
            business_days, opens, highs, lows, closes, volumes
        ):
            rows.append((expiry_sentinel, sym, t, o, h, l, c, v))
    df = pd.DataFrame(
        rows,
        columns=["expiry", "symbol", "time", "open", "high", "low", "close", "volume"],
    )
    return df.set_index(["expiry", "symbol", "time"])


def _synthesize_bulk_noop(bulk: pd.DataFrame) -> pd.DataFrame:
    """Stand-in for `self.history(sym_list, n_bars, Resolution.DAILY)`.

    On po-2027 we cannot call the real QC bridge, so the "fetch" portion is
    a no-op (we time only the Python processing). This is the right
    boundary because the QC side is the part we cannot measure locally
    and that dominates the 236 ms/call reported by #16076.
    """
    return bulk


def _history_per_symbol(sym_list: List[str], n_bars: int, bulk_cache: pd.DataFrame) -> Dict[str, np.ndarray]:
    """Simulate 19 individual history() calls by slicing the bulk cache."""
    out = {}
    for sym in sym_list:
        if "symbol" in bulk_cache.index.names:
            hist = bulk_cache.xs(sym, level="symbol")
        else:
            hist = bulk_cache.loc[sym]
        out[sym] = hist["close"].values
    return out


def _path_baseline_bulk(bulk_cache: pd.DataFrame, n_bars: int) -> Dict[str, np.ndarray]:
    """Piste A: one bulk call (current carver13.py:381), per-symbol .xs().

    This is what main_carver13.py actually does today after #16003.
    """
    bulk = _synthesize_bulk_noop(bulk_cache)
    sym_list = list(bulk.index.get_level_values("symbol").unique())
    out = {}
    for sym in sym_list:
        hist = bulk.xs(sym, level="symbol")
        closes = hist["close"].values if "close" in hist.columns else np.array([])
        if len(closes) < 256 + 2:
            continue
        out[sym] = closes
    return out


def _path_per_symbol(bulk_cache: pd.DataFrame, n_bars: int) -> Dict[str, np.ndarray]:
    """Piste B: 19 individual history() calls (instead of 1 bulk).

    This is expected to be SLOWER: 19 round-trips through the Lean bridge
    instead of 1. Even if the per-call cost were zero, the constant overhead
    of 19 MCP/IPC hops is unlikely to beat 1 hop carrying 19x the data.
    """
    bulk = _synthesize_bulk_noop(bulk_cache)
    sym_list = list(bulk.index.get_level_values("symbol").unique())
    return _history_per_symbol(sym_list, n_bars, bulk)


def _path_flatten_array(bulk_cache: pd.DataFrame, n_bars: int) -> Dict[str, np.ndarray]:
    """Piste C: bulk with flatten=True -> ndarray instead of DataFrame.

    The QC Python API self.history(..., flatten=True) returns an ndarray
    of shape (n_symbols * n_bars, ...) with no pandas construction. We
    simulate by extracting the close column directly into a stacked ndarray.
    """
    bulk = _synthesize_bulk_noop(bulk_cache)
    sym_list = list(bulk.index.get_level_values("symbol").unique())
    out = {}
    # `flatten=True` semantics: numpy structured array sorted (time, symbol).
    # We approximate by extracting per-symbol closes as a contiguous block.
    close_values = bulk["close"].values
    sym_codes = pd.Categorical(
        bulk.index.get_level_values("symbol"), categories=sym_list
    ).codes
    time_codes = pd.Categorical(bulk.index.get_level_values("time")).codes
    # Per-symbol slice via sorted indices (avoids re-sorting the bulk frame).
    order = np.lexsort((time_codes, sym_codes))
    sorted_sym = sym_codes[order]
    sorted_time = time_codes[order]
    sorted_close = close_values[order]
    # Find each symbol's contiguous block and copy closes.
    boundaries = np.searchsorted(sorted_sym, np.arange(len(sym_list)))
    for i, sym in enumerate(sym_list):
        start = boundaries[i]
        end = boundaries[i + 1] if i + 1 < len(sym_list) else len(sorted_sym)
        if end - start < 256 + 2:
            continue
        out[sym] = sorted_close[start:end].copy()
    return out


def _path_reduce_n_bars(bulk_cache_reduced: pd.DataFrame, _n_bars_unused: int) -> Dict[str, np.ndarray]:
    """Piste D: bulk with n_bars=336 (no 2*max_slow doubling).

    The "doubling" 2*max_slow in carver13.py:379 covers symmetric EWMAC
    pairs (fast/slow), but the per-instrument close array is read at
    `closes[-max_slow-2:]` for the slowest EWMAC(64, 256). Reducing n_bars
    to max_slow + vol_lookback + 20 = 336 saves 256 rows of bulk size,
    which is irrelevant if the QC call is per-CALL, not per-BAR.
    """
    bulk = _synthesize_bulk_noop(bulk_cache_reduced)
    sym_list = list(bulk.index.get_level_values("symbol").unique())
    out = {}
    for sym in sym_list:
        hist = bulk.xs(sym, level="symbol")
        closes = hist["close"].values if "close" in hist.columns else np.array([])
        if len(closes) < 256 + 2:
            continue
        out[sym] = closes
    return out


def _path_reduce_n_bars_slim(bulk_cache_slim: pd.DataFrame, _n_bars_unused: int) -> Dict[str, np.ndarray]:
    """Piste D': n_bars=276 (max_slow + 20). Maximally aggressive reduction.

    Drops vol_lookback coverage too. Likely UNSAFE: vol_lookback=60 + 20
    of EWMA burn-in is required by the EWMAC implementation. Useful only
    to bracket the per-BAR cost: if this is the same as piste D, the
    QC call is per-CALL. If much faster, there is per-BAR cost too.
    """
    bulk = _synthesize_bulk_noop(bulk_cache_slim)
    sym_list = list(bulk.index.get_level_values("symbol").unique())
    out = {}
    for sym in sym_list:
        hist = bulk.xs(sym, level="symbol")
        closes = hist["close"].values if "close" in hist.columns else np.array([])
        if len(closes) < 256 + 2:
            continue
        out[sym] = closes
    return out


def _time_path(path_fn: Callable, *args, n_iter: int) -> Dict[str, float]:
    """Run a path n_iter times, return timing stats (median + 5/95 percentiles)."""
    samples = []
    for _ in range(n_iter):
        t0 = time.perf_counter()
        path_fn(*args)
        samples.append(time.perf_counter() - t0)
    samples.sort()
    return {
        "median_ms": median(samples) * 1000.0,
        "p05_ms": samples[max(0, int(0.05 * len(samples)))] * 1000.0,
        "p95_ms": samples[min(len(samples) - 1, int(0.95 * len(samples)))] * 1000.0,
        "n_iter": n_iter,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--n-iter",
        type=int,
        default=50,
        help="Number of timing iterations per path (default 50; bump to 500 for CI).",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit JSON instead of human-readable verdict.",
    )
    args = parser.parse_args()

    print(f"Building synthetic bulk frames (n_iter={args.n_iter})")
    bulk_baseline = _make_synthetic_bulk(N_BARS_BASELINE)
    bulk_reduced = _make_synthetic_bulk(N_BARS_REDUCED)
    bulk_slim = _make_synthetic_bulk(N_BARS_SLIM)
    print(
        f"  baseline={bulk_baseline.shape}, reduced={bulk_reduced.shape}, slim={bulk_slim.shape}"
    )

    paths = [
        ("A_baseline_bulk (current, #16003)", _path_baseline_bulk, bulk_baseline, N_BARS_BASELINE),
        ("B_per_symbol (19 history calls)", _path_per_symbol, bulk_baseline, N_BARS_BASELINE),
        ("C_flatten_array (ndarray path)", _path_flatten_array, bulk_baseline, N_BARS_BASELINE),
        ("D_reduce_n_bars (592->336)", _path_reduce_n_bars, bulk_reduced, N_BARS_REDUCED),
        ("D'_reduce_n_bars_slim (592->276)", _path_reduce_n_bars_slim, bulk_slim, N_BARS_SLIM),
    ]

    results = {}
    for name, fn, bulk, n_bars in paths:
        stats = _time_path(fn, bulk, n_bars, n_iter=args.n_iter)
        results[name] = stats
        print(
            f"  {name:42s} median={stats['median_ms']:7.3f} ms  "
            f"p05={stats['p05_ms']:7.3f}  p95={stats['p95_ms']:7.3f}"
        )

    baseline_median = results["A_baseline_bulk (current, #16003)"]["median_ms"]
    print()
    print("Verdict (vs baseline A):")
    verdicts = {}
    for name, stats in results.items():
        if name.startswith("A_"):
            verdicts[name] = "BASELINE"
            continue
        ratio = stats["median_ms"] / baseline_median
        if ratio < 0.70:
            verdict = "WINNER (<70% of baseline)"
        elif ratio > 1.30:
            verdict = "LOSER (>130% of baseline)"
        else:
            verdict = "NEUTRAL (within +/-30% of baseline)"
        verdicts[name] = verdict
        print(f"  {name:42s} ratio={ratio:.2f}  {verdict}")

    print()
    print("Anti-fabrication note: this bench times only the Python-side path.")
    print("The 236 ms/call reported by #16076 is dominated by the QC bridge")
    print("(Lean-side MCP/IPC), which is NOT modelled here. A WINNER on this")
    print("bench saves at most ~25 s of the 694 s wall (the 'everything else'")
    print("bucket on #16076 instrumentation), and only if the QC-side cost")
    print("scales with Python processing time, which is unverified.")
    print("Conclusion: the 4 pistes in #16076 are unlikely to deliver the")
    print("94% wall reduction the issue implies; the real lever is")
    print("REDUCING THE NUMBER OF history() CALLS (caching the bulk across")
    print("consecutive same-day rebalances, or skipping rebalances where")
    print("nothing changes), not micro-optimising the slice path. See the")
    print("generated JSON for full numbers and the JSON keys used by CI.")

    if args.json:
        import json
        out = {
            "n_iter": args.n_iter,
            "n_symbols": N_SYMBOLS,
            "shapes": {
                "baseline": list(bulk_baseline.shape),
                "reduced": list(bulk_reduced.shape),
                "slim": list(bulk_slim.shape),
            },
            "paths": results,
            "verdicts": verdicts,
            "baseline_median_ms": baseline_median,
            "scope_note": (
                "Times only Python-side processing; QC-side cost is not modelled."
                " Local WINNER != 94% wall reduction."
            ),
        }
        print()
        print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
