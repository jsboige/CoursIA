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
import sys
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


def _make_flatten_layout(bulk: pd.DataFrame, n_bars: int):
    """Build the layout a true ``self.history(..., flatten=True)`` would deliver.

    Returns ``(arr, sym_codes, n_bars)`` for ``_path_flatten_array_no_df``:

    - ``arr``: ``ndarray`` of shape ``(n_symbols * n_bars,)`` containing
      the close values, sorted by ``(time, symbol)`` -- the layout
      implied by the QC ``flatten=True`` docs (numpy structured array).
    - ``sym_codes``: ``ndarray`` of the same length, each entry being
      the integer index of the symbol on that row.
    - ``n_bars``: echoed back for signature parity with the DataFrame
      pistes.

    This helper is the cost-equivalent of what the QC bridge would have
    to produce client-side: a single ndarray + an aligned codes vector,
    already sorted. The post-fetch Python transform measured by
    ``_path_flatten_array_no_df`` is therefore the **Python-side floor**
    of any ``flatten=True`` migration -- not a measurement of
    ``flatten=True`` itself (po-2027 is RECOVERABLE-USER-HAND on QC API,
    see MEMORY ``qc-cycle-gating-recoverable-user-hand.md``).
    """
    sym_list = list(bulk.index.get_level_values("symbol").unique())
    sym_codes_full = pd.Categorical(
        bulk.index.get_level_values("symbol"), categories=sym_list
    ).codes
    time_codes = pd.Categorical(bulk.index.get_level_values("time")).codes
    order = np.lexsort((time_codes, sym_codes_full))
    arr = bulk["close"].values[order].astype(np.float64, copy=False)
    sym_codes = sym_codes_full[order].astype(np.int64, copy=False)
    return arr, sym_codes, n_bars


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
    """Piste C: in-memory transformation of a pre-built bulk DataFrame.

    HONEST SCOPE (REPAIR 2026-09-14, c.1148 adjoint re-review): this path
    measures the **transformation** of a bulk the QC bridge already
    returned as a DataFrame. It does NOT model ``flatten=True`` because
    a real ``flatten=True`` would not produce a DataFrame in the first
    place -- there would be no ``Categorical`` / ``MultiIndex`` to
    convert. The transformation measured here is what carver13.py:381
    does today, swapping one pandas construction (xs-slice) for another
    (``Categorical`` + ``lexsort`` + ``searchsorted``). A genuine
    ``flatten=True`` WINNER would have to be measured by an entirely
    separate bench on QC Cloud, which is out of scope here (po-2027
    RECOVERABLE-USER-HAND on QC API, see MEMORY
    qc-cycle-gating-recoverable-user-hand.md).

    Bottom line: this bench discriminates A vs B vs C **as different
    ways to slice the same DataFrame**, NOT as a comparison with a
    real ``flatten=True`` return shape. The previous PR's "WINNER
    flatten=True" framing was an over-attribution, flagged by the
    adjoint preflight on 2026-09-14.
    """
    bulk = _synthesize_bulk_noop(bulk_cache)
    sym_list = list(bulk.index.get_level_values("symbol").unique())
    out = {}
    # `flatten=True` semantics would skip this Categorical step entirely;
    # what we actually do is xs-slice + Categorical + lexsort + copy.
    close_values = bulk["close"].values
    sym_codes = pd.Categorical(
        bulk.index.get_level_values("symbol"), categories=sym_list
    ).codes
    time_codes = pd.Categorical(bulk.index.get_level_values("time")).codes
    order = np.lexsort((time_codes, sym_codes))
    sorted_sym = sym_codes[order]
    sorted_close = close_values[order]
    boundaries = np.searchsorted(sorted_sym, np.arange(len(sym_list)))
    for i, sym in enumerate(sym_list):
        start = boundaries[i]
        end = boundaries[i + 1] if i + 1 < len(sym_list) else len(sorted_sym)
        if end - start < 256 + 2:
            continue
        out[sym] = sorted_close[start:end].copy()
    return out


def _path_flatten_array_no_df(arr: np.ndarray, sym_codes: np.ndarray, n_bars: int) -> Dict[str, np.ndarray]:
    """Piste C_alt: array-only path -- if the QC bridge returned ndarray.

    Receives a pre-built ndarray ``arr`` of shape (n_symbols * n_bars,)
    plus an aligned ``sym_codes`` integer array (each row's symbol
    index) -- the QC ``flatten=True`` contract from the docs (numpy
    structured array sorted (time, symbol)).

    This is **NOT** a guarantee of what ``self.history(flatten=True)``
    actually returns. It is a ``what-if'' measurement that quantifies
    the lower bound: even with a perfectly contiguous ndarray and a
    zero-cost sym→array split, how fast is the post-fetch transform?
    The carver13 EWMAC forecasts downstream of this dict are bit-equal
    to A/B/C (test_all_pistes_return_identical_close_arrays pins this),
    so a future PR that moves to ``flatten=True`` would inherit this
    measurement as its Python-side floor.

    Difference vs ``_path_flatten_array``: skips the DataFrame->ndarray
    extraction, the Categorical codes, and the lexsort. The bulk is
    already in the layout the flatten contract would deliver.
    """
    out = {}
    n_symbols = int(sym_codes.max()) + 1 if len(sym_codes) > 0 else 0
    boundaries = np.searchsorted(sym_codes, np.arange(n_symbols))
    for i in range(n_symbols):
        start = boundaries[i]
        end = boundaries[i + 1] if i + 1 < n_symbols else len(sym_codes)
        if end - start < 256 + 2:
            continue
        # Direct ndarray slice; no copy because contiguous (per flatten
        # contract) -- in the wild, a defensive copy may be needed, but
        # this is the floor.
        out[f"SYM{i:02d}"] = arr[start:end]
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
    """Run a path n_iter times, return timing stats.

    Reports median + IQR (p25/p75) + 5/95 percentiles. IQR is what the
    verdict WINNER criterion uses ("non-overlapping IQRs"); reporting
    it without computing it is the exact fabrication the 2026-09-14
    REPAIR (#16093, adjoint preflight) called out.

    ``path_fn`` may be 0-arg (built with --measure-construction, which
    re-builds the bulk internally) or N-arg (the usual pre-built bulk
    + n_bars). We introspect the signature once and adapt.
    """
    import inspect as _inspect

    try:
        n_params = len(_inspect.signature(path_fn).parameters)
    except (TypeError, ValueError):
        n_params = len(args)
    is_zero_arg = n_params == 0

    samples = []
    for _ in range(n_iter):
        t0 = time.perf_counter()
        if is_zero_arg:
            path_fn()
        else:
            path_fn(*args)
        samples.append(time.perf_counter() - t0)
    samples.sort()
    n = len(samples)
    # quantiles(..., n=4) gives quartiles [p25, p50, p75]; under Python 3.8+
    # the IQR endpoint convention is the inclusive one -- what reviewers
    # expect from "interquartile range".
    quartiles = quantiles(samples, n=4, method="inclusive") if n >= 4 else [
        samples[0], samples[n // 2], samples[-1]
    ]
    return {
        "median_ms": median(samples) * 1000.0,
        "p25_ms": quartiles[0] * 1000.0,
        "p75_ms": quartiles[2] * 1000.0,
        "iqr_ms": (quartiles[2] - quartiles[0]) * 1000.0,
        "p05_ms": samples[max(0, int(0.05 * n))] * 1000.0,
        "p95_ms": samples[min(n - 1, int(0.95 * n))] * 1000.0,
        "n_iter": n_iter,
    }


def _iqr_disjoint(baseline: Dict[str, float], candidate: Dict[str, float]) -> bool:
    """True iff the candidate IQR sits entirely below the baseline IQR.

    Used by the WINNER verdict (in addition to the ratio < 0.70 guard)
    so that a noisy single-trial speedup cannot masquerade as an
    improvement. With n_iter >= 30 the IQR spans ~50% of samples, so
    disjoint IQRs are a sterner test than the median ratio.
    """
    return candidate["p75_ms"] < baseline["p25_ms"]


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
        help="Emit JSON only on stdout (stderr keeps human-readable progress).",
    )
    parser.add_argument(
        "--measure-construction",
        action="store_true",
        help="Include the synthetic-bulk construction cost in the timed "
        "frontier. Default OFF: the bench times the post-fetch path on a "
        "pre-built bulk (the production path receives a fully built bulk "
        "from the QC bridge, never constructs it client-side).",
    )
    args = parser.parse_args()

    # Convention: --json -> stdout = pure JSON document, stderr = human
    # chatter. Before the REPAIR (adjoint preflight 2026-09-14), all
    # output went to stdout and `json.loads(stdout)` failed on line 1.
    def _say(msg: str) -> None:
        if args.json:
            print(msg, file=sys.stderr)
        else:
            print(msg)

    _say(f"Building synthetic bulk frames (n_iter={args.n_iter})")
    bulk_baseline = _make_synthetic_bulk(N_BARS_BASELINE)
    bulk_reduced = _make_synthetic_bulk(N_BARS_REDUCED)
    bulk_slim = _make_synthetic_bulk(N_BARS_SLIM)
    _say(
        f"  baseline={bulk_baseline.shape}, reduced={bulk_reduced.shape}, "
        f"slim={bulk_slim.shape}"
    )
    if args.measure_construction:
        _say("  --measure-construction ON: bulk build included in timed frontier.")

    # paths[i] = (label, callable, *args). The callable is what _time_path
    # will run n_iter times. With --measure-construction, the callable is
    # wrapped so the bulk build is part of the measurement -- this is what
    # lets the verdict attribute (or refuse to attribute) the speedup to
    # pandas construction.
    def _maybe_wrap_with_construction(fn, n_bars):
        if not args.measure_construction:
            return fn
        def wrapped():
            # Re-build every call to attribute cost to construction as well.
            bulk = _make_synthetic_bulk(n_bars, seed=42)
            return fn(bulk, n_bars)
        return wrapped

    paths = [
        ("A_baseline_bulk (current, #16003)", _maybe_wrap_with_construction(_path_baseline_bulk, N_BARS_BASELINE), bulk_baseline, N_BARS_BASELINE),
        ("B_per_symbol (19 history calls)", _maybe_wrap_with_construction(_path_per_symbol, N_BARS_BASELINE), bulk_baseline, N_BARS_BASELINE),
        ("C_flatten_array (DataFrame->array, REPAIR scope)", _maybe_wrap_with_construction(_path_flatten_array, N_BARS_BASELINE), bulk_baseline, N_BARS_BASELINE),
        ("C_alt_no_df (true flatten=True layout, ndarray floor)", _path_flatten_array_no_df, _make_flatten_layout(bulk_baseline, N_BARS_BASELINE), N_BARS_BASELINE),
        ("D_reduce_n_bars (592->336)", _maybe_wrap_with_construction(_path_reduce_n_bars, N_BARS_REDUCED), bulk_reduced, N_BARS_REDUCED),
        ("D'_observe_only_n_bars_slim (592->276, vol_lookback dropped, observation-only)", _maybe_wrap_with_construction(_path_reduce_n_bars_slim, N_BARS_SLIM), bulk_slim, N_BARS_SLIM),
    ]

    results = {}
    for name, fn, bulk, n_bars in paths:
        # C_alt_no_df takes a (arr, sym_codes, n_bars) tuple -- unpack it
        # so _time_path gets the right *args.
        if name.startswith("C_alt_"):
            arr, sym_codes, _ = bulk
            stats = _time_path(fn, arr, sym_codes, n_bars, n_iter=args.n_iter)
        else:
            stats = _time_path(fn, bulk, n_bars, n_iter=args.n_iter)
        results[name] = stats
        _say(
            f"  {name:42s} median={stats['median_ms']:7.3f} ms  "
            f"iqr={stats['iqr_ms']:6.3f}  p25={stats['p25_ms']:6.3f}  "
            f"p75={stats['p75_ms']:6.3f}  p05={stats['p05_ms']:6.3f}  "
            f"p95={stats['p95_ms']:6.3f}"
        )

    baseline_stats = results["A_baseline_bulk (current, #16003)"]
    baseline_median = baseline_stats["median_ms"]
    _say("")
    _say("Verdict (vs baseline A; WINNER requires ratio < 0.70 AND IQR disjoint):")
    verdicts = {}
    winner_details = {}
    for name, stats in results.items():
        if name.startswith("A_"):
            verdicts[name] = "BASELINE"
            continue
        ratio = stats["median_ms"] / baseline_median
        iqr_disjoint = _iqr_disjoint(baseline_stats, stats)
        if ratio < 0.70 and iqr_disjoint:
            verdict = "WINNER (<70% AND IQR disjoint)"
        elif ratio < 0.70:
            verdict = "NEUTRAL_MEDIAN_ONLY (ratio<0.70 but IQR overlaps baseline)"
        elif ratio > 1.30:
            verdict = "LOSER (>130% of baseline)"
        else:
            verdict = "NEUTRAL (within +/-30% of baseline)"
        verdicts[name] = verdict
        winner_details[name] = {"ratio": ratio, "iqr_disjoint": iqr_disjoint}
        _say(f"  {name:42s} ratio={ratio:.2f}  iqr_disjoint={iqr_disjoint}  {verdict}")

    _say("")
    _say("Anti-fabrication note: this bench times only the Python-side path.")
    _say("The 236 ms/call reported by #16076 is dominated by the QC bridge")
    _say("(Lean-side MCP/IPC), which is NOT modelled here. A WINNER on this")
    _say("bench saves at most ~25 s of the 694 s wall (the 'everything else'")
    _say("bucket on #16076 instrumentation), and only if the QC-side cost")
    _say("scales with Python processing time, which is unverified.")
    _say("Scope: with --measure-construction OFF (default), the bench measures")
    _say("the POST-FETCH transformation of a pre-built bulk -- not bulk")
    _say("construction. To attribute a speedup to 'pandas construction', pass")
    _say("--measure-construction (and re-run).")
    _say("")
    _say("Piste scope notes (REPAIR 2026-09-14, c.1148 adjoint re-review):")
    _say("  - C_flatten_array: DataFrame->array transformation, NOT flatten=True.")
    _say("    A true flatten=True would not produce a DataFrame in the first")
    _say("    place; the Categorical/lexsort measured here is what carver13")
    _say("    already does with xs-slices. The 'WINNER flatten=True' framing")
    _say("    of v1 was an over-attribution.")
    _say("  - C_alt_no_df: array-only floor. Quantifies the Python-side lower")
    _say("    bound assuming the QC bridge delivered a sorted ndarray; the")
    _say("    QC side itself remains unverified (po-2027 RECOVERABLE-USER-HAND).")
    _say("  - D_reduce_n_bars: vol_lookback preserved; safe path.")
    _say("  - D'_observe_only_n_bars_slim: vol_lookback dropped (Likely UNSAFE")
    _say("    for vol_lookback=60 + 20 of EWMA burn-in). Listed for")
    _say("    observation of per-row construction cost only. NOT a recommendation")
    _say("    to ship: levers QC-side (reducing n_bars) are out of scope of this")
    _say("    Python-side bench and require neutrality on forecasts/orders/")
    _say("    backtest before adoption.")
    _say("Conclusion: the 5 pistes in #16076 are unlikely to deliver the")
    _say("94% wall reduction the issue implies; the real lever is")
    _say("REDUCING THE NUMBER OF history() CALLS (caching the bulk across")
    _say("consecutive same-day rebalances, or skipping rebalances where")
    _say("nothing changes), not micro-optimising the slice path. See the")
    _say("generated JSON for full numbers and the JSON keys used by CI.")

    if args.json:
        import json as _json
        out = {
            "n_iter": args.n_iter,
            "n_symbols": N_SYMBOLS,
            "measure_construction": args.measure_construction,
            "shapes": {
                "baseline": list(bulk_baseline.shape),
                "reduced": list(bulk_reduced.shape),
                "slim": list(bulk_slim.shape),
            },
            "paths": results,
            "verdicts": verdicts,
            "winner_details": winner_details,
            "baseline_median_ms": baseline_median,
            "scope_note": (
                "Times only Python-side processing; QC-side cost is not modelled."
                " Local WINNER != 94% wall reduction. WINNER requires BOTH"
                " ratio < 0.70 AND IQR (p25..p75) disjoint from baseline."
                " C is in-memory DataFrame->array transform, NOT flatten=True."
                " C_alt_no_df is the Python-side floor assuming flatten=True layout."
                " D' slim drops vol_lookback (Likely UNSAFE) and is observation-only."
            ),
        }
        # Pure JSON on stdout, one document, terminated by a newline.
        sys.stdout.write(_json.dumps(out, indent=2))
        sys.stdout.write("\n")


def main_with_args(argv: List[str]) -> int:
    """Testable entrypoint: same as ``main()`` but accepts an argv list.

    Splitting stdout/stderr means a subprocess test can assert
    ``json.loads(stdout)`` succeeds AND that progress chatter lives on
    stderr. See tests/test_history_pistes_bench.py:TestREPAIRAdjointPreflight16093.
    """
    old_argv = sys.argv
    try:
        sys.argv = ["bench_carver13_history_pistes"] + list(argv)
        main()
    except SystemExit as e:
        # argparse calls sys.exit(2) on bad args; tests treat that as
        # an expected error code. The happy path returns None (0).
        return e.code if isinstance(e.code, int) else 1
    finally:
        sys.argv = old_argv
    return 0


if __name__ == "__main__":
    sys.exit(main_with_args(sys.argv[1:]))
