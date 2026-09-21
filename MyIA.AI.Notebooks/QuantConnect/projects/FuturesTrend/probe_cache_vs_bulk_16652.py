# region imports
from AlgorithmImports import *
import numpy as np

from main_carver13 import CarverThirteen
# endregion


class CarverThirteenCacheProbe(CarverThirteen):
    """#16652 divergence sonde: 16076 cache windows vs fresh history() bulk.

    Additive diagnostic arm. The production arm (main_carver13.py) is
    untouched: this subclass only OBSERVES. On every rebalance day, for
    every ticker served from the sliding-window cache (i.e. NOT re-fetched
    today by the production invalidator), we additionally pull a fresh
    bulk history() and compare the cached closes deque against the fresh
    closes. Any divergence is a cache-vs-bulk mismatch the current
    invalidator (mapped-contract change) does NOT cover -- a candidate
    "missing invalidator" per issue #16652.

    Divergence shape discriminates the hypotheses:
    - full-window : the whole past was re-scaled (BACKWARDS_RATIO re-scale
      without a detected Mapped change)
    - head        : oldest bars differ -> window boundary shift
    - tail        : recently appended on_data bars differ from the fresh
      bulk's last bars (live-bar normalization vs historical, or calendar
      misalignment between the bar stream and history())
    - middle      : historical data revision inside the window
    - length-only : same values on the common tail but different lengths
      (per-symbol cadence drift between on_data appends and history())

    Cost: one extra bulk history() call per served day (~236 ms measured
    in #16073), so the probe run deliberately reverts the #16076 wall gain
    (735 s -> 69 s became ~700-800 s again). One-off diagnostic, not the
    production arm.
    """

    def initialize(self):
        super().initialize()
        self._probe = {
            "compared_days": 0,
            "divergent_days": 0,
            "divergent_ticks": 0,
            "patterns": {},
            "log_budget": 200,
            "examples": [],
        }
        self._fetch_stamp = {}

    def _seed_windows(self, bulk):
        super()._seed_windows(bulk)
        for t, w in self._roll_cache.items():
            if w["primed"]:
                self._fetch_stamp[t] = self.time

    def _stale_tickers(self):
        stale = super()._stale_tickers()
        # Compare every ticker NOT re-fetched today. On the seed day
        # (stale is None) every ticker is re-fetched, so nothing to compare.
        if self._cache_seeded and stale is not None:
            if stale:
                self.log(
                    f"PROBE16652 REFETCH: {self.time:%Y-%m-%d} tickers={sorted(stale)}"
                )
            self._probe_compare(exclude=set(stale))
        return stale

    def _probe_compare(self, exclude):
        self._probe["compared_days"] += 1
        n_bars = 2 * self.max_slow + self.vol_lookback + 20
        try:
            bulk = self.history(list(self.symbols.values()), n_bars, Resolution.DAILY)
        except Exception as exc:
            self.log(f"PROBE16652 ERROR history: {exc}")
            return
        if bulk is None or bulk.empty:
            self.log(
                f"PROBE16652 AVAIL: {self.time:%Y-%m-%d} fresh bulk EMPTY "
                f"while cache serves"
            )
            return
        sym_level = "symbol" if "symbol" in bulk.index.names else 0
        day_div = False
        for ticker, sym in self.symbols.items():
            if ticker in exclude:
                continue
            w = self._roll_cache[ticker]
            if not w["primed"] or len(w["closes"]) == 0:
                continue
            try:
                hist = (
                    bulk.xs(sym, level="symbol")
                    if sym_level == "symbol"
                    else bulk.loc[sym]
                )
            except KeyError:
                continue
            fresh = (
                hist["close"].values.astype(float)
                if "close" in hist.columns
                else np.array([])
            )
            if fresh.size == 0:
                continue
            cached = np.array(w["closes"], dtype=float)
            k = min(fresh.size, cached.size)
            if k == 0:
                continue
            rel = np.abs(cached[-k:] - fresh[-k:]) / np.maximum(
                np.abs(fresh[-k:]), 1e-12
            )
            bad = np.where(rel > 1e-8)[0]
            len_drift = cached.size - fresh.size
            if bad.size == 0 and len_drift == 0:
                continue
            day_div = True
            self._probe["divergent_ticks"] += 1
            if bad.size == 0:
                pattern = "length-only"
            elif bad.size > 0.5 * k:
                pattern = "full-window"
            elif bad.max() < k / 2:
                pattern = "head"
            elif bad.min() > k / 2:
                pattern = "tail"
            else:
                pattern = "middle"
            self._probe["patterns"][pattern] = (
                self._probe["patterns"].get(pattern, 0) + 1
            )
            if self._probe["log_budget"] > 0:
                self._probe["log_budget"] -= 1
                stamp = self._fetch_stamp.get(ticker)
                days_since = (self.time - stamp).days if stamp else -1
                max_rel = float(rel[bad].max()) if bad.size else 0.0
                div_line = (
                    f"DIV {self.time:%Y-%m-%d} {ticker} "
                    f"pattern={pattern} n_bad={int(bad.size)}/{k} "
                    f"max_rel={max_rel:.2e} len={cached.size}/{fresh.size} "
                    f"map={self._mapped_contract(sym)}/{w['mapped']} "
                    f"dsf={days_since}"
                )
                self.log(f"PROBE16652 {div_line}")
                if len(self._probe["examples"]) < 8:
                    self._probe["examples"].append(div_line)
        if day_div:
            self._probe["divergent_days"] += 1

    def on_end_of_algorithm(self):
        # QC free tier caps stored logs at 100 kb/backtest, which engine-level
        # order-error rows exhaust on day one (measured run 0f906bb8: storage
        # stopped at 2016-02-18, all PROBE16652 lines dropped). So the probe
        # verdict travels in the final RuntimeError payload, which the API
        # returns verbatim -- the production arm's own instrumentation channel.
        p = self._probe
        probe_payload = (
            f"PROBE16652 SUMMARY: compared_days={p['compared_days']} "
            f"divergent_days={p['divergent_days']} "
            f"divergent_ticks={p['divergent_ticks']} "
            f"patterns={p['patterns']} "
            f"|| {' ; '.join(p['examples'])} || "
        )
        self.log(f"PROBE16652 {probe_payload}")
        try:
            super().on_end_of_algorithm()
        except RuntimeError as exc:
            raise RuntimeError(probe_payload + str(exc)) from None
