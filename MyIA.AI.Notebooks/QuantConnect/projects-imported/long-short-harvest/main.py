#region imports
from AlgorithmImports import *
import numpy as np
from sklearn.ensemble import RandomForestClassifier
from sklearn.preprocessing import StandardScaler
from collections import deque
#endregion
# Long-Short Volatility Harvest ML
# Source: QC Strategy Library - VolatilityHarvestML Long-Short
# Concept: Long-short equity with ML regime detection, Hurst exponent scoring,
# ATR-based stops, and 3-stage trailing stops. Long book: top 4 market cap stocks.
# Short book: stocks with Hurst > threshold + extension + momentum filters.
# Imported from QC Cloud Project ID: 29687399


class VolatilityHarvestMLLongShort(QCAlgorithm):

    def initialize(self):
        self.set_start_date(2005, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(
            BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN,
        )

        self.settings.free_portfolio_value_percentage = 0.025

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.set_benchmark(self.spy)

        self.gld = self.add_equity("GLD", Resolution.DAILY).symbol

        self.vix = self.add_data(self.CBOE, "VIX", Resolution.DAILY).symbol

        self.long_gross = float(self.get_parameter("long_gross") or 0.9)
        self.short_gross = float(self.get_parameter("short_gross") or 0.6)

        self.universe_settings.resolution = Resolution.DAILY
        self._top_set = set()
        self._last_top_month = -1

        self.ml_tilt = float(self.get_parameter("ml_tilt") or 0.25)
        self.top_weight_max = float(
            self.get_parameter("top_weight_max") or 0.35,
        )
        self.top_weight_min = float(
            self.get_parameter("top_weight_min") or 0.0,
        )

        self.coarse_count = int(self.get_parameter("coarse_count") or 2000)
        self.max_universe = int(self.get_parameter("max_universe") or 150)
        self.top_n = int(self.get_parameter("top_n") or 1)

        self.min_ipo_days = int(self.get_parameter("min_ipo_days") or 365)

        self.lookback_bars = int(
            self.get_parameter("lookback_bars") or 260,
        )
        self.n_list = [10, 10, 40, 60, 90, 100]

        self.sma_len = int(self.get_parameter("sma_len") or 195)
        self.ext_k = float(self.get_parameter("ext_k") or 2.0)
        self.mom_k = float(self.get_parameter("mom_k") or 1.75)
        self.score_threshold = float(
            self.get_parameter("score_threshold") or 0.85,
        )
        self.stop_atr = float(self.get_parameter("stop_atr") or 2.0)

        self._active = []
        self._entry = {}

        self.long_trail_1 = float(
            self.get_parameter("long_trail_1") or 0.095,
        )
        self.long_trail_2 = float(
            self.get_parameter("long_trail_2") or 0.07,
        )
        self.long_trail_3 = float(
            self.get_parameter("long_trail_3") or 0.0485,
        )

        self._long_trail = {}

        self.model = RandomForestClassifier(
            n_estimators=100, max_depth=5, random_state=42,
        )
        self.scaler = StandardScaler()
        self.trained = False
        self.min_training = 504

        self.add_universe(self.coarse_selection, self.fine_selection)

        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 30),
            self.check_signal_long,
        )

        self.schedule.on(
            self.date_rules.month_start("SPY"),
            self.time_rules.after_market_open("SPY", 60),
            self.train_model,
        )

        self.schedule.on(
            self.date_rules.every(DayOfWeek.MONDAY),
            self.time_rules.after_market_open(self.spy, 30),
            self.rebalance_short,
        )

        self.schedule.on(
            self.date_rules.every_day(self.spy),
            self.time_rules.after_market_open(self.spy, 160),
            self.risk_check_short,
        )

        self.schedule.on(
            self.date_rules.every_day(self.spy),
            self.time_rules.after_market_open(self.spy, 90),
            self.risk_check_long,
        )

        self.set_warm_up(252)

    def _safe_set_holdings(self, symbol, target_weight):
        pv = float(self.portfolio.total_portfolio_value)
        if pv <= 0:
            return
        mr = float(self.portfolio.margin_remaining)
        max_abs = max(0.0, mr / pv)
        w = float(np.clip(float(target_weight), -max_abs, max_abs))
        self.set_holdings(symbol, w)

    def coarse_selection(self, coarse):
        filtered = [
            c for c in coarse
            if c.has_fundamental_data
            and c.price is not None and c.price > 5
            and c.dollar_volume is not None and c.dollar_volume > 2e7
        ]
        filtered.sort(key=lambda c: c.dollar_volume, reverse=True)
        return [c.symbol for c in filtered[:self.coarse_count]]

    def fine_selection(self, fine):
        today = self.time.date()

        if self.time.month != self._last_top_month:
            fine_mc = [f for f in fine if f.market_cap and f.market_cap > 0]
            fine_mc.sort(key=lambda f: f.market_cap, reverse=True)
            self._top_set = set([f.symbol for f in fine_mc[:4]])
            self._last_top_month = self.time.month

        kept = []
        for f in fine:
            if not f.market_cap or f.market_cap < 1_000_000_000:
                continue

            sr = f.security_reference
            if sr is None or sr.ipo_date is None:
                continue

            days_since_ipo = (today - sr.ipo_date.date()).days
            if days_since_ipo < self.min_ipo_days:
                continue

            kept.append(f)

        kept.sort(key=lambda f: f.dollar_volume, reverse=True)
        short_symbols = [f.symbol for f in kept[:self.max_universe]]
        self._active = short_symbols

        return list(set(short_symbols) | set(self._top_set))

    def _cap_and_renormalize(self, weights, total, wmin, wmax):
        w = np.array(weights, dtype=float)
        n = len(w)
        if n == 0:
            return w

        if wmin > 0:
            w = np.maximum(w, wmin)
        if wmax > 0:
            w = np.minimum(w, wmax)

        target = float(total)
        for _ in range(10):
            s = float(np.sum(w))
            diff = target - s
            if abs(diff) < 1e-8:
                break

            if diff > 0:
                adjustable = [
                    i for i in range(n)
                    if (wmax <= 0 or w[i] < wmax - 1e-12)
                ]
            else:
                adjustable = [
                    i for i in range(n)
                    if (wmin <= 0 or w[i] > wmin + 1e-12)
                ]

            if not adjustable:
                break

            incr = diff / float(len(adjustable))
            for i in adjustable:
                w[i] += incr

            if wmin > 0:
                w = np.maximum(w, wmin)
            if wmax > 0:
                w = np.minimum(w, wmax)

        return w

    def _pick_overweight_symbol(self, syms):
        best = syms[0]
        best_cap = -1.0

        for sym in syms:
            cap_val = -1.0
            sec = (
                self.securities[sym]
                if self.securities.contains_key(sym) else None
            )
            if sec is not None and sec.fundamentals is not None:
                cap = sec.fundamentals.market_cap
                if cap and cap > 0:
                    cap_val = float(cap)

            if cap_val > best_cap:
                best_cap = cap_val
                best = sym

        return best

    def _ensure_long_trail_state(self, sym, target_w):
        if not self.securities.contains_key(sym):
            return
        px = float(self.securities[sym].price)
        if px <= 0:
            return
        st = self._long_trail.get(sym)
        if st is None:
            self._long_trail[sym] = {
                "high": px, "stage": 0, "target_w": float(target_w),
            }
        else:
            st["target_w"] = float(target_w)

    def allocate_top(self, total_weight, ml_bullish=False):
        syms = list(self._top_set)
        if not syms:
            return

        tw = float(total_weight)
        if tw <= 0:
            for sym in syms:
                if (
                    self.portfolio[sym].invested
                    and self.portfolio[sym].quantity > 0
                ):
                    self.liquidate(sym)
                self._long_trail.pop(sym, None)
            return

        n = len(syms)
        base = tw / float(n)
        weights = np.array([base] * n, dtype=float)

        if ml_bullish and self.ml_tilt > 0 and n >= 2:
            ow = self._pick_overweight_symbol(syms)
            i_ow = syms.index(ow)
            extra = base * float(self.ml_tilt)
            weights[i_ow] += extra
            sub = extra / float(n - 1)
            for i in range(n):
                if i != i_ow:
                    weights[i] -= sub

        weights = self._cap_and_renormalize(
            weights, tw, self.top_weight_min, self.top_weight_max,
        )

        for i, sym in enumerate(syms):
            w = float(weights[i])
            self._safe_set_holdings(sym, w)
            self._ensure_long_trail_state(sym, w)

        if self.portfolio[self.spy].invested:
            self.liquidate(self.spy)

    def liquidate_non_top_longs_only(self):
        for kvp in self.portfolio:
            sym = kvp.key
            if sym.security_type != SecurityType.EQUITY:
                continue
            if sym in (self.spy, self.gld):
                continue
            holding = kvp.value
            if (
                holding.invested and holding.quantity > 0
                and sym not in self._top_set
            ):
                self.liquidate(sym)
                self._long_trail.pop(sym, None)

    def get_features(self, vix_closes, spy_closes):
        if len(vix_closes) < 50 or len(spy_closes) < 200:
            return None

        current_vix = vix_closes[-1]
        vix_sma20 = np.mean(vix_closes[-20:])
        vix_sma50 = np.mean(vix_closes[-50:])
        vix_std = np.std(vix_closes[-20:])
        vix_zscore = (
            (current_vix - vix_sma20) / vix_std if vix_std > 0 else 0.0
        )
        vix_percentile = (
            float(np.sum(vix_closes < current_vix))
            / float(len(vix_closes))
        )

        spy_current = spy_closes[-1]
        spy_sma50 = np.mean(spy_closes[-50:])
        spy_sma200 = np.mean(spy_closes[-200:])
        spy_5d_ret = spy_closes[-1] / spy_closes[-5] - 1
        spy_10d_ret = spy_closes[-1] / spy_closes[-10] - 1
        spy_20d_ret = spy_closes[-1] / spy_closes[-20] - 1
        spy_vol = np.std(
            np.diff(spy_closes[-21:]) / spy_closes[-21:-1],
        )

        return [
            float(current_vix),
            float(vix_zscore),
            float(vix_percentile),
            float(current_vix / vix_sma20) if vix_sma20 != 0 else 1.0,
            float(current_vix / vix_sma50) if vix_sma50 != 0 else 1.0,
            float(spy_5d_ret),
            float(spy_10d_ret),
            float(spy_20d_ret),
            float(spy_current / spy_sma50) if spy_sma50 != 0 else 1.0,
            float(spy_current / spy_sma200) if spy_sma200 != 0 else 1.0,
            float(spy_vol * np.sqrt(252)),
        ]

    def train_model(self):
        if self.is_warming_up:
            return

        vix_hist = self.history([self.vix], 800, Resolution.DAILY)
        spy_hist = self.history([self.spy], 800, Resolution.DAILY)
        if vix_hist.empty or spy_hist.empty:
            return

        try:
            vix_closes = vix_hist.loc[self.vix]["close"].values
            spy_closes = spy_hist.loc[self.spy]["close"].values
        except Exception:
            return

        if (
            len(vix_closes) < self.min_training
            or len(spy_closes) < self.min_training
        ):
            return

        x_data, y_data = [], []
        for i in range(200, len(spy_closes) - 21):
            feats = self.get_features(vix_closes[:i], spy_closes[:i])
            if feats is None:
                continue
            label = 1 if spy_closes[i + 21] / spy_closes[i] > 0.02 else 0
            x_data.append(feats)
            y_data.append(label)

        if len(x_data) < 100:
            return

        x_data = np.array(x_data)
        y_data = np.array(y_data)

        self.scaler.fit(x_data)
        xs = self.scaler.transform(x_data)
        self.model.fit(xs, y_data)
        self.trained = True

    class CBOE(PythonData):
        def get_source(self, config, date, is_live):
            return SubscriptionDataSource(
                "https://cdn.cboe.com/api/global/us_indices/daily_prices/VIX_History.csv",
                SubscriptionTransportMedium.REMOTE_FILE,
            )

        def reader(self, config, line, date, is_live):
            if not (line.strip() and line[0].isdigit()):
                return None

            data = line.split(',')
            try:
                bar = VolatilityHarvestMLLongShort.CBOE()
                bar.symbol = config.symbol
                bar.time = datetime.strptime(data[0], "%m/%d/%Y")
                bar.value = float(data[4])
                bar["close"] = float(data[4])
                bar["open"] = float(data[1])
                bar["high"] = float(data[2])
                bar["low"] = float(data[3])
                return bar
            except Exception:
                return None

    def check_signal_long(self):
        if self.is_warming_up:
            return

        self.liquidate_non_top_longs_only()

        vix_hist = self.history([self.vix], 100, Resolution.DAILY)
        spy_hist = self.history([self.spy], 200, Resolution.DAILY)
        if vix_hist.empty or spy_hist.empty:
            return

        try:
            vix_closes = vix_hist.loc[self.vix]["close"].values
            spy_closes = spy_hist.loc[self.spy]["close"].values
        except Exception:
            return

        if len(vix_closes) < 50 or len(spy_closes) < 200:
            return

        current_vix = float(vix_closes[-1])
        vix_sma = float(np.mean(vix_closes[-20:]))
        vix_p80 = float(np.percentile(vix_closes, 80))

        spy_current = float(spy_closes[-1])
        spy_sma50 = float(np.mean(spy_closes[-50:]))
        spy_sma200 = float(np.mean(spy_closes[-200:]))
        spy_5d_ret = float(spy_closes[-1] / spy_closes[-5] - 1)

        ml_bullish = False
        if self.trained:
            feats = self.get_features(vix_closes, spy_closes)
            if feats is not None:
                x_input = self.scaler.transform([feats])
                prob_array = self.model.predict_proba(x_input)[0]
                if len(prob_array) == 2:
                    prob = float(prob_array[1])
                else:
                    prob = (
                        0.7 if self.model.predict(x_input)[0] == 1 else 0.5
                    )
                ml_bullish = prob > 0.6

        lg = float(self.long_gross)

        if current_vix > vix_p80 and spy_5d_ret < -0.03:
            weight = 1.0 if ml_bullish else 0.85
            eq_w = lg * weight
            self.allocate_top(eq_w, ml_bullish=ml_bullish)
            self._safe_set_holdings(self.gld, lg * (1.0 - weight))
            return

        if current_vix < 13 and spy_current > spy_sma50 * 1.05:
            self.allocate_top(lg * 0.40, ml_bullish=ml_bullish)
            self._safe_set_holdings(self.gld, lg * 0.40)
            return

        if 20 < current_vix < vix_sma:
            weight = 0.85 if ml_bullish else 0.70
            eq_w = lg * weight
            self.allocate_top(eq_w, ml_bullish=ml_bullish)
            self._safe_set_holdings(self.gld, lg * (1.0 - weight))
            return

        if current_vix > vix_sma * 1.2:
            self.allocate_top(0.0, ml_bullish=ml_bullish)
            self._safe_set_holdings(self.gld, lg * 0.50)
            return

        if spy_current > spy_sma200:
            base = 0.90 if ml_bullish else 0.70
            self.allocate_top(lg * base, ml_bullish=ml_bullish)
            self._safe_set_holdings(self.gld, lg * (1.0 - base))
        else:
            self.allocate_top(lg * 0.30, ml_bullish=ml_bullish)
            self._safe_set_holdings(self.gld, lg * 0.50)

    def risk_check_long(self):
        if self.is_warming_up:
            return

        for sym in list(self._long_trail.keys()):
            if (
                not self.securities.contains_key(sym)
                or not self.portfolio[sym].invested
                or self.portfolio[sym].quantity <= 0
            ):
                self._long_trail.pop(sym, None)
                continue

            if sym not in self._top_set:
                continue

            px = float(self.securities[sym].price)
            if px <= 0:
                continue

            st = self._long_trail.get(sym)
            if st is None:
                continue

            if px > float(st["high"]):
                st["high"] = px

            high = float(st["high"])
            if high <= 0:
                continue

            dd = (high - px) / high
            stage = int(st["stage"])
            full_target_w = float(st["target_w"])

            if stage == 0 and dd >= self.long_trail_1:
                new_w = full_target_w * (2.0 / 3.0)
                self._safe_set_holdings(sym, new_w)
                st["stage"] = 1
                st["high"] = px
            elif stage == 1 and dd >= self.long_trail_2:
                new_w = full_target_w * (1.0 / 3.0)
                self._safe_set_holdings(sym, new_w)
                st["stage"] = 2
                st["high"] = px
            elif stage == 2 and dd >= self.long_trail_3:
                self.liquidate(sym)
                self._long_trail.pop(sym, None)

    def _atr(self, df, n):
        w = df.shape[0]
        if w < n + 1:
            return None
        s = 0.0
        for i in range(1, n + 1):
            hi = float(df["high"].iloc[w - i])
            lo = float(df["low"].iloc[w - i])
            cl = float(df["close"].iloc[w - i])
            s += max(hi - lo, abs(hi - cl), abs(lo - cl))
        return s / float(n)

    def _hurst_like(self, df, n, bump):
        atr = self._atr(df, n)
        if atr is None or atr <= 0:
            return None

        high_max = float(df["high"].tail(n).max())
        low_min = float(df["low"].tail(n).min())
        span = high_max - low_min
        if span <= 0:
            return None

        h = (np.log(span) - np.log(atr)) / np.log(float(n))
        if h > 0.45:
            h += bump
        elif h < 0.45:
            h -= bump
        return float(h)

    def _compute_score_and_filters(self, symbol):
        df = self.history(symbol, self.lookback_bars, Resolution.DAILY)
        if df is None or df.empty:
            return None

        if isinstance(df.index, pd.MultiIndex):
            df = df.xs(symbol)

        if len(df) < max(self.n_list) + 6:
            return None

        hvals = []
        for n in self.n_list:
            hv = self._hurst_like(df, n, 0.01 + 0.0002 * n)
            if hv is not None:
                hvals.append(hv)

        if len(hvals) < 4:
            return None

        havg = float(sum(hvals) / float(len(hvals)))
        agree = int(sum(1 for x in hvals if x > 0.6))

        close_now = float(df["close"].iloc[-1])
        sma = float(df["close"].tail(self.sma_len).mean())

        atr20 = self._atr(df, 20)
        if atr20 is None or atr20 <= 0:
            return None

        close_5 = float(df["close"].iloc[-5])

        ext_ok = (close_now - sma) > self.ext_k * atr20
        mom_ok = (close_now - close_5) > self.mom_k * atr20
        score = havg + 0.02 * max(0, agree - 3)

        return (
            float(score), bool(ext_ok), bool(mom_ok),
            close_now, float(atr20),
        )

    def rebalance_short(self):
        if self.is_warming_up or not self._active:
            return

        scored = []
        for sym in self._active:
            if sym == self.spy:
                continue
            if (
                not self.securities.contains_key(sym)
                or not self.securities[sym].has_data
            ):
                continue

            out = self._compute_score_and_filters(sym)
            if out is None:
                continue

            score, ext_ok, mom_ok, close_now, atr20 = out
            if score >= self.score_threshold and ext_ok and mom_ok:
                scored.append((score, sym, close_now, atr20))

        scored.sort(reverse=True, key=lambda x: x[0])
        picked = scored[:self.top_n]
        selected = [sym for _, sym, _, _ in picked]

        for kvp in self.portfolio:
            sym = kvp.key
            if sym in (self.spy, self.gld):
                continue
            holding = kvp.value
            if (
                holding.invested and holding.quantity < 0
                and sym not in selected
            ):
                self.liquidate(sym)
                self._entry.pop(sym, None)

        if selected:
            w = -abs(self.short_gross) / float(len(selected))
            for _, sym, close_now, atr20 in picked:
                self._safe_set_holdings(sym, w)
                if sym not in self._entry:
                    self._entry[sym] = {
                        "entry_price": close_now, "entry_atr": atr20,
                    }

    def risk_check_short(self):
        if self.is_warming_up:
            return

        exits = []
        for sym, info in list(self._entry.items()):
            if (
                not self.securities.contains_key(sym)
                or not self.portfolio[sym].invested
            ):
                self._entry.pop(sym, None)
                continue

            if self.portfolio[sym].quantity >= 0:
                self._entry.pop(sym, None)
                continue

            price = float(self.securities[sym].price)
            if price <= 0:
                continue

            entry = float(info["entry_price"])
            atr = float(info["entry_atr"])
            if atr <= 0:
                continue

            if (price - entry) > self.stop_atr * atr:
                exits.append(sym)

        for sym in exits:
            self.liquidate(sym)
            self._entry.pop(sym, None)
