#region imports
from AlgorithmImports import *
from datetime import datetime
import numpy as np
import pandas as pd
from sklearn.ensemble import RandomForestClassifier
from sklearn.preprocessing import StandardScaler
#endregion
# https://www.quantconnect.com/strategies/238
# Long Short Harvest by Grant Forman
# OOS 1Y Sharpe 3.39, 5Y CAGR 57.94%, 5Y Drawdown 15.20%, 76% Win Rate
# Long-short equity with ML overlay, Hurst-style regime detection, ATR-scaled filters
# Source: QC Strategy Library #238, cloned 2026-04-04, QC Project ID: 29687399


class VolatilityHarvestML_LongShort(QCAlgorithm):

    def Initialize(self):
        self.SetStartDate(2012, 1, 1)
        self.SetCash(100000)
        self.SetBrokerageModel(BrokerageName.InteractiveBrokersBrokerage, AccountType.Margin)

        self.Settings.FreePortfolioValuePercentage = 0.025

        self.spy = self.AddEquity("SPY", Resolution.Daily).Symbol
        self.SetBenchmark(self.spy)

        self.gld = self.AddEquity("GLD", Resolution.Daily).Symbol

        self.vix = self.AddData(self.CBOE, "VIX", Resolution.Daily).Symbol

        self.long_gross = float(self.GetParameter("long_gross") or 0.9)
        self.short_gross = float(self.GetParameter("short_gross") or 0.6)

        self.UniverseSettings.Resolution = Resolution.Daily
        self._top_set = set()
        self._last_top_month = -1

        self.ml_tilt = float(self.GetParameter("ml_tilt") or 0.25)
        self.top_weight_max = float(self.GetParameter("top_weight_max") or 0.35)
        self.top_weight_min = float(self.GetParameter("top_weight_min") or 0.0)

        self.coarse_count = int(self.GetParameter("coarse_count") or 2000)
        self.max_universe = int(self.GetParameter("max_universe") or 150)
        self.top_n = int(self.GetParameter("top_n") or 1)

        self.min_ipo_days = int(self.GetParameter("min_ipo_days") or 365)

        self.lookback_bars = int(self.GetParameter("lookback_bars") or 260)
        self.n_list = [10, 10, 40, 60, 90, 100]

        self.sma_len = int(self.GetParameter("sma_len") or 195)
        self.ext_k = float(self.GetParameter("ext_k") or 2.0)
        self.mom_k = float(self.GetParameter("mom_k") or 1.75)
        self.score_threshold = float(self.GetParameter("score_threshold") or 0.85)
        self.stop_atr = float(self.GetParameter("stop_atr") or 2.0)

        self._active = []
        self._entry = {}

        self.long_trail_1 = float(self.GetParameter("long_trail_1") or 0.095)
        self.long_trail_2 = float(self.GetParameter("long_trail_2") or 0.07)
        self.long_trail_3 = float(self.GetParameter("long_trail_3") or 0.0485)

        self._long_trail = {}

        self.model = RandomForestClassifier(n_estimators=100, max_depth=5, random_state=42)
        self.scaler = StandardScaler()
        self.trained = False
        self.min_training = 504

        self.AddUniverse(self.CoarseSelection, self.FineSelection)

        self.Schedule.On(
            self.DateRules.EveryDay("SPY"),
            self.TimeRules.AfterMarketOpen("SPY", 30),
            self.CheckSignal_Long
        )

        self.Schedule.On(
            self.DateRules.MonthStart("SPY"),
            self.TimeRules.AfterMarketOpen("SPY", 60),
            self.TrainModel
        )

        self.Schedule.On(
            self.DateRules.Every(DayOfWeek.Monday),
            self.TimeRules.AfterMarketOpen(self.spy, 30),
            self.Rebalance_Short
        )

        self.Schedule.On(
            self.DateRules.EveryDay(self.spy),
            self.TimeRules.AfterMarketOpen(self.spy, 160),
            self.RiskCheck_Short
        )

        self.Schedule.On(
            self.DateRules.EveryDay(self.spy),
            self.TimeRules.AfterMarketOpen(self.spy, 90),
            self.RiskCheck_Long
        )

        self.SetWarmUp(252)

    def _safe_set_holdings(self, symbol, target_weight):
        pv = float(self.Portfolio.TotalPortfolioValue)
        if pv <= 0:
            return
        mr = float(self.Portfolio.MarginRemaining)
        max_abs = max(0.0, mr / pv)
        w = float(np.clip(float(target_weight), -max_abs, max_abs))
        self.SetHoldings(symbol, w)

    def CoarseSelection(self, coarse):
        filtered = [
            c for c in coarse
            if c.HasFundamentalData
            and c.Price is not None and c.Price > 5
            and c.DollarVolume is not None and c.DollarVolume > 2e7
        ]
        filtered.sort(key=lambda c: c.DollarVolume, reverse=True)
        return [c.Symbol for c in filtered[:self.coarse_count]]

    def FineSelection(self, fine):
        today = self.Time.date()

        if self.Time.month != self._last_top_month:
            fine_mc = [f for f in fine if f.MarketCap and f.MarketCap > 0]
            fine_mc.sort(key=lambda f: f.MarketCap, reverse=True)
            self._top_set = set([f.Symbol for f in fine_mc[:4]])
            self._last_top_month = self.Time.month

        kept = []
        for f in fine:
            if not f.MarketCap or f.MarketCap < 1_000_000_000:
                continue

            sr = f.SecurityReference
            if sr is None or sr.IPODate is None:
                continue

            days_since_ipo = (today - sr.IPODate.date()).days
            if days_since_ipo < self.min_ipo_days:
                continue

            kept.append(f)

        kept.sort(key=lambda f: f.DollarVolume, reverse=True)
        short_symbols = [f.Symbol for f in kept[:self.max_universe]]
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
                adjustable = [i for i in range(n) if (wmax <= 0 or w[i] < wmax - 1e-12)]
            else:
                adjustable = [i for i in range(n) if (wmin <= 0 or w[i] > wmin + 1e-12)]

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
            sec = self.Securities[sym] if self.Securities.ContainsKey(sym) else None
            if sec is not None and sec.Fundamentals is not None:
                cap = sec.Fundamentals.MarketCap
                if cap and cap > 0:
                    cap_val = float(cap)

            if cap_val > best_cap:
                best_cap = cap_val
                best = sym

        return best

    def _ensure_long_trail_state(self, sym, target_w):
        if not self.Securities.ContainsKey(sym):
            return
        px = float(self.Securities[sym].Price)
        if px <= 0:
            return
        st = self._long_trail.get(sym)
        if st is None:
            self._long_trail[sym] = {"high": px, "stage": 0, "target_w": float(target_w)}
        else:
            st["target_w"] = float(target_w)

    def AllocateTop(self, total_weight, ml_bullish=False):
        syms = list(self._top_set)
        if not syms:
            return

        TW = float(total_weight)
        if TW <= 0:
            for sym in syms:
                if self.Portfolio[sym].Invested and self.Portfolio[sym].Quantity > 0:
                    self.Liquidate(sym)
                self._long_trail.pop(sym, None)
            return

        n = len(syms)
        base = TW / float(n)
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

        weights = self._cap_and_renormalize(weights, TW, self.top_weight_min, self.top_weight_max)

        for i, sym in enumerate(syms):
            w = float(weights[i])
            self._safe_set_holdings(sym, w)
            self._ensure_long_trail_state(sym, w)

        if self.Portfolio[self.spy].Invested:
            self.Liquidate(self.spy)

    def LiquidateNonTopLongsOnly(self):
        for kvp in self.Portfolio:
            sym = kvp.Key
            if sym.SecurityType != SecurityType.Equity:
                continue
            if sym in (self.spy, self.gld):
                continue
            holding = kvp.Value
            if holding.Invested and holding.Quantity > 0 and sym not in self._top_set:
                self.Liquidate(sym)
                self._long_trail.pop(sym, None)

    def GetFeatures(self, vix_closes, spy_closes):
        if len(vix_closes) < 50 or len(spy_closes) < 200:
            return None

        current_vix = vix_closes[-1]
        vix_sma20 = np.mean(vix_closes[-20:])
        vix_sma50 = np.mean(vix_closes[-50:])
        vix_std = np.std(vix_closes[-20:])
        vix_zscore = (current_vix - vix_sma20) / vix_std if vix_std > 0 else 0.0
        vix_percentile = float(np.sum(vix_closes < current_vix)) / float(len(vix_closes))

        spy_current = spy_closes[-1]
        spy_sma50 = np.mean(spy_closes[-50:])
        spy_sma200 = np.mean(spy_closes[-200:])
        spy_5d_ret = spy_closes[-1] / spy_closes[-5] - 1
        spy_10d_ret = spy_closes[-1] / spy_closes[-10] - 1
        spy_20d_ret = spy_closes[-1] / spy_closes[-20] - 1
        spy_vol = np.std(np.diff(spy_closes[-21:]) / spy_closes[-21:-1])

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

    def TrainModel(self):
        if self.IsWarmingUp:
            return

        vix_hist = self.History([self.vix], 800, Resolution.Daily)
        spy_hist = self.History([self.spy], 800, Resolution.Daily)
        if vix_hist.empty or spy_hist.empty:
            return

        try:
            vix_closes = vix_hist.loc[self.vix]["close"].values
            spy_closes = spy_hist.loc[self.spy]["close"].values
        except:
            return

        if len(vix_closes) < self.min_training or len(spy_closes) < self.min_training:
            return

        X, y = [], []
        for i in range(200, len(spy_closes) - 21):
            feats = self.GetFeatures(vix_closes[:i], spy_closes[:i])
            if feats is None:
                continue
            label = 1 if spy_closes[i + 21] / spy_closes[i] > 1.02 else 0
            X.append(feats)
            y.append(label)

        if len(X) < 100:
            return

        X = np.array(X)
        y = np.array(y)

        self.scaler.fit(X)
        Xs = self.scaler.transform(X)
        self.model.fit(Xs, y)
        self.trained = True

    class CBOE(PythonData):
        def GetSource(self, config, date, isLive):
            return SubscriptionDataSource(
                "https://cdn.cboe.com/api/global/us_indices/daily_prices/VIX_History.csv",
                SubscriptionTransportMedium.RemoteFile
            )

        def Reader(self, config, line, date, isLive):
            if not (line.strip() and line[0].isdigit()):
                return None

            data = line.split(',')
            try:
                bar = VolatilityHarvestML_LongShort.CBOE()
                bar.Symbol = config.Symbol
                bar.Time = datetime.strptime(data[0], "%m/%d/%Y")
                bar.Value = float(data[4])
                bar["close"] = float(data[4])
                bar["open"] = float(data[1])
                bar["high"] = float(data[2])
                bar["low"] = float(data[3])
                return bar
            except:
                return None

    def CheckSignal_Long(self):
        if self.IsWarmingUp:
            return

        self.LiquidateNonTopLongsOnly()

        vix_hist = self.History([self.vix], 100, Resolution.Daily)
        spy_hist = self.History([self.spy], 200, Resolution.Daily)
        if vix_hist.empty or spy_hist.empty:
            return

        try:
            vix_closes = vix_hist.loc[self.vix]["close"].values
            spy_closes = spy_hist.loc[self.spy]["close"].values
        except:
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
            feats = self.GetFeatures(vix_closes, spy_closes)
            if feats is not None:
                X = self.scaler.transform([feats])
                prob_array = self.model.predict_proba(X)[0]
                if len(prob_array) == 2:
                    prob = float(prob_array[1])
                else:
                    prob = 0.7 if self.model.predict(X)[0] == 1 else 0.5
                ml_bullish = prob > 0.6

        LG = float(self.long_gross)

        if current_vix > vix_p80 and spy_5d_ret < -0.03:
            weight = 1.0 if ml_bullish else 0.85
            eq_w = LG * weight
            self.AllocateTop(eq_w, ml_bullish=ml_bullish)
            self._safe_set_holdings(self.gld, LG * (1.0 - weight))
            return

        if current_vix < 13 and spy_current > spy_sma50 * 1.05:
            self.AllocateTop(LG * 0.40, ml_bullish=ml_bullish)
            self._safe_set_holdings(self.gld, LG * 0.40)
            return

        if 20 < current_vix < vix_sma:
            weight = 0.85 if ml_bullish else 0.70
            eq_w = LG * weight
            self.AllocateTop(eq_w, ml_bullish=ml_bullish)
            self._safe_set_holdings(self.gld, LG * (1.0 - weight))
            return

        if current_vix > vix_sma * 1.2:
            self.AllocateTop(0.0, ml_bullish=ml_bullish)
            self._safe_set_holdings(self.gld, LG * 0.50)
            return

        if spy_current > spy_sma200:
            base = 0.90 if ml_bullish else 0.70
            self.AllocateTop(LG * base, ml_bullish=ml_bullish)
            self._safe_set_holdings(self.gld, LG * (1.0 - base))
        else:
            self.AllocateTop(LG * 0.30, ml_bullish=ml_bullish)
            self._safe_set_holdings(self.gld, LG * 0.50)

    def RiskCheck_Long(self):
        if self.IsWarmingUp:
            return

        for sym in list(self._long_trail.keys()):
            if not self.Securities.ContainsKey(sym) or not self.Portfolio[sym].Invested or self.Portfolio[sym].Quantity <= 0:
                self._long_trail.pop(sym, None)
                continue

            if sym not in self._top_set:
                continue

            px = float(self.Securities[sym].Price)
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
                self.Liquidate(sym)
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
        df = self.History(symbol, self.lookback_bars, Resolution.Daily)
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

        return float(score), bool(ext_ok), bool(mom_ok), close_now, float(atr20)

    def Rebalance_Short(self):
        if self.IsWarmingUp or not self._active:
            return

        scored = []
        for sym in self._active:
            if sym == self.spy:
                continue
            if not self.Securities.ContainsKey(sym) or not self.Securities[sym].HasData:
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

        for kvp in self.Portfolio:
            sym = kvp.Key
            if sym in (self.spy, self.gld):
                continue
            holding = kvp.Value
            if holding.Invested and holding.Quantity < 0 and sym not in selected:
                self.Liquidate(sym)
                self._entry.pop(sym, None)

        if selected:
            w = -abs(self.short_gross) / float(len(selected))
            for _, sym, close_now, atr20 in picked:
                self._safe_set_holdings(sym, w)
                if sym not in self._entry:
                    self._entry[sym] = {"entry_price": close_now, "entry_atr": atr20}

    def RiskCheck_Short(self):
        if self.IsWarmingUp:
            return

        exits = []
        for sym, info in list(self._entry.items()):
            if not self.Securities.ContainsKey(sym) or not self.Portfolio[sym].Invested:
                self._entry.pop(sym, None)
                continue

            if self.Portfolio[sym].Quantity >= 0:
                self._entry.pop(sym, None)
                continue

            price = float(self.Securities[sym].Price)
            if price <= 0:
                continue

            entry = float(info["entry_price"])
            atr = float(info["entry_atr"])
            if atr <= 0:
                continue

            if (price - entry) > self.stop_atr * atr:
                exits.append(sym)

        for sym in exits:
            self.Liquidate(sym)
            self._entry.pop(sym, None)
