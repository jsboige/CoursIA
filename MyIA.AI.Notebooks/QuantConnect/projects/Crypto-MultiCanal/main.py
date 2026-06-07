# region imports
from AlgorithmImports import *
import numpy as np
import pandas as pd
import math
import traceback
from datetime import timezone


# --- Inlined from channel_helpers.py for QC Cloud compatibility ---


def _get_line_params_time(p1_time_num, p1_price, p2_time_num, p2_price):
    """Get slope (m) and intercept (c) for a line through two time-price points."""
    time_diff = p2_time_num - p1_time_num
    if abs(time_diff) < 1e-9:
        return float('inf'), float(p1_time_num)
    m = (p2_price - p1_price) / time_diff
    c = p1_price - m * p1_time_num
    return m, c


def _find_envelope_line(pivots_df, is_resistance, recency_alpha=0.0,
                        max_violation_pct=0.0, check_all_pivots=None):
    """Find the tightest envelope line through any pair of same-type pivots.

    Algorithm:
    1. Try ALL pairs of same-type pivots as anchors
    2. Check containment against check_all_pivots (if provided) or same-type pivots
    3. Allow up to max_violation_pct fraction of check points to violate
    4. Score = (violations, avg_margin) -- minimize violations first, then tightness
    """
    n_pivots = len(pivots_df)
    if n_pivots < 2:
        return None, None

    pivots_vals = pivots_df[['time_numeric', 'price']].values

    if check_all_pivots is not None:
        check_vals = check_all_pivots
    else:
        check_vals = pivots_vals
    n_check = len(check_vals)
    max_violations = max(1, int(n_check * max_violation_pct)) if max_violation_pct > 0 else 0

    best = None
    best_violations = n_check + 1
    best_margin = float('inf')

    for i in range(n_pivots):
        for j in range(i + 1, n_pivots):
            t1, p1 = pivots_vals[i]
            t2, p2 = pivots_vals[j]
            if abs(t2 - t1) < 1e-9:
                continue

            m, c = _get_line_params_time(t1, p1, t2, p2)
            if m == float('inf'):
                continue

            violations = 0
            total_margin = 0.0
            n_checked = 0
            valid = True
            for k in range(n_check):
                pk_t, pk_p = check_vals[k]
                if abs(pk_t - t1) < 1e-9 or abs(pk_t - t2) < 1e-9:
                    continue
                line_val = m * pk_t + c
                if is_resistance:
                    margin = line_val - pk_p
                    if margin < -1e-9:
                        violations += 1
                        if violations > max_violations:
                            valid = False
                            break
                else:
                    margin = pk_p - line_val
                    if margin < -1e-9:
                        violations += 1
                        if violations > max_violations:
                            valid = False
                            break
                total_margin += margin
                n_checked += 1

            if not valid:
                continue

            avg_margin = total_margin / n_checked if n_checked > 0 else float('inf')

            if (violations < best_violations or
                    (violations == best_violations and avg_margin < best_margin)):
                best_violations = violations
                best_margin = avg_margin
                best = (i, j)

    if best is None:
        return None, None
    return pivots_df.iloc[best[0]], pivots_df.iloc[best[1]]


def _classic_chart_zigzag(df, threshold_percent=0.05):
    """Classic ZigZag indicator: finds alternating high/low pivots."""
    if len(df) < 2:
        return []

    pivots = []
    first = df.iloc[0]
    last_price = float(first['close'])
    last_time = first['time']
    second = df.iloc[1]
    direction_up = float(second['close']) > last_price
    extreme_price = last_price
    extreme_time = last_time
    last_sign = 1 if direction_up else -1
    pivots.append({'time': last_time, 'price': last_price, 'type': last_sign})

    for i in range(1, len(df)):
        row = df.iloc[i]
        price = float(row['close'])
        time = row['time']

        if direction_up:
            if price > extreme_price:
                extreme_price = price
                extreme_time = time
            else:
                retrace = 1.0 - (price / extreme_price) if extreme_price != 0 else 0
                if retrace >= threshold_percent:
                    pivots.append({'time': extreme_time, 'price': extreme_price, 'type': -1})
                    direction_up = False
                    extreme_price = price
                    extreme_time = time
        else:
            if price < extreme_price:
                extreme_price = price
                extreme_time = time
            else:
                rally = (price / extreme_price) - 1.0 if extreme_price != 0 else float('inf')
                if rally >= threshold_percent:
                    pivots.append({'time': extreme_time, 'price': extreme_price, 'type': 1})
                    direction_up = True
                    extreme_price = price
                    extreme_time = time

    # Ensure alternation
    if len(pivots) > 1 and pivots[-1]['type'] == pivots[-2]['type']:
        if pivots[-1]['type'] == 1:
            if pivots[-1]['price'] < pivots[-2]['price']:
                pivots.pop(-2)
            else:
                pivots.pop(-1)
        else:
            if pivots[-1]['price'] > pivots[-2]['price']:
                pivots.pop(-2)
            else:
                pivots.pop(-1)

    if pivots and pivots[-1]['type'] != (-1 if direction_up else 1):
        pivots.append({'time': extreme_time, 'price': extreme_price,
                       'type': (-1 if direction_up else 1)})

    return pivots


def _get_channel_value_at_time(channel_pivots, time_numeric):
    """Get channel line value at a specific time."""
    if not channel_pivots or channel_pivots[0] is None or channel_pivots[1] is None:
        return float('nan')
    p1, p2 = channel_pivots[0], channel_pivots[1]
    if pd.isna(p1.get('time_numeric')) or pd.isna(p2.get('time_numeric')):
        return float('nan')
    m, c = _get_line_params_time(p1['time_numeric'], p1['price'],
                                  p2['time_numeric'], p2['price'])
    if m == float('inf'):
        return float('nan')
    return m * time_numeric + c


# Alias for readability in algorithm body (match original import names)
get_line_params_time = _get_line_params_time
find_envelope_line = _find_envelope_line
classic_chart_zigzag = _classic_chart_zigzag
get_channel_value_at_time = _get_channel_value_at_time
# endregion


class CryptoMultiChannelAlgorithm(QCAlgorithm):
    """Multi-Channel ZigZag strategy on BTC.

    3 nested channels (macro/meso/micro) built from ZigZag pivots.
    - Macro: overall trend (all pivots, recency-weighted envelope)
    - Meso: from macro's 3rd chronological anchor onward
    - Micro: from meso's 3rd chronological anchor onward

    Trade on the tightest available channel (micro > meso > macro).
    Signals: bounce off support + breakout above resistance (long only).
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)  # Extended from 2020: +3 years for robustness validation (includes 2017 bull & 2018 crash)
        self.set_account_currency("USDT")
        self.set_cash(10000)
        self.btc = self.add_crypto("BTCUSDT", Resolution.DAILY, Market.BINANCE).symbol
        self.set_benchmark(self.btc)
        # Configurable brokerage for fee sweep (default: binance with real fees)
        self._brokerage_mode = self.get_parameter("brokerage", "binance")
        if self._brokerage_mode != "none":
            self.set_brokerage_model(BrokerageName.BINANCE, AccountType.CASH)

        # --- Strategy parameters (v17: v15 base + trail 3%) ---
        self.zigzag_threshold = 0.05
        self.lookback_bars = 500
        self.recency_alpha = 0.0
        self.macro_meso_violation_pct = 0.2
        self.micro_violation_pct = 0.1
        self.bounce_entry_offset = 0.03
        self.breakout_confirm = 0.005
        self.sl_pct = 0.06
        self.tp_rr = 2.5
        self.risk_pct = 0.03
        self.trail_breakeven_pct = 0.03  # v17: trail earlier (was 0.04)

        # --- Trend filter ---
        self.sma_period = 50

        # --- State ---
        self.channels = {
            "macro": {"resistance": (None, None), "support": (None, None)},
            "meso": {"resistance": (None, None), "support": (None, None)},
            "micro": {"resistance": (None, None), "support": (None, None)},
        }
        self._day_count = 0
        self._pending_entry = None
        self._active_sl = None
        self._entry_price = None

        self.set_warm_up(TimeSpan.from_days(60))

    def on_data(self, data):
        if self.is_warming_up:
            return
        if not data.contains_key(self.btc) or data[self.btc] is None:
            return

        self._day_count += 1
        self._recalculate_channels()

        # Manual SL check (Binance Cash can't do SL + TP simultaneously)
        if self.portfolio[self.btc].invested and self._active_sl:
            price = float(data[self.btc].close)
            # Trail SL to breakeven after sufficient gain
            entry = self._active_sl.get('entry')
            if entry and price >= entry * (1 + self.trail_breakeven_pct):
                new_sl = max(self._active_sl['price'], entry * 1.005)
                if new_sl > self._active_sl['price']:
                    self._active_sl['price'] = new_sl
            if price <= self._active_sl['price']:
                self.debug(f"SL HIT: {self._active_sl['tag']} | price={price:.0f} | "
                           f"sl={self._active_sl['price']:.0f}")
                open_orders = self.transactions.get_open_order_tickets(
                    lambda t: t.symbol == self.btc
                )
                for ticket in open_orders:
                    ticket.cancel("SL hit")
                qty = self.portfolio[self.btc].quantity
                if qty > 0:
                    self.market_order(self.btc, -qty, tag=f"{self._active_sl['tag']} SL")
                self._active_sl = None
                self._entry_price = None

        if not self.portfolio[self.btc].invested:
            self._active_sl = None
            self._check_entry(data)

    def _recalculate_channels(self):
        try:
            history_df = self.history(self.btc, self.lookback_bars, Resolution.DAILY)
            if history_df.empty:
                return

            if isinstance(history_df.index, pd.MultiIndex):
                history_df = history_df.loc[self.btc]

            history_df = history_df.reset_index()
            if 'time' not in history_df.columns:
                for col in history_df.columns:
                    if 'time' in col.lower() or 'date' in col.lower() or col == 'index':
                        history_df = history_df.rename(columns={col: 'time'})
                        break
            if 'time' not in history_df.columns or 'close' not in history_df.columns:
                return

            history_df['time'] = pd.to_datetime(history_df['time'])
            if history_df['time'].dt.tz is None:
                history_df['time'] = history_df['time'].dt.tz_localize('UTC')

            df_zz = history_df[['time', 'close']].copy()
            pivot_list = classic_chart_zigzag(df_zz, self.zigzag_threshold)

            if not pivot_list or len(pivot_list) < 4:
                return

            pivots_df = pd.DataFrame(pivot_list)
            pivots_df['time'] = pd.to_datetime(pivots_df['time'])
            if pivots_df['time'].dt.tz is None:
                pivots_df['time_numeric'] = pivots_df['time'].apply(
                    lambda x: x.replace(tzinfo=timezone.utc).timestamp()
                )
            else:
                pivots_df['time_numeric'] = pivots_df['time'].apply(lambda x: x.timestamp())

            high_df = pivots_df[pivots_df['type'] == -1].copy()
            low_df = pivots_df[pivots_df['type'] == 1].copy()

            if len(high_df) < 2 or len(low_df) < 2:
                return

            # All pivots array for containment checking (like v12 legacy)
            all_pivots_np = pivots_df[['time_numeric', 'price']].values

            # === MACRO: all pivots, relaxed containment ===
            self._fit_channel("macro", high_df, low_df,
                              all_pivots_np, self.macro_meso_violation_pct)

            # === MESO: from macro's 3rd chronological anchor ===
            self._reset_channel("meso")
            self._reset_channel("micro")
            macro_anchors = self._get_anchor_times("macro")
            if len(macro_anchors) >= 3:
                meso_start = macro_anchors[2]
            elif len(macro_anchors) >= 2:
                meso_start = macro_anchors[1]
            else:
                meso_start = pivots_df['time_numeric'].median()

            meso_pivots = pivots_df[pivots_df['time_numeric'] >= meso_start - 1e-9]
            meso_high = meso_pivots[meso_pivots['type'] == -1].copy()
            meso_low = meso_pivots[meso_pivots['type'] == 1].copy()
            meso_all = meso_pivots[['time_numeric', 'price']].values
            if len(meso_high) >= 2 and len(meso_low) >= 2:
                self._fit_channel("meso", meso_high, meso_low,
                                  meso_all, self.macro_meso_violation_pct)

            # === MICRO: from meso's 3rd chronological anchor ===
            meso_anchors = self._get_anchor_times("meso")
            if len(meso_anchors) >= 3:
                micro_start = meso_anchors[2]
            elif len(meso_anchors) >= 2:
                micro_start = meso_anchors[1]
            else:
                micro_start = (meso_start + pivots_df['time_numeric'].iloc[-1]) / 2

            micro_pivots = pivots_df[pivots_df['time_numeric'] >= micro_start - 1e-9]
            micro_high = micro_pivots[micro_pivots['type'] == -1].copy()
            micro_low = micro_pivots[micro_pivots['type'] == 1].copy()
            micro_all = micro_pivots[['time_numeric', 'price']].values
            if len(micro_high) >= 2 and len(micro_low) >= 2:
                self._fit_channel("micro", micro_high, micro_low,
                                  micro_all, self.micro_violation_pct)

            # Diagnostics every 60 days
            if self._day_count % 60 == 1:
                t = self.time.replace(tzinfo=timezone.utc).timestamp()
                price = self.securities[self.btc].price
                for scale in ["macro", "meso", "micro"]:
                    res = self.channels[scale]["resistance"]
                    sup = self.channels[scale]["support"]
                    if res[0] and sup[0]:
                        rv = get_channel_value_at_time(res, t)
                        sv = get_channel_value_at_time(sup, t)
                        self.debug(f"[{scale}] res={rv:.0f} sup={sv:.0f} price={price:.0f}")
                    else:
                        self.debug(f"[{scale}] no channel")

        except Exception:
            self.error(f"Recalc error: {traceback.format_exc()}")

    def _fit_channel(self, scale, high_df, low_df,
                     all_pivots_np=None, max_violation_pct=0.0):
        r1, r2 = find_envelope_line(
            high_df, True, recency_alpha=self.recency_alpha,
            max_violation_pct=max_violation_pct, check_all_pivots=all_pivots_np)
        if r1 is not None and r2 is not None:
            self.channels[scale]["resistance"] = (self._to_dict(r1), self._to_dict(r2))
        else:
            self.channels[scale]["resistance"] = (None, None)

        s1, s2 = find_envelope_line(
            low_df, False, recency_alpha=self.recency_alpha,
            max_violation_pct=max_violation_pct, check_all_pivots=all_pivots_np)
        if s1 is not None and s2 is not None:
            self.channels[scale]["support"] = (self._to_dict(s1), self._to_dict(s2))
        else:
            self.channels[scale]["support"] = (None, None)

    def _reset_channel(self, scale):
        self.channels[scale] = {"resistance": (None, None), "support": (None, None)}

    def _get_anchor_times(self, scale):
        """Extract sorted anchor timestamps from a channel's 4 anchor points."""
        times = []
        ch = self.channels[scale]
        for side in ['resistance', 'support']:
            for p in ch[side]:
                if p is not None and 'time_numeric' in p:
                    times.append(p['time_numeric'])
        times.sort()
        return times

    def _to_dict(self, series):
        if series is None or not isinstance(series, pd.Series):
            return None
        t = series.get('time')
        p = series.get('price')
        tn = series.get('time_numeric')
        if t is None or p is None or tn is None:
            return None
        return {'time': t, 'price': float(p), 'time_numeric': float(tn)}

    def _check_entry(self, data):
        price = float(data[self.btc].close)
        t_num = self.time.replace(tzinfo=timezone.utc).timestamp()

        # SMA trend filter: only long above SMA
        history_sma = self.history(self.btc, self.sma_period, Resolution.DAILY)
        if history_sma.empty:
            return
        if isinstance(history_sma.index, pd.MultiIndex):
            history_sma = history_sma.loc[self.btc]
        sma_val = history_sma['close'].mean()
        if price < sma_val:
            return

        # Check macro trend is not down
        macro_trend = self._get_trend("macro")
        if macro_trend == 'down':
            return

        # Try each channel scale: micro > meso > macro
        # Micro: bounce only (no breakout), requires meso/macro trend confirmation
        # Meso/Macro: bounce + breakout as before
        signal = None
        sl_price = None
        tag = None

        for scale in ["micro", "meso", "macro"]:
            if signal is not None:
                break
            sup_p = self.channels[scale]["support"]
            res_p = self.channels[scale]["resistance"]
            has_sup = sup_p[0] is not None and sup_p[1] is not None
            has_res = res_p[0] is not None and res_p[1] is not None

            if not has_sup and not has_res:
                continue

            # Bounce off support
            if has_sup:
                sup_val = get_channel_value_at_time(sup_p, t_num)
                if not pd.isna(sup_val) and sup_val > 0:
                    if scale == "micro":
                        # Micro: tighter zone, require parent trend up
                        meso_trend = self._get_trend("meso")
                        if meso_trend == 'down':
                            continue
                        if sup_val * 0.98 <= price <= sup_val * 1.02:
                            signal = 1
                            sl_price = price * (1 - self.sl_pct)
                            tag = f"Bounce {scale} Sup"
                    else:
                        if sup_val * 0.97 <= price <= sup_val * (1 + self.bounce_entry_offset):
                            signal = 1
                            sl_price = price * (1 - self.sl_pct)
                            tag = f"Bounce {scale} Sup"

            # Breakout above resistance (not for micro, macro uptrend only)
            if signal is None and scale != "micro" and has_res and macro_trend == 'up':
                res_val = get_channel_value_at_time(res_p, t_num)
                if not pd.isna(res_val) and res_val > 0:
                    if price > res_val * (1 + self.breakout_confirm):
                        signal = 1
                        sl_price = res_val * 0.98
                        tag = f"Breakout {scale} Res"

        if signal is None or sl_price is None or sl_price >= price:
            return

        risk = price - sl_price
        tp_price = price + risk * self.tp_rr

        usdt_available = self.portfolio.cash_book["USDT"].amount
        cash_risk = usdt_available * self.risk_pct
        position_usdt = min((cash_risk / risk) * price, usdt_available * 0.95)
        qty = round(position_usdt / price, 5)

        if qty > 0 and position_usdt > 10:
            self.debug(f"TRADE: {tag} | price={price:.0f} | SL={sl_price:.0f} | "
                       f"TP={tp_price:.0f} | SMA={sma_val:.0f} | qty={qty}")
            self._pending_entry = {
                'qty': qty, 'sl': sl_price, 'tp': tp_price,
                'tag': tag, 'entry': price
            }
            self.market_order(self.btc, qty, tag=f"{tag} Entry")

    def _get_trend(self, scale):
        """Determine trend from channel slope: up, down, or flat."""
        res = self.channels[scale]["resistance"]
        sup = self.channels[scale]["support"]
        if res[0] is None or sup[0] is None:
            return 'flat'
        try:
            m_res, _ = get_line_params_time(
                res[0]['time_numeric'], res[0]['price'],
                res[1]['time_numeric'], res[1]['price']
            )
            m_sup, _ = get_line_params_time(
                sup[0]['time_numeric'], sup[0]['price'],
                sup[1]['time_numeric'], sup[1]['price']
            )
            if m_res == float('inf') or m_sup == float('inf'):
                return 'flat'
            if m_res > 0 and m_sup > 0:
                return 'up'
            if m_res < 0 and m_sup < 0:
                return 'down'
            return 'flat'
        except Exception:
            return 'flat'

    def on_order_event(self, order_event):
        if order_event.status != OrderStatus.FILLED:
            return

        order = self.transactions.get_order_by_id(order_event.order_id)
        if order is None:
            return
        tag = order.tag

        if "Entry" in tag and self._pending_entry:
            entry = self._pending_entry
            self._pending_entry = None
            actual_qty = self.portfolio[self.btc].quantity
            if actual_qty > 0:
                self.limit_order(self.btc, -actual_qty, entry['tp'],
                                  tag=f"{entry['tag']} TP")
                self._active_sl = {
                    'price': entry['sl'], 'tag': entry['tag'],
                    'entry': entry.get('entry', 0)
                }

        if "TP" in tag:
            self._active_sl = None
            self._entry_price = None
