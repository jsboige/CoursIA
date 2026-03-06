# region imports
from AlgorithmImports import *
import numpy as np
import pandas as pd
import traceback
from datetime import timezone
from channel_helpers import (
    classic_chart_zigzag, find_best_channel_line_strict_weighted,
    get_line_params_time, get_channel_value_at_time
)
# endregion


class CryptoMultiChannelAlgorithm(QCAlgorithm):
    """Multi-Channel ZigZag strategy on BTC.

    Concept: 2 nested channels (macro/meso) built from ZigZag pivots.
    - Macro channel: overall trend context (500d lookback, all pivots)
    - Meso channel: trading channel (recent pivots within macro)

    Trade on meso channel, fall back to macro if meso unavailable.
    Signals: bounce off support + breakout above resistance (long only).
    """

    def initialize(self):
        self.set_start_date(2020, 1, 1)
        self.set_account_currency("USDT")
        self.set_cash(10000)
        self.btc = self.add_crypto("BTCUSDT", Resolution.DAILY, Market.BINANCE).symbol
        self.set_benchmark(self.btc)
        self.set_brokerage_model(BrokerageName.BINANCE, AccountType.CASH)

        # --- Strategy parameters ---
        self.zigzag_threshold = 0.05
        self.lookback_bars = 500
        self.bounce_entry_offset = 0.05
        self.breakout_confirm = 0.01
        self.sl_pct = 0.05
        self.tp_rr = 2.0
        self.risk_pct = 0.02
        self.max_violation_pct = 0.3

        # --- State ---
        self.channels = {
            "macro": {"resistance": (None, None), "support": (None, None)},
            "meso": {"resistance": (None, None), "support": (None, None)},
        }
        self._day_count = 0
        self._pending_entry = None

        self.set_warm_up(TimeSpan.from_days(60))

    def on_data(self, data):
        if self.is_warming_up:
            return
        if not data.contains_key(self.btc) or data[self.btc] is None:
            return

        self._day_count += 1
        self._recalculate_channels()

        if not self.portfolio[self.btc].invested:
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

            # === MACRO: all pivots ===
            self._fit_channel("macro", high_df, low_df)
            macro_res = self.channels["macro"]["resistance"]
            macro_sup = self.channels["macro"]["support"]
            macro_ok = macro_res[0] is not None and macro_sup[0] is not None

            # === MESO: recent pivots (last ~40% of time range) ===
            self.channels["meso"] = {"resistance": (None, None), "support": (None, None)}
            if macro_ok:
                # Use the last N pivots as meso window
                n_total = len(pivots_df)
                meso_count = max(6, n_total // 3)  # at least 6 pivots, or 1/3 of total
                recent_pivots = pivots_df.tail(meso_count)
                meso_high = recent_pivots[recent_pivots['type'] == -1].copy()
                meso_low = recent_pivots[recent_pivots['type'] == 1].copy()
                if len(meso_high) >= 2 and len(meso_low) >= 2:
                    self._fit_channel("meso", meso_high, meso_low)

            # Diagnostics
            if self._day_count % 60 == 1:
                t = self.time.replace(tzinfo=timezone.utc).timestamp()
                price = self.securities[self.btc].price
                for scale in ["macro", "meso"]:
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

    def _fit_channel(self, scale, high_df, low_df):
        high_np = high_df[['time_numeric', 'price']].values
        low_np = low_df[['time_numeric', 'price']].values

        r1, r2 = find_best_channel_line_strict_weighted(
            high_df, high_np, True, 2.0, 1.0, self.max_violation_pct
        )
        if r1 is not None and r2 is not None:
            self.channels[scale]["resistance"] = (self._to_dict(r1), self._to_dict(r2))
        else:
            self.channels[scale]["resistance"] = (None, None)

        s1, s2 = find_best_channel_line_strict_weighted(
            low_df, low_np, False, 2.0, 1.0, self.max_violation_pct
        )
        if s1 is not None and s2 is not None:
            self.channels[scale]["support"] = (self._to_dict(s1), self._to_dict(s2))
        else:
            self.channels[scale]["support"] = (None, None)

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

        # Prefer meso channels, fall back to macro
        for scale in ["meso", "macro"]:
            res_p = self.channels[scale]["resistance"]
            sup_p = self.channels[scale]["support"]
            if sup_p[0] is not None or res_p[0] is not None:
                active_scale = scale
                break
        else:
            return

        res_p = self.channels[active_scale]["resistance"]
        sup_p = self.channels[active_scale]["support"]
        has_sup = sup_p[0] is not None and sup_p[1] is not None
        has_res = res_p[0] is not None and res_p[1] is not None

        if not has_sup and not has_res:
            return

        # Check macro trend for filtering
        macro_trend = self._get_trend("macro")

        signal = None
        sl_price = None
        tag = None

        # 1. Bounce off support (long)
        if has_sup and macro_trend != 'down':
            sup_val = get_channel_value_at_time(sup_p, t_num)
            if not pd.isna(sup_val) and sup_val > 0:
                if price <= sup_val * (1 + self.bounce_entry_offset) and price >= sup_val * 0.95:
                    signal = 1
                    sl_price = price * (1 - self.sl_pct)
                    tag = f"Bounce {active_scale} Sup"

        # 2. Breakout above resistance (long)
        if signal is None and has_res:
            res_val = get_channel_value_at_time(res_p, t_num)
            if not pd.isna(res_val) and res_val > 0:
                if price > res_val * (1 + self.breakout_confirm):
                    signal = 1
                    sl_price = res_val * 0.98
                    tag = f"Breakout {active_scale} Res"

        if signal is not None and sl_price is not None and sl_price < price:
            risk = price - sl_price
            tp_price = price + risk * self.tp_rr

            usdt_available = self.portfolio.cash_book["USDT"].amount
            cash_risk = usdt_available * self.risk_pct
            position_usdt = min((cash_risk / risk) * price, usdt_available * 0.95)
            qty = round(position_usdt / price, 5)

            if qty > 0 and position_usdt > 10:
                self.debug(f"TRADE: {tag} | price={price:.0f} | SL={sl_price:.0f} | "
                           f"TP={tp_price:.0f} | qty={qty}")
                self._pending_entry = {
                    'qty': qty, 'sl': sl_price, 'tp': tp_price, 'tag': tag
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
                self.stop_market_order(self.btc, -actual_qty, entry['sl'],
                                       tag=f"{entry['tag']} SL")
                self.limit_order(self.btc, -actual_qty, entry['tp'],
                                  tag=f"{entry['tag']} TP")

        if "SL" in tag or "TP" in tag:
            open_orders = self.transactions.get_open_order_tickets(
                lambda t: t.symbol == self.btc
            )
            for ticket in open_orders:
                ticket.cancel("OCO counterpart filled")
