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

    Simplified v6: macro-only channels first, to verify trading mechanics.
    Then meso/micro can be added back once signals fire.
    """

    def initialize(self):
        self.set_start_date(2020, 1, 1)
        self.set_account_currency("USDT")
        self.set_cash(10000)  # 10,000 USDT
        self.btc = self.add_crypto("BTCUSDT", Resolution.DAILY, Market.BINANCE).symbol
        self.set_benchmark(self.btc)
        self.set_brokerage_model(BrokerageName.BINANCE, AccountType.CASH)

        # --- Strategy parameters ---
        self.zigzag_threshold = 0.05
        self.lookback_bars = 500
        self.bounce_entry_offset = 0.05  # within 5% of support
        self.breakout_confirm = 0.01  # 1% above resistance
        self.sl_pct = 0.05  # 5% stop loss
        self.tp_rr = 2.0  # 2:1 reward/risk
        self.risk_pct = 0.02  # 2% risk per trade
        self.max_violation_pct = 0.3  # 30% violations allowed

        # --- State ---
        self.channels = {"resistance": (None, None), "support": (None, None)}
        self.trade_active = False
        self._day_count = 0
        self._pending_entry = None

        self.set_warm_up(TimeSpan.from_days(60))

    def on_data(self, data):
        if self.is_warming_up:
            return
        if not data.contains_key(self.btc) or data[self.btc] is None:
            return

        self._day_count += 1

        # Recalculate channels daily
        self._recalculate_channels()

        # Entry logic
        if not self.portfolio[self.btc].invested:
            self._check_entry(data)

    def _recalculate_channels(self):
        try:
            history_df = self.history(self.btc, self.lookback_bars, Resolution.DAILY)
            if history_df.empty:
                if self._day_count <= 3:
                    self.debug(f"Day {self._day_count}: No history data")
                return

            if isinstance(history_df.index, pd.MultiIndex):
                history_df = history_df.loc[self.btc]

            history_df = history_df.reset_index()
            if 'time' not in history_df.columns:
                time_col = [c for c in history_df.columns if 'time' in c.lower() or 'date' in c.lower()]
                if time_col:
                    history_df = history_df.rename(columns={time_col[0]: 'time'})
                elif 'index' in history_df.columns:
                    history_df = history_df.rename(columns={'index': 'time'})
                else:
                    if self._day_count <= 3:
                        self.debug(f"Day {self._day_count}: Columns = {history_df.columns.tolist()}")
                    return

            price_col = 'close' if 'close' in history_df.columns else None
            if price_col is None:
                if self._day_count <= 3:
                    self.debug(f"Day {self._day_count}: No close column. Cols: {history_df.columns.tolist()}")
                return

            history_df['time'] = pd.to_datetime(history_df['time'])
            if history_df['time'].dt.tz is None:
                history_df['time'] = history_df['time'].dt.tz_localize('UTC')

            df_zz = history_df[['time', price_col]].rename(columns={price_col: 'close'})
            pivot_list = classic_chart_zigzag(df_zz, self.zigzag_threshold)

            if not pivot_list or len(pivot_list) < 4:
                if self._day_count <= 3:
                    self.debug(f"Day {self._day_count}: Only {len(pivot_list) if pivot_list else 0} pivots")
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
                if self._day_count <= 3:
                    self.debug(f"Day {self._day_count}: {len(high_df)} highs, {len(low_df)} lows")
                return

            high_np = high_df[['time_numeric', 'price']].values
            low_np = low_df[['time_numeric', 'price']].values

            # Find resistance
            r1, r2 = find_best_channel_line_strict_weighted(
                high_df, high_np, True, 2.0, 1.0, self.max_violation_pct
            )
            if r1 is not None and r2 is not None:
                self.channels["resistance"] = (
                    self._to_dict(r1), self._to_dict(r2)
                )
            else:
                self.channels["resistance"] = (None, None)

            # Find support
            s1, s2 = find_best_channel_line_strict_weighted(
                low_df, low_np, False, 2.0, 1.0, self.max_violation_pct
            )
            if s1 is not None and s2 is not None:
                self.channels["support"] = (
                    self._to_dict(s1), self._to_dict(s2)
                )
            else:
                self.channels["support"] = (None, None)

            # Log diagnostics periodically
            if self._day_count % 30 == 1:
                res_ok = self.channels["resistance"][0] is not None
                sup_ok = self.channels["support"][0] is not None
                self.debug(f"[Chan] Day {self._day_count}: res={res_ok} sup={sup_ok} "
                           f"pivots={len(pivots_df)} (H:{len(high_df)} L:{len(low_df)})")
                if res_ok and sup_ok:
                    t = self.time.replace(tzinfo=timezone.utc).timestamp()
                    rv = get_channel_value_at_time(self.channels["resistance"], t)
                    sv = get_channel_value_at_time(self.channels["support"], t)
                    price = self.securities[self.btc].price
                    self.debug(f"[Chan] price={price:.0f} res={rv:.0f} sup={sv:.0f}")

        except Exception:
            self.error(f"Recalc error: {traceback.format_exc()}")

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

        res_p = self.channels["resistance"]
        sup_p = self.channels["support"]

        # Need at least support for bounce entry
        has_sup = sup_p[0] is not None and sup_p[1] is not None
        has_res = res_p[0] is not None and res_p[1] is not None

        if not has_sup and not has_res:
            return

        signal = None
        sl_price = None
        tag = None

        if has_sup:
            sup_val = get_channel_value_at_time(sup_p, t_num)
            if not pd.isna(sup_val) and sup_val > 0:
                # Bounce off support: price within 5% above support
                if price <= sup_val * (1 + self.bounce_entry_offset) and price >= sup_val * 0.95:
                    signal = 1
                    sl_price = price * (1 - self.sl_pct)
                    tag = "Bounce Support"

        if signal is None and has_res:
            res_val = get_channel_value_at_time(res_p, t_num)
            if not pd.isna(res_val) and res_val > 0:
                # Breakout above resistance
                if price > res_val * (1 + self.breakout_confirm):
                    signal = 1
                    sl_price = res_val * 0.98  # SL just below resistance
                    tag = "Breakout Resistance"

        if signal is not None and sl_price is not None and sl_price < price:
            risk = price - sl_price
            tp_price = price + risk * self.tp_rr

            # Position sizing: use available USDT directly
            usdt_available = self.portfolio.cash_book["USDT"].amount
            cash_risk = usdt_available * self.risk_pct
            position_usdt = min((cash_risk / risk) * price, usdt_available * 0.95)
            qty = round(position_usdt / price, 5)  # BTC precision

            if qty > 0 and position_usdt > 10:  # min $10 order
                self.debug(f"TRADE: {tag} | price={price:.0f} | SL={sl_price:.0f} | "
                           f"TP={tp_price:.0f} | qty={qty}")
                self._pending_entry = {
                    'qty': qty, 'sl': sl_price, 'tp': tp_price, 'tag': tag
                }
                self.market_order(self.btc, qty, tag=f"{tag} Entry")

    def on_order_event(self, order_event):
        if order_event.status != OrderStatus.FILLED:
            return

        order = self.transactions.get_order_by_id(order_event.order_id)
        if order is None:
            return

        tag = order.tag

        # Entry filled: place SL/TP with actual holdings
        if "Entry" in tag and hasattr(self, '_pending_entry') and self._pending_entry:
            entry = self._pending_entry
            self._pending_entry = None
            # Use actual BTC holdings (net of fees)
            actual_qty = self.portfolio[self.btc].quantity
            if actual_qty > 0:
                self.stop_market_order(self.btc, -actual_qty, entry['sl'],
                                       tag=f"{entry['tag']} SL")
                self.limit_order(self.btc, -actual_qty, entry['tp'],
                                  tag=f"{entry['tag']} TP")

        # If SL or TP filled, cancel the other
        if "SL" in tag or "TP" in tag:
            open_orders = self.transactions.get_open_order_tickets(
                lambda t: t.symbol == self.btc
            )
            for ticket in open_orders:
                ticket.cancel("OCO counterpart filled")
