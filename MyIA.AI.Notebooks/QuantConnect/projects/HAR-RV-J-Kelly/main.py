# region imports
from AlgorithmImports import *
# endregion
import numpy as np
from collections import deque


class HarrvjKellyAlgorithm(QCAlgorithm):
    """HAR-RV-J / HAR Classic Kelly strategy on crypto assets with 3 sizing arms.

    Extends HAR (Corsi 2009) with optional jump component from
    Huang-Tauchen bipower variation (Andersen, Bollerslev & Diebold 2007).

    RV_t = BPV_t + J_t,  where J_t = max(RV_t - (pi/2)*BPV_t, 0)

    Set parameter use_jumps=1 for HAR-RV-J (6 features),
    use_jumps=0 for HAR Classic (3 features).

    Sizing arms (parameter sizing_mode):
      0 = quarter-Kelly mu/sigma^2 (baseline, kelly_fraction=0.25, cap 0.30)
      1 = rolling trade-based Kelly (article #18312 inspired-by, window 40 trades,
          multiplier 1.5, cap 0.30) - probability-of-profit + win/loss ratio from
          last N closed trades, NOT from mu/sigma^2
      2 = prudent vol-targeted Kelly (quarter mu/sigma^2 shrunk by inverse
          realized volatility forecast, cap 0.20) - keeps mu/sigma^2 base
          but scales down in high-vol regimes

    Assets: BTCUSDT, ETHUSDT, LTCUSDT, BCHUSDT (crypto, Binance).
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_end_date(2025, 6, 1)
        self.set_cash(100000)
        self.set_account_currency("USDT")
        self.set_brokerage_model(BrokerageName.BINANCE, AccountType.CASH)

        # Parameter: 1 = HAR-RV-J (6 features), 0 = HAR Classic (3 features)
        self.use_jumps = self.get_parameter("use_jumps", "1") == "1"

        # Parameter: sizing_mode 0/1/2 (see class docstring)
        self.sizing_mode = int(self.get_parameter("sizing_mode", "0"))

        # Crypto tickers (Binance-provided)
        self.tickers = ["BTCUSDT", "ETHUSDT", "LTCUSDT", "BCHUSDT"]
        self.symbols = {}
        for ticker in self.tickers:
            crypto = self.add_crypto(ticker, Resolution.DAILY, Market.BINANCE)
            self.symbols[ticker] = crypto.symbol

        # Model parameters
        self.train_window = 500
        self.refit_freq = 22
        self.kelly_fraction = 0.25  # mode 0: baseline quarter-Kelly
        self.forecast_horizon = 5

        # Mode 1 (rolling trade-based Kelly, article #18312): window of last N trades
        self.trade_kelly_window = 40
        self.trade_kelly_multiplier = 1.5  # 1.5x Kelly inspired-by article

        # Mode 2 (prudent vol-targeted): scale-down factor
        self.vol_target = 0.40  # 40% annualized vol target

        # Per-asset state
        self.daily_rv = {t: deque(maxlen=self.train_window + 50) for t in self.tickers}
        self.daily_bpv = {t: deque(maxlen=self.train_window + 50) for t in self.tickers}
        self.daily_jumps = {t: deque(maxlen=self.train_window + 50) for t in self.tickers}
        self.daily_ret = {t: deque(maxlen=50) for t in self.tickers}
        self.coefs = {t: None for t in self.tickers}
        self.last_fit_day = {t: -100 for t in self.tickers}

        # Trade log per asset for mode 1 (rolling trade-based Kelly).
        # Each entry: signed trade P&L as fraction of capital at trade time.
        # Cleared on the rebalance bar.
        self.trade_pnl = {t: deque(maxlen=self.trade_kelly_window + 5) for t in self.tickers}
        # Pre-rebalance portfolio value to compute trade P&L after rebalance
        self._pre_rebalance_value = None
        self._pre_rebalance_held = set()

        self.day_count = 0

        self.schedule.on(
            self.date_rules.every(DayOfWeek.MONDAY),
            self.time_rules.at(0, 0),
            self.rebalance,
        )

        self.set_warm_up(250, Resolution.DAILY)

    def on_data(self, data: Slice):
        for ticker, sym in self.symbols.items():
            if not data.bars.contains_key(sym):
                continue
            bar = data[sym]
            if bar is None:
                continue

            hist = self.history(sym, 2, Resolution.DAILY)
            if hist is not None and len(hist) >= 2:
                prev = float(hist["close"].iloc[-2])
                curr = float(bar.close)
                if prev > 0:
                    r = np.log(curr / prev)
                    rv = r ** 2

                    rets = list(self.daily_ret[ticker])
                    if len(rets) >= 1:
                        bpv = (np.pi / 2) * abs(r) * abs(rets[-1])
                    else:
                        bpv = rv

                    jump = max(rv - bpv, 0)

                    self.daily_rv[ticker].append(rv)
                    self.daily_bpv[ticker].append(bpv)
                    self.daily_jumps[ticker].append(jump)
                    self.daily_ret[ticker].append(r)

        self.day_count += 1

    def rebalance(self):
        if self.is_warming_up:
            return

        # Mode 1: record trade P&L from previous rebalance bar.
        # Attribute the portfolio return to each ticker that was held at EITHER
        # this or the previous rebalance. This way trade_pnl starts populating
        # as soon as positions are opened, even if the first few rebalances see
        # the position opened mid-cycle.
        if self.sizing_mode == 1 and self._pre_rebalance_value is not None:
            current_value = float(self.portfolio.total_portfolio_value)
            trade_ret = (current_value / self._pre_rebalance_value) - 1.0
            # Track tickers held now or at last snapshot
            now_held = {
                t for t in self.tickers
                if self.portfolio[self.symbols[t]].invested
            }
            all_held = now_held | self._pre_rebalance_held
            if all_held:
                per_asset_ret = trade_ret / len(all_held)
                for t in all_held:
                    self.trade_pnl[t].append(per_asset_ret)

        weights = {}
        for ticker in self.tickers:
            sym = self.symbols[ticker]
            if len(self.daily_rv[ticker]) < self.train_window:
                continue

            var_forecast = self._forecast(ticker)
            if var_forecast is None or var_forecast <= 0:
                continue

            vol_ann = np.sqrt(var_forecast * 252 / self.forecast_horizon)

            rets = list(self.daily_ret[ticker])
            if len(rets) < 5:
                continue
            mom_5d = sum(rets[-5:])
            direction = 1.0 if mom_5d > 0 else 0.0

            if self.sizing_mode == 0:
                w = self._size_mu_var(rets, vol_ann)
            elif self.sizing_mode == 1:
                # Mode 1: rolling trade-based Kelly. Cold-start: fall back to
                # mu/var quarter-Kelly until trade_pnl has enough observations
                # to compute a stable win-rate + win/loss ratio. This avoids
                # the bootstrap deadlock where mode 1 returns 0 because no
                # trades have been recorded, so no positions are opened, so
                # no trades can ever be recorded.
                if len(self.trade_pnl[ticker]) >= self.trade_kelly_window:
                    w = self._size_trade_based(ticker)
                else:
                    w = self._size_mu_var(rets, vol_ann)
            elif self.sizing_mode == 2:
                w = self._size_vol_targeted(rets, vol_ann)
            else:
                w = 0.0

            weights[ticker] = w * direction

        total = sum(weights.values())
        if total > 1.0:
            weights = {t: w / total for t, w in weights.items()}

        for ticker in self.tickers:
            sym = self.symbols[ticker]
            w = weights.get(ticker, 0.0)
            if w > 0.001:
                self.set_holdings(sym, w)
            else:
                self.liquidate(sym)

        # Record portfolio value and held set for next-rebalance trade P&L attribution (mode 1)
        self._pre_rebalance_value = float(self.portfolio.total_portfolio_value)
        self._pre_rebalance_held = {
            t for t in self.tickers
            if self.portfolio[self.symbols[t]].invested
        }

    def _size_mu_var(self, rets, vol_ann):
        """Mode 0: quarter-Kelly from mu/sigma^2 (baseline).

        f* = mu_ann / sigma^2 (continuous-time Kelly for excess return 0).
        Sized at quarter (kelly_fraction=0.25), capped at 0.30.
        """
        mu_daily = np.mean(rets[-20:]) if len(rets) >= 20 else 0.0
        mu_ann = mu_daily * 252
        var_ann = vol_ann ** 2
        if var_ann <= 1e-8:
            return 0.0
        kelly_full = mu_ann / var_ann
        kelly_adj = max(0, kelly_full * self.kelly_fraction)
        return min(kelly_adj, 0.30)

    def _size_trade_based(self, ticker):
        """Mode 1: rolling trade-based Kelly (article #18312).

        f* = p - (1 - p) / (win/loss ratio) on the last N closed trades.
        Multiplier 1.5 matches the article's chosen parameter (between 1x and 2x).
        Cap 0.30 to align with baseline's exposure ceiling.

        Falls back to 0 if fewer than 5 trades or no winners/losers observed.
        """
        trades = list(self.trade_pnl[ticker])
        if len(trades) < 5:
            return 0.0
        trades = trades[-self.trade_kelly_window:]
        wins = [t for t in trades if t > 0]
        losses = [t for t in trades if t <= 0]
        if len(wins) == 0 or len(losses) == 0:
            return 0.0
        p = len(wins) / len(trades)
        avg_win = float(np.mean(wins))
        avg_loss = float(np.mean(losses))  # negative
        if avg_win <= 0 or avg_loss >= 0:
            return 0.0
        win_loss_ratio = avg_win / abs(avg_loss)
        kelly_full = p - (1.0 - p) / win_loss_ratio
        kelly_adj = max(0, kelly_full * self.trade_kelly_multiplier)
        return min(kelly_adj, 0.30)

    def _size_vol_targeted(self, rets, vol_ann):
        """Mode 2: prudent vol-targeted Kelly.

        Base = quarter-Kelly from mu/sigma^2 (same formula as mode 0).
        Scale by min(vol_target / realized_vol_ann, 1.0) so that in high-vol
        regimes the position shrinks toward zero rather than compounding.
        Cap 0.20 (tighter than baseline's 0.30) to reflect additional caution.
        """
        mu_daily = np.mean(rets[-20:]) if len(rets) >= 20 else 0.0
        mu_ann = mu_daily * 252
        var_ann = vol_ann ** 2
        if var_ann <= 1e-8:
            return 0.0
        kelly_full = mu_ann / var_ann
        kelly_adj = max(0, kelly_full * self.kelly_fraction)
        # Inverse-vol scaling
        vol_scale = min(self.vol_target / vol_ann, 1.0) if vol_ann > 0 else 0.0
        return min(kelly_adj * vol_scale, 0.20)

    def _forecast(self, ticker):
        """Unified forecast: HAR-RV-J or HAR Classic based on parameter."""
        rv = np.array(self.daily_rv[ticker])
        n = len(rv)
        if n < self.train_window:
            return None
        rv = rv[-self.train_window:]

        jumps = np.array(self.daily_jumps[ticker])[-self.train_window:] if self.use_jumps else None

        should_refit = (self.day_count - self.last_fit_day[ticker]) >= self.refit_freq
        if should_refit or self.coefs[ticker] is None:
            coefs = self._fit(rv, jumps)
            if coefs is not None:
                self.coefs[ticker] = coefs
                self.last_fit_day[ticker] = self.day_count

        if self.coefs[ticker] is None:
            return None

        log_rv = np.log(np.maximum(rv, 1e-12))
        rv_d = log_rv[-1]
        rv_w = float(np.mean(log_rv[-5:])) if len(log_rv) >= 5 else rv_d
        rv_m = float(np.mean(log_rv[-22:])) if len(log_rv) >= 22 else rv_w

        c = self.coefs[ticker]
        if self.use_jumps:
            j_d = jumps[-1]
            j_w = float(np.mean(jumps[-5:])) if len(jumps) >= 5 else j_d
            j_m = float(np.mean(jumps[-22:])) if len(jumps) >= 22 else j_w
            log_rv_pred = c[0] + c[1]*rv_d + c[2]*rv_w + c[3]*rv_m + c[4]*j_d + c[5]*j_w + c[6]*j_m
        else:
            log_rv_pred = c[0] + c[1]*rv_d + c[2]*rv_w + c[3]*rv_m

        # Iterated h-step forecast
        hist_rv = list(log_rv)
        hist_j = list(jumps) if jumps is not None else None
        for _ in range(self.forecast_horizon - 1):
            tail_rv = hist_rv[-22:]
            d = tail_rv[-1]
            w = float(np.mean(tail_rv[-5:]))
            m = float(np.mean(tail_rv))
            if self.use_jumps and hist_j is not None:
                tail_j = hist_j[-22:]
                jd = tail_j[-1]
                jw = float(np.mean(tail_j[-5:]))
                jm = float(np.mean(tail_j))
                pred = c[0] + c[1]*d + c[2]*w + c[3]*m + c[4]*jd + c[5]*jw + c[6]*jm
                hist_j.append(jm)
            else:
                pred = c[0] + c[1]*d + c[2]*w + c[3]*m
            hist_rv.append(pred)

        avg_log_rv = float(np.mean(hist_rv[len(log_rv):]))
        return np.exp(avg_log_rv)

    def _fit(self, rv, jumps):
        """OLS fit: HAR-RV-J(6 features) or HAR Classic(3 features)."""
        log_rv = np.log(np.maximum(rv, 1e-12))
        n = len(log_rv)
        if n < 50:
            return None

        y = []
        X = []
        for i in range(22, n - 1):
            y.append(log_rv[i + 1])
            rv_d = log_rv[i]
            rv_w = float(np.mean(log_rv[max(0, i - 4):i + 1]))
            rv_m = float(np.mean(log_rv[max(0, i - 21):i + 1]))
            if self.use_jumps and jumps is not None:
                j_d = jumps[i]
                j_w = float(np.mean(jumps[max(0, i - 4):i + 1]))
                j_m = float(np.mean(jumps[max(0, i - 21):i + 1]))
                X.append([1.0, rv_d, rv_w, rv_m, j_d, j_w, j_m])
            else:
                X.append([1.0, rv_d, rv_w, rv_m])

        if len(y) < 30:
            return None

        X = np.array(X)
        y = np.array(y)
        try:
            coefs, _, _, _ = np.linalg.lstsq(X, y, rcond=None)
            return tuple(coefs)
        except Exception:
            return None
