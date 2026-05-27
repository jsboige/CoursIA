# region imports
from AlgorithmImports import *
import numpy as np
from xgboost import XGBClassifier
from sklearn.preprocessing import StandardScaler
# endregion


class ESGFMLXGBoost(QCAlgorithm):
    """
    ESGF ML XGBoost - Template pedagogique.

    XGBoost classifier sur 5 actions tech (variante de ESGF-ML-RandomForest).
    Features (6) : returns 1/5/20j, RSI normalise, ratio SMA20/SMA50, vol 20j.
    Label : rendement 5j > +1% -> Buy (2), < -1% -> Avoid (0), sinon Flat (1).
    Re-entrainement mensuel sur fenetre glissante 2 ans.

    Variante XGBoost du template ESGF-ML-RandomForest. Comparez les Sharpe.

    Inspirez-vous de ce template pour votre projet de groupe :
    - Changez les hyperparametres : n_estimators, max_depth, learning_rate
    - Ajoutez des features (volume, Bollinger, fondamentaux)
    - Tunez les seuils BUY_THRESHOLD / SELL_THRESHOLD
    - Comparez avec sklearn GradientBoosting

    Ref: QC-Py-18-ML-Features-Engineering, QC-Py-19-ML-Supervised-Classification
    """

    TICKERS = ["AAPL", "MSFT", "GOOGL", "AMZN", "NVDA"]
    TRAIN_LOOKBACK = 504
    FORWARD_DAYS = 5
    BUY_THRESHOLD = 0.01
    SELL_THRESHOLD = -0.01

    def initialize(self):
        self.set_start_date(2020, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)
        self.set_benchmark("SPY")

        self.symbols = {}
        for ticker in self.TICKERS:
            self.symbols[ticker] = self.add_equity(ticker, Resolution.DAILY).symbol

        self.model = None
        self.scaler = StandardScaler()

        self.schedule.on(
            self.date_rules.month_start("AAPL"),
            self.time_rules.after_market_open("AAPL", 60),
            self.train_and_rebalance
        )

        self.set_warm_up(self.TRAIN_LOOKBACK + 10, Resolution.DAILY)

    def _compute_features(self, closes, idx):
        if idx < 50:
            return None
        w = closes.iloc[:idx + 1]
        price = w.iloc[-1]

        ret_1d  = price / w.iloc[-2]  - 1 if len(w) >= 2  else 0.0
        ret_5d  = price / w.iloc[-5]  - 1 if len(w) >= 5  else 0.0
        ret_20d = price / w.iloc[-20] - 1 if len(w) >= 20 else 0.0

        vol = float(w.pct_change().iloc[-20:].std()) if len(w) >= 21 else 0.02

        delta = w.pct_change().iloc[-14:]
        gains  = delta.clip(lower=0).mean()
        losses = (-delta.clip(upper=0)).mean()
        rsi = 100 - 100 / (1 + gains / losses) if losses > 0 else 50.0
        rsi_norm = (rsi - 50) / 50

        sma20 = float(w.iloc[-20:].mean())
        sma50 = float(w.iloc[-50:].mean()) if len(w) >= 50 else sma20
        ma_ratio = sma20 / sma50 if sma50 > 0 else 1.0

        features = [ret_1d, ret_5d, ret_20d, vol, rsi_norm, ma_ratio]
        return features if not any(np.isnan(f) for f in features) else None

    def train_and_rebalance(self):
        if self.is_warming_up:
            return

        all_X, all_y = [], []
        for ticker, symbol in self.symbols.items():
            hist = self.history(symbol, self.TRAIN_LOOKBACK + self.FORWARD_DAYS + 5, Resolution.DAILY)
            if hist is None or len(hist) < 100 or "close" not in hist.columns:
                continue
            closes = hist["close"]
            for i in range(50, len(closes) - self.FORWARD_DAYS):
                future_ret = closes.iloc[i + self.FORWARD_DAYS] / closes.iloc[i] - 1
                # XGBoost prefers positive labels: 0=AVOID, 1=FLAT, 2=BUY
                if future_ret > self.BUY_THRESHOLD:
                    label = 2
                elif future_ret < self.SELL_THRESHOLD:
                    label = 0
                else:
                    label = 1
                feat = self._compute_features(closes, i)
                if feat is not None:
                    all_X.append(feat)
                    all_y.append(label)

        if len(all_X) < 50:
            return

        X_scaled = self.scaler.fit_transform(np.array(all_X))
        self.model = XGBClassifier(
            n_estimators=100, max_depth=4, learning_rate=0.1,
            random_state=42, eval_metric='mlogloss', verbosity=0
        )
        self.model.fit(X_scaled, np.array(all_y))
        self.debug(f"XGB trained: {len(all_X)} samples, classes={dict(zip(*np.unique(all_y, return_counts=True)))}")

        self._rebalance()

    def _rebalance(self):
        if self.model is None:
            return

        buy_signals = []
        for ticker, symbol in self.symbols.items():
            hist = self.history(symbol, 60, Resolution.DAILY)
            if hist is None or len(hist) < 51 or "close" not in hist.columns:
                continue
            feat = self._compute_features(hist["close"], len(hist["close"]) - 1)
            if feat is None:
                continue
            x_scaled = self.scaler.transform(np.array(feat).reshape(1, -1))
            proba = self.model.predict_proba(x_scaled)[0]
            classes = list(self.model.classes_)
            buy_prob = proba[classes.index(2)] if 2 in classes else 0.0
            if buy_prob > 0.45:
                buy_signals.append((ticker, symbol, buy_prob))

        selected = {s for _, s, _ in buy_signals}
        for symbol in self.symbols.values():
            if self.portfolio[symbol].invested and symbol not in selected:
                self.liquidate(symbol)

        if not buy_signals:
            return

        weight = 0.95 / len(buy_signals)
        for ticker, symbol, prob in buy_signals:
            self.set_holdings(symbol, weight)
            self.debug(f"BUY {ticker}: buy_prob={prob:.2f}, weight={weight:.1%}")

    def on_data(self, data):
        pass
