from AlgorithmImports import *
import numpy as np
try:
    import joblib
except ImportError:
    joblib = None
from sklearn.ensemble import RandomForestClassifier

class MyEnhancedCryptoMlAlgorithm(QCAlgorithm):
    """
    Strategie ML amelioree avec:
    - Separation train/test stricte (2021-2022 train, 2023-2024 test)
    - Risk management (stop-loss -5%, take-profit +10%)
    - Retraining periodique (tous les 30 jours)
    - Position sizing probabiliste (confidence thresholds)
    """
    MODEL_KEY = "myCryptoMlModel.pkl"

    # Dates fixes pour eviter data leakage
    # Training: 2021-01-01 a 2022-12-31 (2 ans, periode pre-backtest)
    # Backtest: 2023-01-01 a 2024-06-01 (1.5 ans out-of-sample)
    # Extended: 4 years training (2019-2022) for more regime diversity
    TRAIN_START = datetime(2019, 1, 1)
    TRAIN_END = datetime(2022, 12, 31)
    # Extended: test through present (2023-2026)
    BACKTEST_START = datetime(2023, 1, 1)
    BACKTEST_END = datetime(2026, 3, 1)

    STARTING_CASH = 100000
    SMA_PERIOD = 20
    RSI_PERIOD = 14
    EMA_PERIODS = [10, 20, 50, 200]
    ADX_PERIOD = 14
    ATR_PERIOD = 14

    # Risk management
    STOP_LOSS_PCT = 0.05     # -5%
    TAKE_PROFIT_PCT = 0.10   # +10%

    # Position sizing probabiliste
    CONFIDENCE_LONG_THRESHOLD = 0.6   # Si proba > 0.6: long proportionnel
    CONFIDENCE_EXIT_THRESHOLD = 0.4   # Si proba < 0.4: liquidation
    # Entre 0.4 et 0.6: pas de trade (zone d'incertitude)

    # Retraining periodique
    RETRAIN_INTERVAL_DAYS = 60  # Increased from 30 for more stable model
    RETRAIN_LOOKBACK_DAYS = 730  # 2 years lookback for regime diversity

    def Initialize(self):
        # Configuration backtest (out-of-sample)
        self.SetStartDate(self.BACKTEST_START.year, self.BACKTEST_START.month, self.BACKTEST_START.day)
        self.SetEndDate(self.BACKTEST_END.year, self.BACKTEST_END.month, self.BACKTEST_END.day)

        self.SetAccountCurrency("USDT")
        self.SetCash("USDT", self.STARTING_CASH)
        self.SetBrokerageModel(BrokerageName.Binance, AccountType.Cash)

        self.symbol = self.AddCrypto("BTCUSDT", Resolution.Daily, Market.Binance).Symbol
        self.Securities[self.symbol].SetDataNormalizationMode(DataNormalizationMode.Raw)
        self.SetBenchmark(self.symbol)

        # Modele ML
        self.model = None
        self.last_retrain_date = None

        # Tentative de chargement depuis Object Store
        if joblib and self.ObjectStore.ContainsKey(self.MODEL_KEY):
            file_path = self.ObjectStore.GetFilePath(self.MODEL_KEY)
            self.model = joblib.load(file_path)
            self.Debug(f"Modele charge depuis l'Object Store: {self.MODEL_KEY}")
        else:
            self.Debug(f"Cle {self.MODEL_KEY} introuvable. Entrainement initial au demarrage.")
            self.train_model_scheduled = True

        # Indicateurs techniques
        self.sma = self.SMA(self.symbol, self.SMA_PERIOD, Resolution.Daily)
        self.rsi = self.RSI(self.symbol, self.RSI_PERIOD, MovingAverageType.Wilders, Resolution.Daily)
        self.ema_dict = {}
        for period in self.EMA_PERIODS:
            self.ema_dict[period] = self.EMA(self.symbol, period, Resolution.Daily)
        self.adx = self.ADX(self.symbol, self.ADX_PERIOD, Resolution.Daily)
        self.atr = self.ATR(self.symbol, self.ATR_PERIOD, MovingAverageType.Simple, Resolution.Daily)

        self.prev_close = None

        # Warm-up
        warmup_bars = max(self.EMA_PERIODS) + self.ADX_PERIOD
        self.SetWarmUp(warmup_bars, Resolution.Daily)

        # Risk management - tracking prix d'entree
        self.entry_price = None

        # Planification du retraining periodique (tous les 30 jours a 09:30 UTC)
        self.Schedule.On(
            self.DateRules.Every(DayOfWeek.Monday, DayOfWeek.Tuesday, DayOfWeek.Wednesday,
                                 DayOfWeek.Thursday, DayOfWeek.Friday, DayOfWeek.Saturday, DayOfWeek.Sunday),
            self.TimeRules.At(9, 30),
            self.CheckRetraining
        )

    def CheckRetraining(self):
        """Verifie si retraining necessaire (tous les 30 jours)."""
        if self.IsWarmingUp:
            return

        if self.last_retrain_date is None:
            # Premier retraining
            days_since_last = 999
        else:
            days_since_last = (self.Time - self.last_retrain_date).days

        if days_since_last >= self.RETRAIN_INTERVAL_DAYS:
            self.Debug(f"{self.Time} => Retraining schedule (derniers {days_since_last} jours)")
            success = self._train_model_with_lookback(self.RETRAIN_LOOKBACK_DAYS)
            if success:
                self.last_retrain_date = self.Time
                self.Debug(f"Retraining reussi. Prochain dans {self.RETRAIN_INTERVAL_DAYS} jours.")
            else:
                self.Debug("Retraining echoue. Tentative au prochain cycle.")

    def _train_model_initial(self):
        """
        Entrainement initial sur la periode 2021-2022 (training set fixe).
        Utilise uniquement les donnees anterieures au backtest pour eviter data leakage.
        """
        # Calcul du nombre de jours entre TRAIN_START et TRAIN_END
        training_days = (self.TRAIN_END - self.TRAIN_START).days + 1

        # Recuperation historique depuis TRAIN_START
        history = self.History(self.symbol, self.TRAIN_START, self.TRAIN_END, Resolution.Daily)

        if history.empty or len(history) < 60:
            self.Debug("Pas assez d'historique pour l'entrainement initial.")
            return False

        closes = history['close'].values
        highs = history['high'].values
        lows = history['low'].values

        # Construction des features
        X_list, y_list = [], []
        for i in range(max(self.EMA_PERIODS) + 1, len(closes) - 1):
            features = self._compute_features(closes, highs, lows, i)
            # Label : le prix monte le lendemain ?
            label = 1 if closes[i+1] > closes[i] else 0
            X_list.append(features)
            y_list.append(label)

        if len(X_list) < 30:
            return False

        X_train = np.array(X_list)
        y_train = np.array(y_list)

        self.model = RandomForestClassifier(n_estimators=100, max_depth=5, random_state=42)
        self.model.fit(X_train, y_train)

        accuracy = self.model.score(X_train, y_train)
        self.Debug(f"Modele initial entraine (2021-2022): {len(X_train)} samples, accuracy={accuracy:.2%}")
        return True

    def _train_model_with_lookback(self, lookback_days):
        """
        Retraining periodique sur les derniers N jours.
        Utilise uniquement les donnees passees (rolling window).
        """
        history = self.History(self.symbol, lookback_days, Resolution.Daily)

        if history.empty or len(history) < 60:
            self.Debug(f"Pas assez d'historique pour retraining ({len(history)} jours).")
            return False

        closes = history['close'].values
        highs = history['high'].values
        lows = history['low'].values

        # Construction des features
        X_list, y_list = [], []
        for i in range(max(self.EMA_PERIODS) + 1, len(closes) - 1):
            features = self._compute_features(closes, highs, lows, i)
            label = 1 if closes[i+1] > closes[i] else 0
            X_list.append(features)
            y_list.append(label)

        if len(X_list) < 30:
            return False

        X_train = np.array(X_list)
        y_train = np.array(y_list)

        self.model = RandomForestClassifier(n_estimators=100, max_depth=5, random_state=42)
        self.model.fit(X_train, y_train)

        accuracy = self.model.score(X_train, y_train)
        self.Debug(f"Modele retrained ({lookback_days}j): {len(X_train)} samples, accuracy={accuracy:.2%}")
        return True

    def _compute_features(self, closes, highs, lows, i):
        """Calcule les features pour l'index i."""
        daily_ret = (closes[i] - closes[i-1]) / closes[i-1] if closes[i-1] > 0 else 0
        sma_20 = np.mean(closes[i-self.SMA_PERIOD:i])
        rsi_14 = self._compute_rsi(closes[i-self.RSI_PERIOD:i+1])
        ema_10 = self._ema(closes[:i+1], 10)
        ema_20 = self._ema(closes[:i+1], 20)
        ema_50 = self._ema(closes[:i+1], 50)
        ema_200 = self._ema(closes[:i+1], 200)
        adx_val = self._compute_adx(highs[i-self.ADX_PERIOD:i+1], lows[i-self.ADX_PERIOD:i+1], closes[i-self.ADX_PERIOD:i+1])
        atr_val = np.mean([highs[j] - lows[j] for j in range(max(0, i-self.ATR_PERIOD), i)])
        return [sma_20, rsi_14, daily_ret, ema_10, ema_20, ema_50, ema_200, adx_val, atr_val]

    def _ema(self, data, period):
        if len(data) < period:
            return np.mean(data)
        multiplier = 2.0 / (period + 1)
        ema = np.mean(data[:period])
        for val in data[period:]:
            ema = (val - ema) * multiplier + ema
        return ema

    def _compute_rsi(self, prices):
        if len(prices) < 2:
            return 50.0
        deltas = np.diff(prices)
        gains = np.where(deltas > 0, deltas, 0)
        losses = np.where(deltas < 0, -deltas, 0)
        avg_gain = np.mean(gains) if len(gains) > 0 else 0
        avg_loss = np.mean(losses) if len(losses) > 0 else 1e-10
        rs = avg_gain / max(avg_loss, 1e-10)
        return 100 - (100 / (1 + rs))

    def _compute_adx(self, highs, lows, closes):
        if len(highs) < 3:
            return 25.0
        tr = [max(highs[i] - lows[i], abs(highs[i] - closes[i-1]), abs(lows[i] - closes[i-1]))
              for i in range(1, len(highs))]
        return np.mean(tr) if tr else 25.0

    def OnData(self, slice: Slice):
        if not slice.Bars.ContainsKey(self.symbol):
            return

        bar = slice.Bars[self.symbol]
        current_price = bar.Close

        if self.IsWarmingUp:
            return

        # Verification indicateurs prets
        if not self.sma.IsReady or not self.rsi.IsReady or not self.adx.IsReady or not self.atr.IsReady:
            return
        for period in self.EMA_PERIODS:
            if not self.ema_dict[period].IsReady:
                return

        # Entrainement initial si necessaire
        if self.model is None and getattr(self, 'train_model_scheduled', False):
            self.train_model_scheduled = False
            if not self._train_model_initial():
                self.Debug("Entrainement initial echoue. Arret.")
                self.Quit("Impossible d'entrainer le modele.")
                return

        if self.model is None:
            return

        # Calcul daily return
        if self.prev_close is None:
            self.prev_close = current_price
            return

        daily_return = (current_price - self.prev_close) / self.prev_close
        self.prev_close = current_price

        # Extraction features actuelles
        sma_val = self.sma.Current.Value
        rsi_val = self.rsi.Current.Value
        ema_10 = self.ema_dict[10].Current.Value
        ema_20 = self.ema_dict[20].Current.Value
        ema_50 = self.ema_dict[50].Current.Value
        ema_200 = self.ema_dict[200].Current.Value
        adx_val = self.adx.Current.Value
        atr_val = self.atr.Current.Value

        X = np.array([[sma_val, rsi_val, daily_return, ema_10, ema_20, ema_50, ema_200, adx_val, atr_val]])

        # Prediction probabiliste
        proba = self.model.predict_proba(X)[0]  # [proba_down, proba_up]
        confidence_up = proba[1]  # Probabilite de hausse

        # Risk management - Stop-loss et Take-profit
        if self.Portfolio[self.symbol].Invested:
            if self.entry_price is not None:
                pnl_pct = (current_price - self.entry_price) / self.entry_price

                # Stop-loss a -5%
                if pnl_pct <= -self.STOP_LOSS_PCT:
                    self.Liquidate(self.symbol)
                    self.Debug(f"{self.Time} => STOP-LOSS declenche @ {current_price:.2f} (PnL: {pnl_pct:.2%})")
                    self.entry_price = None
                    return

                # Take-profit a +10%
                if pnl_pct >= self.TAKE_PROFIT_PCT:
                    self.Liquidate(self.symbol)
                    self.Debug(f"{self.Time} => TAKE-PROFIT declenche @ {current_price:.2f} (PnL: {pnl_pct:.2%})")
                    self.entry_price = None
                    return

        # Position sizing probabiliste
        if confidence_up > self.CONFIDENCE_LONG_THRESHOLD:
            # Signal LONG avec confiance elevee
            # Position proportionnelle a la confiance (max 100%)
            position_size = min(confidence_up, 1.0)

            if not self.Portfolio[self.symbol].Invested:
                self.SetHoldings(self.symbol, position_size)
                self.entry_price = current_price
                self.Debug(f"{self.Time} => LONG @ {current_price:.2f} | Confidence: {confidence_up:.2%} | Size: {position_size:.2%}")
            else:
                # Ajustement position si deja investi
                current_holdings = self.Portfolio[self.symbol].HoldingsValue / self.Portfolio.TotalPortfolioValue
                if abs(current_holdings - position_size) > 0.1:  # Rebalance si ecart > 10%
                    self.SetHoldings(self.symbol, position_size)
                    self.Debug(f"{self.Time} => Rebalance @ {current_price:.2f} | New size: {position_size:.2%}")

        elif confidence_up < self.CONFIDENCE_EXIT_THRESHOLD:
            # Signal EXIT avec confiance faible de hausse (donc confiance elevee de baisse)
            if self.Portfolio[self.symbol].Invested:
                final_pnl = (current_price - self.entry_price) / self.entry_price if self.entry_price else 0
                self.Liquidate(self.symbol)
                self.Debug(f"{self.Time} => EXIT @ {current_price:.2f} | Confidence: {confidence_up:.2%} | Final PnL: {final_pnl:.2%}")
                self.entry_price = None

        else:
            # Zone d'incertitude (0.4 < confidence < 0.6) - Pas de trade
            pass
