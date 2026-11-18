from AlgorithmImports import *
from collections import deque
import numpy as np
import pandas as pd
try:
    import joblib
except ImportError:
    joblib = None
from sklearn.ensemble import RandomForestClassifier

class MyEnhancedCryptoMlAlgorithm(QCAlgorithm):
    """
    Strategie ML amelioree avec:
    - Separation train/test stricte (entrainement 2017-2020, backtest 2021-2026)
    - Risk management (stop-loss -8%, take-profit +15%)
    - Retraining periodique (tous les 60 jours)
    - Position sizing probabiliste (confidence thresholds)
    - Enhanced trend filter (EMA200 + RSI + ADX)
    - Model regularization (n_estimators=50, max_depth=4)
    """
    MODEL_KEY = "myCryptoMlModel.pkl"

    # Dates fixes pour eviter data leakage
    # Training: 2017-2020 (4 ans: bull 2017, bear 2018, recovery 2019, COVID 2020)
    # Backtest: 2021-2026 (out-of-sample, >= 5 ans, no overlap with training)
    TRAIN_START = datetime(2017, 1, 1)
    TRAIN_END = datetime(2020, 12, 31)
    BACKTEST_START = datetime(2021, 1, 1)
    BACKTEST_END = datetime(2026, 3, 1)

    STARTING_CASH = 100000
    SMA_PERIOD = 20
    RSI_PERIOD = 14
    EMA_PERIODS = [10, 20, 50, 200]
    ADX_PERIOD = 14
    ATR_PERIOD = 14

    # Risk management - optimized based on research
    STOP_LOSS_PCT = 0.08     # -8% (optimized from 10%)
    TAKE_PROFIT_PCT = 0.15   # +15% (optimized from 20%)

    # Volatility filter (based on research: 60% threshold = optimal Sharpe)
    VOLATILITY_THRESHOLD = 0.60  # Skip trading if annual vol > 60%

    # Position sizing probabiliste - optimized thresholds
    CONFIDENCE_LONG_THRESHOLD = 0.56   # Si proba > 0.56: long (relaxed from 0.58 for more trades)
    CONFIDENCE_EXIT_THRESHOLD = 0.40   # Si proba < 0.40: liquidation (relaxed from 0.42)

    # Retraining periodique
    RETRAIN_INTERVAL_DAYS = 60  # Increased from 30 for more stable model
    RETRAIN_LOOKBACK_DAYS = 730  # 2 years lookback for regime diversity

    def Initialize(self):
        # Configuration backtest (out-of-sample). Fenetre par parametre (#23504),
        # par defaut la fenetre publiee.
        start = datetime.strptime(self.GetParameter("start_date", self.BACKTEST_START.strftime("%Y-%m-%d")), "%Y-%m-%d")
        end = datetime.strptime(self.GetParameter("end_date", self.BACKTEST_END.strftime("%Y-%m-%d")), "%Y-%m-%d")
        self.SetStartDate(start.year, start.month, start.day)
        self.SetEndDate(end.year, end.month, end.day)

        # #23504. `gate` : entries (defaut) = le filtre de volatilite bloque les entrees
        # et les renforcements, les sorties sont evaluees chaque jour ; legacy = code
        # d'origine, ou le filtre faisait `return` avant le stop, la prise de benefice
        # et la sortie du modele.
        self.gate = self.GetParameter("gate", "entries").lower()
        if self.gate not in ("entries", "legacy"):
            raise ValueError(f"unknown gate parameter: {self.gate} (expected entries or legacy)")
        # `features` : train (defaut) = a l'inference, le vecteur est calcule par
        # _compute_features sur les dernieres barres, comme a l'entrainement ; legacy =
        # indicateurs Lean d'origine (ADX 0-100 dans la colonne ou l'entrainement met un
        # true range moyen, RSI Wilders, ATR, volatilite ATR/prix).
        self.features_mode = self.GetParameter("features", "train").lower()
        if self.features_mode not in ("train", "legacy"):
            raise ValueError(f"unknown features parameter: {self.features_mode} (expected train or legacy)")
        # `mode` : strategy (defaut) ou btc (BTC achete le premier jour et detenu).
        self.mode = self.GetParameter("mode", "strategy").lower()
        if self.mode not in ("strategy", "btc"):
            raise ValueError(f"unknown mode parameter: {self.mode} (expected strategy or btc)")
        self.reference_bought = False

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
            self.model_source = "objectstore"
            self.Debug(f"Modele charge depuis l'Object Store: {self.MODEL_KEY}")
        else:
            self.model_source = "trained"
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

        # Fenetre des barres journalieres pour features=train : meme profondeur que
        # l'historique du re-entrainement. Elements (fin de barre, close, high, low).
        self.window = deque(maxlen=self.RETRAIN_LOOKBACK_DAYS)
        self.train_adx_min = None  # minimum de la colonne 8 au dernier entrainement

        # Mesures #23504 (statistiques d'execution, sans effet sur la decision).
        self.gate_days = 0                 # jours ou le filtre est actif
        self.gate_days_invested = 0        # dont jours avec une ligne detenue
        self.suspended_breaches = 0        # legacy : stop ou prise de benefice depasses, sans sortie
        self.stop_exits = 0
        self.tp_exits = 0
        self.model_exits = 0
        self.gate_exits = 0                # entries : sorties un jour de filtre actif
        self.predict_days = 0
        self.adx_slot_below_train_min = 0  # colonne 8 d'inference sous le minimum d'entrainement
        self.entries = 0

        # Trace `shadow` (#18923) : valeur du portefeuille une fois par barre
        # journaliere, dans e0..e4.
        self.trace_count = 0

        # Planification du retraining periodique (tous les 60 jours a 09:30 UTC)
        self.Schedule.On(
            self.DateRules.Every(DayOfWeek.Monday, DayOfWeek.Tuesday, DayOfWeek.Wednesday,
                                 DayOfWeek.Thursday, DayOfWeek.Friday, DayOfWeek.Saturday, DayOfWeek.Sunday),
            self.TimeRules.At(9, 30),
            self.CheckRetraining
        )

    def CheckRetraining(self):
        """Verifie si retraining necessaire (tous les 60 jours)."""
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
        Entrainement initial sur la periode 2019-2022 (training set fixe).
        Utilise uniquement les donnees anterieures au backtest pour eviter data leakage.
        """
        # Recuperation historique depuis TRAIN_START
        history = self.History(self.symbol, self.TRAIN_START, self.TRAIN_END, Resolution.Daily)

        if history.empty or len(history) < 60:
            self.Debug("Pas assez d'historique pour l'entrainement initial.")
            return False

        closes = history['close'].values
        highs = history['high'].values
        lows = history['low'].values

        # Construction des features - STRICTEMENT walk-forward
        X_list, y_list = [], []
        for i in range(max(self.EMA_PERIODS) + 2, len(closes)):
            features = self._compute_features(closes, highs, lows, i)
            # Label: le prix monte de i-1 vers i (predire avec features jusqu'a i-1)
            label = 1 if closes[i] > closes[i-1] else 0
            X_list.append(features)
            y_list.append(label)

        if len(X_list) < 30:
            return False

        X_train = np.array(X_list)
        y_train = np.array(y_list)

        # Model regularization: reduce complexity to prevent overfitting
        # n_estimators=50 (from 100), max_depth=4 (from 5), min_samples_leaf=10 (new)
        self.model = RandomForestClassifier(
            n_estimators=50,
            max_depth=4,
            min_samples_leaf=10,
            random_state=42
        )
        self.model.fit(X_train, y_train)
        self.train_adx_min = float(X_train[:, 7].min())

        accuracy = self.model.score(X_train, y_train)
        self.Debug(f"Modele initial entraine (2019-2022): {len(X_train)} samples, accuracy={accuracy:.2%}")
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

        # Construction des features - STRICTEMENT walk-forward
        X_list, y_list = [], []
        for i in range(max(self.EMA_PERIODS) + 2, len(closes)):
            features = self._compute_features(closes, highs, lows, i)
            # Label: le prix monte de i-1 vers i (predire avec features jusqu'a i-1)
            label = 1 if closes[i] > closes[i-1] else 0
            X_list.append(features)
            y_list.append(label)

        if len(X_list) < 30:
            return False

        X_train = np.array(X_list)
        y_train = np.array(y_list)

        # Model regularization: reduce complexity to prevent overfitting
        self.model = RandomForestClassifier(
            n_estimators=50,
            max_depth=4,
            min_samples_leaf=10,
            random_state=42
        )
        self.model.fit(X_train, y_train)
        self.train_adx_min = float(X_train[:, 7].min())

        accuracy = self.model.score(X_train, y_train)
        self.Debug(f"Modele retrained ({lookback_days}j): {len(X_train)} samples, accuracy={accuracy:.2%}")
        return True

    def _compute_features(self, closes, highs, lows, i):
        """Calcule les features pour l'index i - STRICTEMENT walk-forward (pas de data leakage)."""
        # IMPORTANT: Toutes les features utilisent uniquement les donnees JUSQU'A i-1
        daily_ret = (closes[i-1] - closes[i-2]) / closes[i-2] if closes[i-2] > 0 else 0
        sma_20 = np.mean(closes[i-self.SMA_PERIOD:i])
        rsi_14 = self._compute_rsi(closes[i-self.RSI_PERIOD:i])
        ema_10 = self._ema(closes[:i], 10)
        ema_20 = self._ema(closes[:i], 20)
        ema_50 = self._ema(closes[:i], 50)
        ema_200 = self._ema(closes[:i], 200)
        adx_val = self._compute_adx(highs[i-self.ADX_PERIOD:i], lows[i-self.ADX_PERIOD:i], closes[i-self.ADX_PERIOD:i])
        atr_val = np.mean([highs[j] - lows[j] for j in range(max(0, i-self.ATR_PERIOD), i)])
        # Volatilite annuelle pour filtre
        vol_20 = np.std(closes[i-20:i]) / np.mean(closes[i-20:i]) * np.sqrt(252) if i >= 20 else 0
        return [sma_20, rsi_14, daily_ret, ema_10, ema_20, ema_50, ema_200, adx_val, atr_val, vol_20]

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

    def _trace(self):
        self.Plot("shadow", f"e{self.trace_count % 5}", self.Portfolio.TotalPortfolioValue)
        self.trace_count += 1

    def _buy_reference(self):
        if self.reference_bought:
            return
        # 0.98 : marge pour les frais d'un compte cash.
        self.SetHoldings(self.symbol, 0.98)
        self.reference_bought = True

    def _update_window(self, bar):
        """Barres journalieres pour features=train (#23504) : la fenetre est remplie
        une fois par History, avec la profondeur du re-entrainement, puis completee
        barre par barre."""
        if not self.window:
            history = self.History(self.symbol, self.RETRAIN_LOOKBACK_DAYS, Resolution.Daily)
            if not history.empty:
                times = history.index.get_level_values(-1)
                for t, c, h, l in zip(times, history['close'].values, history['high'].values, history['low'].values):
                    self.window.append((pd.Timestamp(t), float(c), float(h), float(l)))
        end = pd.Timestamp(bar.EndTime)
        ohlc = (float(bar.Close), float(bar.High), float(bar.Low))
        # La barre courante peut deja etre la derniere de l'historique : comparer aussi
        # les prix, pour ne pas la compter deux fois si les horodatages different.
        if not self.window or (self.window[-1][0] < end and self.window[-1][1:] != ohlc):
            self.window.append((end,) + ohlc)

    def OnData(self, slice: Slice):
        if not slice.Bars.ContainsKey(self.symbol):
            return

        bar = slice.Bars[self.symbol]
        current_price = bar.Close

        if self.IsWarmingUp:
            return

        if self.mode != "strategy":
            self._buy_reference()
            self._trace()
            return
        self._trace()
        if self.features_mode == "train":
            self._update_window(bar)

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

        # Calcul volatilite annuelle pour filtre (ATR/Price * sqrt(252))
        current_vol = (atr_val / current_price) * np.sqrt(252) if current_price > 0 else 0
        invested = self.Portfolio[self.symbol].Invested
        gate_on = current_vol > self.VOLATILITY_THRESHOLD
        if gate_on:
            self.gate_days += 1
            if invested:
                self.gate_days_invested += 1

        # FILTRE VOLATILITE: Skip trading si vol > 60% (recherche montre optimal).
        # legacy : le `return` saute aussi le stop, la prise de benefice et la sortie
        # du modele (#23504) ; entries : le filtre est applique a la branche d'achat.
        if gate_on and self.gate == "legacy":
            if invested and self.entry_price is not None:
                pnl_pct = (current_price - self.entry_price) / self.entry_price
                if pnl_pct <= -self.STOP_LOSS_PCT or pnl_pct >= self.TAKE_PROFIT_PCT:
                    self.suspended_breaches += 1
            self.Debug(f"{self.Time} => VOLATILITY FILTER: Skip (vol={current_vol:.1%} > {self.VOLATILITY_THRESHOLD:.0%})")
            return

        if self.features_mode == "train":
            # Meme fonction et meme profondeur d'historique qu'a l'entrainement (#23504).
            closes = np.array([b[1] for b in self.window])
            highs = np.array([b[2] for b in self.window])
            lows = np.array([b[3] for b in self.window])
            if len(closes) < max(self.EMA_PERIODS) + 2:
                return
            features = self._compute_features(closes, highs, lows, len(closes))
        else:
            features = [sma_val, rsi_val, daily_return, ema_10, ema_20, ema_50, ema_200, adx_val, atr_val, current_vol]
        X = np.array([features])
        self.predict_days += 1
        if self.train_adx_min is not None and features[7] < self.train_adx_min:
            self.adx_slot_below_train_min += 1

        # Prediction probabiliste
        proba = self.model.predict_proba(X)[0]  # [proba_down, proba_up]
        confidence_up = proba[1]  # Probabilite de hausse

        # Risk management - Stop-loss et Take-profit
        if self.Portfolio[self.symbol].Invested:
            if self.entry_price is not None:
                pnl_pct = (current_price - self.entry_price) / self.entry_price

                # Stop-loss a -8%
                if pnl_pct <= -self.STOP_LOSS_PCT:
                    self.Liquidate(self.symbol)
                    self.stop_exits += 1
                    self.gate_exits += int(gate_on)
                    self.Debug(f"{self.Time} => STOP-LOSS declenche @ {current_price:.2f} (PnL: {pnl_pct:.2%})")
                    self.entry_price = None
                    return

                # Take-profit a +15%
                if pnl_pct >= self.TAKE_PROFIT_PCT:
                    self.Liquidate(self.symbol)
                    self.tp_exits += 1
                    self.gate_exits += int(gate_on)
                    self.Debug(f"{self.Time} => TAKE-PROFIT declenche @ {current_price:.2f} (PnL: {pnl_pct:.2%})")
                    self.entry_price = None
                    return

        # Position sizing probabiliste avec enhanced trend filter
        if confidence_up > self.CONFIDENCE_LONG_THRESHOLD:
            # Signal LONG avec confiance elevee
            position_size = min(confidence_up, 1.0)

            # ENHANCED TREND FILTER: Multi-confirmation pour eviter faux signaux
            if current_price < ema_200:
                self.Debug(f"{self.Time} => TREND FILTER: Skip long (price {current_price:.2f} < EMA200 {ema_200:.2f})")
                return
            if rsi_val < 40:
                self.Debug(f"{self.Time} => RSI FILTER: Skip long (RSI {rsi_val:.1f} < 40, oversold)")
                return
            if adx_val < 20:
                self.Debug(f"{self.Time} => ADX FILTER: Skip long (ADX {adx_val:.1f} < 20, no trend)")
                return

            if not self.Portfolio[self.symbol].Invested:
                if gate_on:
                    return  # entries : pas d'entree un jour de filtre actif (#23504)
                # Account for transaction fees
                self.SetHoldings(self.symbol, position_size)
                self.entries += 1
                self.entry_price = current_price
                self.Debug(f"{self.Time} => LONG @ {current_price:.2f} | Confidence: {confidence_up:.2%} | Size: {position_size:.2%}")
            else:
                # Ajustement position si deja investi
                current_holdings = self.Portfolio[self.symbol].HoldingsValue / self.Portfolio.TotalPortfolioValue
                if abs(current_holdings - position_size) > 0.1:  # Rebalance si ecart > 10%
                    if gate_on and position_size > current_holdings:
                        return  # entries : pas de renforcement un jour de filtre actif (#23504)
                    self.SetHoldings(self.symbol, position_size)
                    self.Debug(f"{self.Time} => Rebalance @ {current_price:.2f} | New size: {position_size:.2%}")

        elif confidence_up < self.CONFIDENCE_EXIT_THRESHOLD:
            # Signal EXIT avec confiance faible de hausse (donc confiance elevee de baisse)
            if self.Portfolio[self.symbol].Invested:
                final_pnl = (current_price - self.entry_price) / self.entry_price if self.entry_price else 0
                self.Liquidate(self.symbol)
                self.model_exits += 1
                self.gate_exits += int(gate_on)
                self.Debug(f"{self.Time} => EXIT @ {current_price:.2f} | Confidence: {confidence_up:.2%} | Final PnL: {final_pnl:.2%}")
                self.entry_price = None

        else:
            # Zone d'incertitude (0.4 < confidence < 0.56) - Pas de trade
            pass

    def OnEndOfAlgorithm(self):
        # Statistiques d'execution #23504, lues par l'API (runtimeStatistics).
        for name in ("gate_days", "gate_days_invested", "suspended_breaches", "stop_exits",
                     "tp_exits", "model_exits", "gate_exits", "predict_days",
                     "adx_slot_below_train_min", "entries"):
            self.SetRuntimeStatistic(name, str(getattr(self, name)))
        self.SetRuntimeStatistic("model_source", self.model_source)
        if self.train_adx_min is not None:
            self.SetRuntimeStatistic("train_adx_min", f"{self.train_adx_min:.2f}")
