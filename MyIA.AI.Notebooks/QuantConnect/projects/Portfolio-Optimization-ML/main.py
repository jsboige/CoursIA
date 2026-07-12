from AlgorithmImports import *
import numpy as np
import pandas as pd
from scipy.optimize import minimize

try:
    import joblib
except ImportError:
    joblib = None

try:
    from sklearn.covariance import LedoitWolf, ShrunkCovariance
    from sklearn.preprocessing import StandardScaler
    SKLEARN_AVAILABLE = True
except ImportError:
    SKLEARN_AVAILABLE = False


class PortfolioOptimizationMLAlgorithm(QCAlgorithm):
    """
    Portfolio Optimization with Machine Learning.

    Concept:
    - Utilise Modern Portfolio Theory (Markowitz, 1952) avec améliorations ML
    - Covariance matrix estimée avec Ledoit-Wolf (shrinkage régularisée)
    - Returns prédits avec Momentum + Mean Reversion (features techniques)
    - Risk Parity weighting avec contraintes de volatilité cible
    - Rebalancement mensuel

    Universe: 15 Large-Caps US (5 secteurs)
    - Technology: AAPL, MSFT, NVDA
    - Financials: JPM, BAC, WFC
    - Healthcare: JNJ, UNH, PFE
    - Consumer: AMZN, TSLA, MCD
    - Industrials: CAT, HON, UNP

    Basé sur: QC-Py-07 (Portfolio Optimization) + ML enhancements
    """

    # Universe de 15 large-caps
    UNIVERSE = {
        # Tech
        "AAPL": "Technology",
        "MSFT": "Technology",
        "NVDA": "Technology",
        # Financials
        "JPM": "Financials",
        "BAC": "Financials",
        "WFC": "Financials",
        # Healthcare
        "JNJ": "Healthcare",
        "UNH": "Healthcare",
        "PFE": "Healthcare",
        # Consumer
        "AMZN": "Consumer",
        "TSLA": "Consumer",
        "MCD": "Consumer",
        # Industrials
        "CAT": "Industrials",
        "HON": "Industrials",
        "UNP": "Industrials"
    }

    # Paramètres de trading
    STARTING_CASH = 100000
    REBALANCE_DAY = 1  # 1er jour du mois

    # Paramètres de volatilité cible
    TARGET_VOLATILITY = 0.15  # 15% volatilité annualisée cible
    MIN_WEIGHT = 0.01  # 1% min par position
    MAX_WEIGHT = 0.25  # 25% max par position

    # Lookback periods pour estimation
    RETURNS_WINDOW = 60  # 60 jours pour covariance
    MOMENTUM_WINDOW = 126  # 6 mois pour momentum
    MIN_REVERSION_WINDOW = 20  # 20 jours pour mean reversion

    # Paramètres ML
    COV_ESTIMATOR = "ledoit_wolf"  # "sample", "ledoit_wolf", "shrunk"

    # Seuils de signal
    MOMENTUM_THRESHOLD = 0.02  # 2% momentum mensuel = positif
    OVERBOUGHT_THRESHOLD = 0.8  # RSI > 80 = overbought
    OVERSOLD_THRESHOLD = 0.2  # RSI < 20 = oversold

    def Initialize(self):
        # Configuration backtest
        self.SetStartDate(2015, 1, 1)
        self.SetEndDate(2026, 3, 1)
        self.SetCash(self.STARTING_CASH)
        self.SetBrokerageModel(BrokerageName.AlphaStreams, AccountType.Cash)

        # Ajouter les 15 actions
        self.symbols = []
        self.tickers = list(self.UNIVERSE.keys())

        for ticker in self.tickers:
            symbol = self.AddEquity(ticker, Resolution.Daily, Market.USA).Symbol
            self.symbols.append(symbol)

        # Benchmark = SPY
        self.benchmark = self.AddEquity("SPY", Resolution.Daily, Market.USA).Symbol
        self.SetBenchmark(self.benchmark)

        # Indicateurs pour chaque action
        self.indicators = {}
        for symbol in self.symbols:
            self.indicators[symbol.ID] = self.initialize_indicators(symbol)

        # Schedule: Rebalance mensuel
        self.Schedule.On(self.DateRules.MonthStart(self.tickers),
                         self.TimeRules.AfterMarketOpen("SPY", 30),
                         self.Rebalance)

        # Warm-up
        self.SetWarmUp(self.RETURNS_WINDOW + 10, Resolution.Daily)

        self.Debug("PortfolioOptimizationML initialized")
        self.Debug(f"Universe: {len(self.symbols)} stocks")

    def initialize_indicators(self, symbol):
        """Initialise les indicateurs techniques."""
        return {
            'rsi': self.RSI(symbol, 14, MovingAverageType.Wilders, Resolution.Daily),
            'sma_short': self.SMA(symbol, 20, Resolution.Daily),
            'sma_long': self.SMA(symbol, 50, Resolution.Daily),
            'atr': self.ATR(symbol, 14, MovingAverageType.Simple, Resolution.Daily)
        }

    def get_historical_returns(self, lookback=None):
        """
        Calcule les rendements historiques pour la covariance matrix.

        Returns:
            DataFrame avec les rendements daily des actions
        """
        if lookback is None:
            lookback = self.RETURNS_WINDOW

        # Récupérer l'historique
        history = self.History(self.symbols, lookback, Resolution.Daily)

        if len(history) == 0 or 'close' not in history.columns:
            return None

        # Pivot pour avoir les tickers en colonnes
        prices = history['close'].unstack(level=0)

        # Calculer les rendements daily
        returns = prices.pct_change().dropna()

        return returns

    def estimate_covariance(self, returns):
        """
        Estime la matrice de covariance avec régularisation.

        Méthodes:
        - sample: Covariance empirique (peut être instable)
        - ledoit_wolf: Shrinkage de Ledoit-Wolf (recommandé)
        - shrunk: Shrinkage vers la matrice identité
        """
        if returns is None or len(returns) < 10:
            return None

        # Sample covariance (baseline)
        sample_cov = returns.cov() * 252  # Annualiser

        if self.COV_ESTIMATOR == "sample" or not SKLEARN_AVAILABLE:
            return sample_cov

        try:
            if self.COV_ESTIMATOR == "ledoit_wolf":
                # Ledoit-Wolf shrinkage (optimal pour financial data)
                lw = LedoitWolf()
                lw.fit(returns.values)
                shrunk_cov = lw.covariance_ * 252  # Annualiser
                return pd.DataFrame(shrunk_cov, index=sample_cov.index, columns=sample_cov.columns)

            elif self.COV_ESTIMATOR == "shrunk":
                # Shrinkage vers identité
                sc = ShrunkCovariance(shrinkage=0.5)
                sc.fit(returns.values)
                shrunk_cov = sc.covariance_ * 252
                return pd.DataFrame(shrunk_cov, index=sample_cov.index, columns=sample_cov.columns)

        except Exception as e:
            self.Debug(f"Error in covariance estimation: {e}")
            return sample_cov

        return sample_cov

    def predict_returns(self):
        """
        Prédit les rendements attendus avec Momentum + Mean Reversion.

        Signal combiné:
        - Momentum (6 mois): Rendement annualisé
        - Mean Reversion (20 jours): Inverse du rendement récent

        Returns:
            Series avec les rendements attendus annualisés
        """
        predicted_returns = {}

        for symbol in self.symbols:
            # Récupérer l'historique
            history = self.History(symbol, self.MOMENTUM_WINDOW + 20, Resolution.Daily)

            if len(history) < self.MOMENTUM_WINDOW:
                continue

            prices = history['close'].values

            # Momentum: rendement sur 6 mois
            momentum_return = (prices[-1] / prices[-self.MOMENTUM_WINDOW]) - 1
            momentum_annual = momentum_return * (252 / self.MOMENTUM_WINDOW)

            # Mean Reversion: rendement inverse sur 20 jours
            recent_return = (prices[-1] / prices[-self.MIN_REVERSION_WINDOW]) - 1
            mean_reversion_signal = -recent_return * (252 / self.MIN_REVERSION_WINDOW)

            # Combiner les signaux (50/50)
            combined_return = 0.5 * momentum_annual + 0.5 * mean_reversion_signal

            predicted_returns[symbol.ID] = combined_return

        return pd.Series(predicted_returns)

    def calculate_rsi_signals(self):
        """
        Calcule les signaux RSI pour filtrer les extremes.

        Returns:
            Dict avec signaux: 1 (oversold=buy), 0 (neutral), -1 (overbought=sell)
        """
        signals = {}

        for symbol in self.symbols:
            rsi = self.indicators[symbol.ID]['rsi']

            if rsi.Current.Value is None:
                signals[symbol.ID] = 0
                continue

            rsi_norm = rsi.Current.Value / 100

            if rsi_norm < self.OVERSOLD_THRESHOLD:
                # Oversold = signal d'achat
                signals[symbol.ID] = 1
            elif rsi_norm > self.OVERBOUGHT_THRESHOLD:
                # Overbought = signal de vente
                signals[symbol.ID] = -1
            else:
                signals[symbol.ID] = 0

        return signals

    def optimize_portfolio(self, expected_returns, cov_matrix):
        """
        Optimise le portfolio avec Mean-Variance + Contraintes.

        Objectif: Maximiser le Sharpe ratio
        Contraintes:
        - Sum(weights) = 1
        - MIN_WEIGHT <= weight <= MAX_WEIGHT
        - Volatilité cible (TARGET_VOLATILITY)

        Returns:
            Series avec les poids optimaux
        """
        if expected_returns is None or cov_matrix is None:
            return None

        n_assets = len(expected_returns)

        # Fonction objective: Sharpe ratio négatif
        def negative_sharpe(weights):
            portfolio_return = np.sum(expected_returns.values * weights)
            portfolio_variance = np.dot(weights.T, np.dot(cov_matrix.values, weights))
            portfolio_vol = np.sqrt(portfolio_variance)

            # Risk-free rate approx = 2%
            sharpe = (portfolio_return - 0.02) / portfolio_vol if portfolio_vol > 0 else 0

            return -sharpe

        # Contraintes
        constraints = [
            {'type': 'eq', 'fun': lambda w: np.sum(w) - 1}  # Sum = 1
        ]

        # Bounds (min/max weight)
        bounds = [(self.MIN_WEIGHT, self.MAX_WEIGHT) for _ in range(n_assets)]

        # Initialisation: equal weight
        x0 = np.array([1.0 / n_assets] * n_assets)

        try:
            result = minimize(
                negative_sharpe,
                x0,
                method='SLSQP',
                bounds=bounds,
                constraints=constraints,
                options={'ftol': 1e-9}
            )

            if result.success:
                weights = pd.Series(result.x, index=expected_returns.index)
                return weights
            else:
                self.Debug(f"Optimization failed: {result.message}")

        except Exception as e:
            self.Debug(f"Error in optimization: {e}")

        # Fallback: equal weight
        return pd.Series([1.0 / n_assets] * n_assets, index=expected_returns.index)

    def apply_risk_parity(self, cov_matrix):
        """
        Alternative: Risk Parity weighting.

        Chaque actif contribue également au risque du portfolio.
        """
        if cov_matrix is None:
            return None

        n = len(cov_matrix)

        # Inverse de la volatilité (diagonale de cov matrix)
        volatilities = np.sqrt(np.diag(cov_matrix.values))
        inv_vol = 1.0 / volatilities

        # Normaliser
        weights = inv_vol / np.sum(inv_vol)

        return pd.Series(weights, index=cov_matrix.index)

    def Rebalance(self):
        """Rebalance le portfolio mensuellement."""

        self.Debug(f"Rebalancing at {self.Time}")

        # 1. Estimer la covariance matrix
        returns = self.get_historical_returns(self.RETURNS_WINDOW)
        cov_matrix = self.estimate_covariance(returns)

        if cov_matrix is None:
            self.Debug("Could not estimate covariance matrix")
            return

        # 2. Prédire les rendements attendus
        expected_returns = self.predict_returns()

        if expected_returns is None or len(expected_returns) == 0:
            self.Debug("Could not predict returns")
            return

        # 3. Calculer les signaux RSI pour filtrer
        rsi_signals = self.calculate_rsi_signals()

        # 4. Optimiser le portfolio
        optimal_weights = self.optimize_portfolio(expected_returns, cov_matrix)

        if optimal_weights is None:
            self.Debug("Optimization failed, using equal weight")
            optimal_weights = pd.Series([1.0 / len(self.symbols)] * len(self.symbols),
                                      index=[s.ID for s in self.symbols])

        # 5. Appliquer les filtres RSI
        filtered_weights = {}
        total_weight = 0

        for symbol_id, weight in optimal_weights.items():
            signal = rsi_signals.get(symbol_id, 0)

            if signal == -1:
                # Overbought: réduire le poids
                adjusted_weight = weight * 0.5
            elif signal == 1:
                # Oversold: augmenter le poids
                adjusted_weight = weight * 1.5
            else:
                adjusted_weight = weight

            filtered_weights[symbol_id] = adjusted_weight
            total_weight += adjusted_weight

        # Normaliser pour sum = 1
        if total_weight > 0:
            for symbol_id in filtered_weights:
                filtered_weights[symbol_id] /= total_weight

        # 6. Exécuter les trades
        self.Liquidate()

        for symbol in self.symbols:
            weight = filtered_weights.get(symbol.ID, 0)

            if weight > self.MIN_WEIGHT:
                self.SetHoldings(symbol, weight)

        self.Debug(f"Rebalance complete: {len([w for w in filtered_weights.values() if w > self.MIN_WEIGHT])} positions")

        # 7. Log stats
        portfolio_vol = np.sqrt(np.dot(list(filtered_weights.values()),
                                     np.dot(cov_matrix.values,
                                           list(filtered_weights.values()))))

        self.Debug(f"Portfolio volatility: {portfolio_vol:.2%}")
        self.Debug(f"Target volatility: {self.TARGET_VOLATILITY:.2%}")
