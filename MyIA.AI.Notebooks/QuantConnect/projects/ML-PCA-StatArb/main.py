#region imports
from AlgorithmImports import *

from sklearn.decomposition import PCA
from sklearn.linear_model import LinearRegression
# endregion
# Hands-On AI Trading - Ex13: PCA Statistical Arbitrage Mean Reversion
# Uses PCA to extract principal components from a universe of stocks, fits OLS
# regression for each stock using the components, then trades mean-reversion
# on the residuals when Z-scores exceed the threshold.
# Source: HandsOnAITradingBook, Section 06, Example 13


class PCAStatArbitrageAlgorithm(QCAlgorithm):
    """
    PCA Statistical Arbitrage Mean Reversion.

    This strategy uses principal component analysis and linear regression
    to perform statistical arbitrage. Mean-reversion models exploit pricing
    inefficiencies between groups of correlated securities.

    Reference: Hands-On AI Trading with Python, QuantConnect, and AWS
    Chapter 06 - Applied Machine Learning, Example 13

    How it works:
    1. Select top stocks by dollar volume from a universe
    2. Calculate principal components from log prices
    3. Fit OLS regression for each stock using PCA factors
    4. Compute z-scores of residuals (deviation from model)
    5. Enter mean-reversion trades on stocks with extreme z-scores

    Parameters:
    - num_components: Number of PCA components (default: 3)
    - lookback_days: Historical window for PCA fitting (default: 60)
    - z_score_threshold: Minimum z-score to trade (default: 1.5)
    - universe_size: Number of stocks in universe (default: 100)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 1, 1)
        self.set_cash(1_000_000)
        self.settings.minimum_order_margin_portfolio_percentage = 0

        self._num_components = self.get_parameter("num_components", 3)
        self._lookback = self.get_parameter("lookback_days", 60)
        self._z_score_threshold = self.get_parameter("z_score_threshold", 1.5)
        self._universe_size = self.get_parameter("universe_size", 100)

        schedule_symbol = Symbol.create("SPY", SecurityType.EQUITY, Market.USA)
        date_rule = self.date_rules.month_start(schedule_symbol)
        self.universe_settings.schedule.on(date_rule)
        self.universe_settings.data_normalization_mode = (
            DataNormalizationMode.RAW
        )
        self._universe = self.add_universe(self._select_assets)

        self.schedule.on(
            date_rule,
            self.time_rules.after_market_open(schedule_symbol, 1),
            self._trade
        )

        chart = Chart('Explained Variance Ratio')
        self.add_chart(chart)
        for i in range(self._num_components):
            chart.add_series(
                Series(f"Component {i}", SeriesType.LINE, "")
            )

    def _select_assets(self, fundamental):
        """Select top stocks by dollar volume above $5."""
        return [
            f.symbol
            for f in sorted(
                [f for f in fundamental if f.price > 5],
                key=lambda f: f.dollar_volume
            )[-self._universe_size:]
        ]

    def _trade(self):
        """Execute PCA stat-arb trading logic."""
        tradeable_assets = [
            symbol
            for symbol in self._universe.selected
            if (self.securities[symbol].price and
                symbol in self.current_slice.quote_bars)
        ]

        if len(tradeable_assets) < 10:
            return

        # Get historical close prices, scaled for splits/dividends
        history = self.history(
            tradeable_assets, self._lookback, Resolution.DAILY,
            data_normalization_mode=DataNormalizationMode.SCALED_RAW
        ).close.unstack(level=0)

        if history.empty or history.shape[0] < 20:
            return

        # Compute portfolio weights via PCA stat-arb
        weights = self._get_weights(history)

        if isinstance(weights, dict) and not weights:
            return
        if hasattr(weights, 'empty') and weights.empty:
            return

        # Enter mean-reversion positions (negative weights = contrarian)
        self.set_holdings(
            [
                PortfolioTarget(symbol, -weight)
                for symbol, weight in weights.items()
            ],
            True
        )

    def _get_weights(self, history):
        """
        Compute portfolio weights from PCA residuals.

        Steps:
        1. Log-transform and center prices
        2. Fit PCA to extract principal components
        3. Fit OLS per stock using PCA factors
        4. Compute z-scores of residuals
        5. Select stocks with extreme negative z-scores
        """
        # Log-transform and center
        sample = np.log(history.dropna(axis=1))
        if sample.empty or sample.shape[1] < self._num_components:
            return {}
        sample -= sample.mean()

        # Fit PCA
        pca_model = PCA().fit(sample)

        # Plot explained variance
        for i in range(self._num_components):
            self.plot(
                'Explained Variance Ratio', f"Component {i}",
                pca_model.explained_variance_ratio_[i]
            )

        # Project onto principal components
        factors = np.dot(sample, pca_model.components_.T)[
            :, :self._num_components
        ]

        # Fit OLS for each stock using sklearn LinearRegression
        # (replaces statsmodels OLS to avoid dependency issues on QC Cloud)
        residuals = {}
        for ticker in sample.columns:
            model = LinearRegression()
            model.fit(factors, sample[ticker])
            predictions = model.predict(factors)
            residuals[ticker] = sample[ticker] - predictions

        resids = pd.DataFrame(residuals)

        # Compute z-scores (standardize residuals)
        zscores = (
            (resids - resids.mean()) / resids.std()
        ).iloc[-1]

        # Select stocks far below mean (for mean reversion)
        selected = zscores[zscores < -self._z_score_threshold]

        if selected.empty:
            return {}

        # Weight proportional to z-score deviation
        weights = selected * (1 / selected.abs().sum())
        return weights.sort_values()

    def on_data(self, data):
        pass
