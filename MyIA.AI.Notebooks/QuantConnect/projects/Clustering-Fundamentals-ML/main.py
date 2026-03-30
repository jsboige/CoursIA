# region imports
from AlgorithmImports import *

from sklearn.decomposition import PCA
from sklearn.preprocessing import StandardScaler
from sklearn.ensemble import GradientBoostingRegressor
# endregion


class ClusteringFundamentalsAlgorithm(QCAlgorithm):
    """
    Hands-On AI Trading - Ch06 Ex10: Stock Selection through
    Clustering Fundamental Data.

    Uses 100 fundamental factors, PCA for dimensionality reduction,
    and a learning-to-rank model to select stocks expected to
    outperform. Monthly rebalance with equal-weight portfolio of
    top-ranked assets.

    Original uses LGBMRanker; this version uses GradientBoostingRegressor
    as a ranking proxy (sklearn-compatible for QC Cloud).

    Universe: Top 100 by dollar volume.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 3, 1)
        self.set_cash(100_000)
        self.settings.daily_precise_end_time = False

        self._liquid_universe_size = self.get_parameter(
            'liquid_universe_size', 100
        )
        self._final_universe_size = self.get_parameter(
            'final_universe_size', 10
        )
        self._lookback_period = timedelta(
            self.get_parameter('lookback_period', 365)
        )
        self._components = self.get_parameter('components', 5)
        self._prediction_period = 22
        self._factors = [
            "market_cap",
            "operation_ratios.revenue_growth.value",
            "operation_ratios.operation_income_growth.value",
            "operation_ratios.net_income_growth.value",
            "operation_ratios.gross_margin.value",
            "operation_ratios.operation_margin.value",
            "operation_ratios.net_margin.value",
            "operation_ratios.current_ratio.value",
            "operation_ratios.quick_ratio.value",
            "operation_ratios.financial_leverage.value",
            "operation_ratios.total_debt_equity_ratio.value",
            "operation_ratios.assets_turnover.value",
            "operation_ratios.roe.value",
            "valuation_ratios.pe_ratio",
            "valuation_ratios.ps_ratio",
            "valuation_ratios.pcf_ratio",
            "valuation_ratios.book_value_yield",
            "valuation_ratios.earning_yield",
            "valuation_ratios.fcf_yield",
            "valuation_ratios.trailing_dividend_yield",
            "valuation_ratios.forward_pe_ratio",
            "valuation_ratios.peg_ratio",
            "valuation_ratios.ev_to_ebitda",
            "valuation_ratios.ev_to_revenue",
            "valuation_ratios.price_to_cash_ratio",
            "company_profile.enterprise_value"
        ]

        schedule_symbol = Symbol.create(
            "SPY", SecurityType.EQUITY, Market.USA
        )
        date_rule = self.date_rules.month_start(schedule_symbol)
        self.schedule.on(
            date_rule,
            self.time_rules.after_market_open(schedule_symbol, 1),
            self._trade
        )

        self._scaler = StandardScaler()
        self._pca = PCA(n_components=self._components, random_state=0)
        self.universe_settings.schedule.on(date_rule)
        self._universe = self.add_universe(self._select_assets)

    def _select_assets(self, fundamental):
        selected = sorted(
            [f for f in fundamental if f.has_fundamental_data],
            key=lambda f: f.dollar_volume
        )[-self._liquid_universe_size:]
        liquid_symbols = [f.symbol for f in selected]

        # Get factors history.
        factors_by_symbol = {
            symbol: pd.DataFrame(columns=self._factors)
            for symbol in liquid_symbols
        }
        history = self.history[Fundamental](
            liquid_symbols,
            self._lookback_period + timedelta(2)
        )
        for fundamental_dict in history:
            for symbol, f in fundamental_dict.items():
                factor_values = []
                for factor in self._factors:
                    factor_values.append(eval(f"f.{factor}"))
                t = f.end_time
                factors_by_symbol[symbol].loc[t] = factor_values

        # Filter factors with too many NaN values.
        all_non_nan_factors = []
        tradable_symbols = []
        for symbol, factor_df in factors_by_symbol.items():
            non_nan = set(factor_df.dropna(axis=1).columns)
            if len(non_nan) < 10:
                continue
            tradable_symbols.append(symbol)
            all_non_nan_factors.append(non_nan)

        if not all_non_nan_factors:
            return []
        factors_to_use = all_non_nan_factors[0]
        for x in all_non_nan_factors[1:]:
            factors_to_use = factors_to_use.intersection(x)
        factors_to_use = sorted(list(factors_to_use))
        self.plot("Factors", "Count", len(factors_to_use))

        if len(factors_to_use) < 3:
            return tradable_symbols[:self._final_universe_size]

        # Get training labels.
        history = self.history(
            tradable_symbols,
            self._lookback_period + timedelta(1),
            Resolution.DAILY
        )
        label_by_symbol = {}
        for symbol in tradable_symbols[:]:
            if symbol not in history.index:
                tradable_symbols.remove(symbol)
                continue
            open_prices = history.loc[symbol]['open'].shift(-1)
            label_by_symbol[symbol] = open_prices.pct_change(
                self._prediction_period
            ).shift(-self._prediction_period).dropna()

        # Build factor matrix and label vector.
        x_train = pd.DataFrame()
        y_df = pd.DataFrame()
        for symbol in tradable_symbols:
            labels = label_by_symbol[symbol]
            factors = factors_by_symbol[symbol][factors_to_use].reindex(
                labels.index
            ).ffill()
            x_train = pd.concat([x_train, factors])
            y_df[symbol] = labels
        x_train = x_train.sort_index()

        # Apply PCA with dynamic n_components.
        n_features = len(factors_to_use)
        n_samples = len(x_train)
        n_comp = min(self._components, n_features, n_samples)
        if n_comp < 2:
            return tradable_symbols[:self._final_universe_size]
        try:
            pca = PCA(n_components=n_comp, random_state=0)
            x_pca = pca.fit_transform(
                self._scaler.fit_transform(x_train)
            )
        except Exception:
            return tradable_symbols[:self._final_universe_size]

        # Use returns directly as regression target.
        y_train = y_df.values.flatten()
        y_train = y_train[~np.isnan(y_train)]

        if len(y_train) < 20 or len(x_pca) != len(y_train):
            return tradable_symbols[:self._final_universe_size]

        # Train GBR as ranking proxy.
        model = GradientBoostingRegressor(
            n_estimators=50, max_depth=3,
            learning_rate=0.05, random_state=0
        )
        model.fit(x_pca, y_train)

        # Predict ranking for current period.
        x_current = pd.DataFrame()
        for symbol in tradable_symbols:
            x_current = pd.concat(
                [x_current,
                 factors_by_symbol[symbol][factors_to_use].iloc[-1:]]
            )
        try:
            predictions = model.predict(
                pca.transform(
                    self._scaler.transform(x_current)
                )
            )
        except Exception:
            return tradable_symbols[:self._final_universe_size]

        prediction_by_symbol = {
            tradable_symbols[i]: pred
            for i, pred in enumerate(predictions)
        }

        sorted_predictions = sorted(
            prediction_by_symbol.items(), key=lambda x: x[1]
        )
        return [
            x[0]
            for x in sorted_predictions[-self._final_universe_size:]
        ]

    def _trade(self):
        if not self._universe.selected:
            return
        weight = 1 / len(self._universe.selected)
        self.set_holdings(
            [
                PortfolioTarget(symbol, weight)
                for symbol in self._universe.selected
            ],
            True
        )
