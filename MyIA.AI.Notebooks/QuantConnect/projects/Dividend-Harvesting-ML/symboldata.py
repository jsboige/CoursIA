# region imports
from AlgorithmImports import *

from sklearn.tree import DecisionTreeRegressor
# endregion


class SymbolData:
    """Per-symbol data container for dividend yield prediction.

    Stores rolling windows of fundamental factors and dividend labels,
    trains a DecisionTreeRegressor to predict next dividend yield.
    """

    def __init__(self, lookback_length=25, minimum_samples=10):
        self._lookback_length = lookback_length
        self._minimum_samples = minimum_samples

        # Rolling windows for factors.
        self._factor_timestamps = []
        self._factor_names = [
            'pe_ratio', 'revenue_growth', 'free_cash_flow_pct',
            'dividend_payout_ratio', 'current_ratio'
        ]
        self._factor_history = {
            name: RollingWindow[float](lookback_length)
            for name in self._factor_names
        }
        self._last_file_date = datetime.min

        # Rolling window for labels (dividend yields).
        self._label_timestamps = []
        self._label_history = RollingWindow[float](lookback_length)

        # ML model.
        self._model = DecisionTreeRegressor(random_state=0)

    def update_factors(self, fundamental):
        f = fundamental
        file_date = max(
            f.financial_statements.file_date.three_months,
            f.financial_statements.file_date.twelve_months
        )
        if file_date <= self._last_file_date:
            return
        self._last_file_date = file_date

        self._factor_timestamps.append(f.end_time)
        self._factor_timestamps = self._factor_timestamps[
            -self._lookback_length:
        ]

        cf = f.financial_statements.cash_flow_statement
        income = f.financial_statements.income_statement
        factor_values = {
            'pe_ratio': f.valuation_ratios.pe_ratio,
            'revenue_growth':
                f.operation_ratios.revenue_growth.three_months,
            'free_cash_flow_pct': (
                cf.free_cash_flow.three_months
                / cf.operating_cash_flow.three_months
            ) if cf.operating_cash_flow.three_months else 0,
            'dividend_payout_ratio': (
                -cf.cash_dividends_paid.three_months
                / income.net_income.three_months
            ) if income.net_income.three_months else 0,
            'current_ratio':
                f.operation_ratios.current_ratio.three_months
        }
        for name, value in factor_values.items():
            self._factor_history[name].add(value)

    def update_labels(self, dividend):
        t = dividend.end_time
        if t in self._label_timestamps:
            return
        self._label_timestamps.append(t)
        self._label_history.Add(
            dividend.distribution / dividend.reference_price
        )

    def train(self):
        if (len(self._factor_timestamps) < self._minimum_samples or
                len(self._label_timestamps) < self._minimum_samples):
            return None

        # Align factors and labels with two cases:
        # Case 1: Multiple factors before a label -> map each to label
        # Case 2: One factor before multiple labels -> map to each
        timestamps = []
        for i, label_ts in enumerate(self._label_timestamps):
            prev_label_ts = (
                self._label_timestamps[i - 1] if i > 0 else datetime.min
            )
            factor_ts_between = [
                t for t in self._factor_timestamps
                if prev_label_ts <= t < label_ts
            ]
            if factor_ts_between:
                for ft in factor_ts_between:
                    timestamps.append((ft, label_ts))
            else:
                earlier = [
                    t for t in self._factor_timestamps if t < label_ts
                ]
                if earlier:
                    timestamps.append((max(earlier), label_ts))

        # Build training data.
        X = np.ndarray((len(timestamps), len(self._factor_names)))
        y = []
        for row_idx, (factor_time, label_time) in enumerate(timestamps):
            for col_idx, name in enumerate(self._factor_names):
                rw_idx = (
                    len(self._factor_timestamps)
                    - self._factor_timestamps.index(factor_time)
                    - 1
                )
                X[row_idx, col_idx] = self._factor_history[name][rw_idx]
            rw_idx = (
                len(self._label_timestamps)
                - self._label_timestamps.index(label_time)
                - 1
            )
            y.append(self._label_history[rw_idx])
        y = np.array(y)

        if len(y) < self._minimum_samples:
            return None

        self._model.fit(X, y)
        return self._model.score(X, y)

    def predict(self):
        latest = [
            self._factor_history[name][0]
            for name in self._factor_names
        ]
        return self._model.predict([latest])[0]
