# region imports
from AlgorithmImports import *
from symbol_data import SymbolData
from piotroski_factors import PiotroskiFactors
# endregion


class PiotroskiScoreUniverseSelectionModel(FundamentalUniverseSelectionModel):

    def __init__(self, algorithm, threshold, max_universe_size=100):
        super().__init__(self._select_assets)
        self._algorithm = algorithm
        self._threshold = threshold
        self._max_universe_size = max_universe_size
        self._symbol_data_by_symbol = {}

    def _select_assets(self, fundamentals):
        # Update the Piotroski factors of all assets.
        for f in fundamentals:
            if f.symbol not in self._symbol_data_by_symbol:
                self._symbol_data_by_symbol[f.symbol] = SymbolData(f)
            else:
                self._symbol_data_by_symbol[f.symbol].update(f)
        # We only want stocks with fundamental data and price > $1.
        filtered = [
            f for f in fundamentals
            if (f.has_fundamental_data and
                f.price > 1 and
                f.dollar_volume > 100_000 and
                not np.isnan(f.valuation_ratios.pb_ratio))
        ]
        # Select the 20% of firms with the greatest Book-to-Market ratio.
        filtered = sorted(
            filtered, key=lambda f: 1 / f.valuation_ratios.pb_ratio
        )[-int(0.2*len(filtered)):]
        # Get the f-scores of all firms that passed the preceding filters.
        f_scores = {}
        for f in filtered:
            symbol_data = self._symbol_data_by_symbol[f.symbol]
            if symbol_data.is_ready:
                f_scores[f.symbol] = symbol_data.score
        # Wait until we have sufficient history.
        if self._algorithm.is_warming_up:
            return []
        # Modified:
        # Select stocks with the highest F-Score, and take the top 100:
        top_symbols = [
            symbol for symbol, score in sorted(
                f_scores.items(), key=lambda x: x[1], reverse=True
            ) if score >= self._threshold
        ][:self._max_universe_size]
        self._algorithm.plot('F-Scores', 'Total', len(f_scores))
        self._algorithm.plot('F-Scores', 'Above Thresold', len(top_symbols))
        return top_symbols

        # Original Paper:
        # Select ALL stocks over the threshold.
        #return [symbol for symbol, fscore in f_scores.items() if fscore >= self._threshold]
