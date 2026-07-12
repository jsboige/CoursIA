# region imports
from AlgorithmImports import *
from piotroski_score import PiotroskiScore
from piotroski_factors import PiotroskiFactors
# endregion


class SymbolData:

    _piotroski_score = PiotroskiScore()

    def __init__(self, fundamental):
        self.is_ready = False
        self.score = None
        self._period_ending_date = datetime.min
        self._factors = RollingWindow(3)
        self.update(fundamental)

    def update(self, fundamental):
        period_ending_date = fundamental.financial_statements.period_ending_date.twelve_months
        # If a new 10K hasn't been released yet...
        if self._period_ending_date == period_ending_date:
            # If it's been 5 months since the previous fiscal year, rebalance this asset.
            if (self._factors.is_ready and
                (fundamental.end_time - self._period_ending_date).days > 5*30):
                self.score = self._piotroski_score.get_score(self._factors)
                self.is_ready = True
        # When a new 10K is released, add the fundamental data to the RollingWindow.
        elif PiotroskiFactors.are_available(fundamental):
            # If we've missed a 10K, reset the RollingWindow.
            if period_ending_date.year - self._period_ending_date.year > 1:
                self._factors.reset()
                self.is_ready = False
            self._factors.add(PiotroskiFactors(fundamental))
            self._period_ending_date = period_ending_date
        return self.is_ready
