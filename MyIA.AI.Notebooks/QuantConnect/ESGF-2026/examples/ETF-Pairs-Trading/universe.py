#region imports
from AlgorithmImports import *
#endregion

class SectorETFUniverseSelectionModel(ETFConstituentsUniverseSelectionModel):
    def __init__(self, universe_settings: UniverseSettings = None) -> None:
        symbol = Symbol.Create("IYM", SecurityType.Equity, Market.USA)
        super().__init__(symbol, universe_settings, self.etf_constituents_filter)

    def etf_constituents_filter(self, constituents: List[ETFConstituentData]) -> List[Symbol]:
        selected = sorted(
            [c for c in constituents if c.Weight],
            key=lambda c: c.Weight,
            reverse=True
        )
        return [c.Symbol for c in selected[:10]]
