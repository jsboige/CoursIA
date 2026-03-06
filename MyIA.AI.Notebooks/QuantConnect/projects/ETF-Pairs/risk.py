# region imports
from AlgorithmImports import *
#endregion

class TrailingStopRiskManagementModel(RiskManagementModel):
    """
    Spread-level risk management for pairs trading.

    IMPORTANT: Per-leg stops break market neutrality. If one leg is stopped but not the other,
    the strategy becomes directional (unintended exposure).

    This implementation disables per-leg stops and relies on:
    1. Alpha model's z-score exit logic (mean-reversion complete)
    2. Insight duration expiry (adaptive based on half-life)
    3. Spread-level monitoring (future enhancement)
    """

    def __init__(self, stop_loss_percentage=0.08):
        self.stop_loss_percentage = stop_loss_percentage

    def ManageRisk(self, algorithm, targets):
        return []
