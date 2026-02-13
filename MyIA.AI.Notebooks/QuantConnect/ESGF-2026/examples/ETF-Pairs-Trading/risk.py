# region imports
from AlgorithmImports import *
#endregion

class TrailingStopRiskManagementModel(RiskManagementModel):
    def __init__(self, stop_loss_percentage=0.08):
        self.stop_loss_percentage = stop_loss_percentage

    def ManageRisk(self, algorithm, targets):
        risk_adjusted_targets = []
        for kvp in algorithm.Portfolio:
            symbol = kvp.Key
            security = kvp.Value
            if security.Invested:
                if security.IsLong:
                    stop_price = security.AveragePrice * (1 - self.stop_loss_percentage)
                    if security.Price < stop_price:
                        algorithm.Log(f"[Risk] Liquidating LONG {symbol} at {security.Price:.2f}, Stop={stop_price:.2f}")
                        risk_adjusted_targets.append(PortfolioTarget(symbol, 0))
                if security.IsShort:
                    stop_price = security.AveragePrice * (1 + self.stop_loss_percentage)
                    if security.Price > stop_price:
                        algorithm.Log(f"[Risk] Liquidating SHORT {symbol} at {security.Price:.2f}, Stop={stop_price:.2f}")
                        risk_adjusted_targets.append(PortfolioTarget(symbol, 0))
        return risk_adjusted_targets
