# region imports
from AlgorithmImports import *
class MyPcm(RiskParityPortfolioConstructionModel):
    def __init__(self, rebalance):
        super().__init__(rebalance)

    def CreateTargets(self, algorithm, insights):
        targets = super().CreateTargets(algorithm, insights)
        for target in targets:
            if target.Quantity != 0:
                security = algorithm.Securities[target.Symbol]
                security.SetLeverage(2)
        return targets
