# region imports
from AlgorithmImports import *
class CustomImmediateExecutionModel(ImmediateExecutionModel):
    def __init__(self, leverage=2.0):
        self.leverage = leverage

    def Execute(self, algorithm, targets):
        leverage = self.leverage
        for target in targets:
            if target.Symbol in algorithm.Portfolio:
                holding = algorithm.Portfolio[target.Symbol].Quantity
            else:
                holding = 0
            target_quantity = target.Quantity * leverage
            adjustment = target_quantity - holding
            if target_quantity == 0:
                algorithm.Liquidate(target.Symbol, tag="Liquidate")
            elif adjustment > 0:
                if holding == 0:
                    tag = "new position"
                else:
                    tag = "Upsizing position"
                algorithm.MarketOrder(target.Symbol, adjustment, tag=tag)
            elif adjustment < 0:
                tag = "downsizing position"
                algorithm.MarketOrder(target.Symbol, adjustment, tag=tag)
