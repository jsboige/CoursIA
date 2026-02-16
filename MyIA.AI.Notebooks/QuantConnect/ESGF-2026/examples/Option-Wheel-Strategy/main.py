# region imports
from AlgorithmImports import *
# endregion


class WheelStrategyAlgorithm(QCAlgorithm):

    def Initialize(self):
        self.SetStartDate(2020, 6, 1)
        self.SetCash(1_000_000)
        self.backtest_resolution = Resolution.Minute
        self.is_live = self.LiveMode
        resolution = Resolution.Minute if self.is_live else self.backtest_resolution
        self.Debug(f"Mode {'Live' if self.is_live else 'Backtest'}, resolution : {resolution}")
        self.SetBrokerageModel(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.Cash)
        self.DefaultOrderProperties = InteractiveBrokersOrderProperties()
        self.DefaultOrderProperties.TimeInForce = TimeInForce.GoodTilCanceled
        self.DefaultOrderProperties.OutsideRegularTradingHours = False
        self.SetSecurityInitializer(
            BrokerageModelSecurityInitializer(
                self.BrokerageModel,
                FuncSecuritySeeder(self.GetLastKnownPrices)
            )
        )
        self._equity = self.AddEquity(
            "SPY",
            resolution=resolution,
            dataNormalizationMode=DataNormalizationMode.Raw
        )
        self.SetBenchmark("SPY")
        self.days_to_expiry = int(self.GetParameter("days_to_expiry", 30))
        self.otm_threshold = float(self.GetParameter("otm_threshold", 0.05))
        self.max_exposure_fraction = float(self.GetParameter("max_exposure_fraction", 1.0))
        self.disable_margin = bool(self.GetParameter("disable_margin", 1))

    def _get_target_contract(self, right, target_price):
        contract_symbols = self.OptionChainProvider.GetOptionContractList(self._equity.Symbol, self.Time)
        if not contract_symbols:
            self.Debug(f"Aucun contrat disponible pour {self._equity.Symbol} a {self.Time}.")
            return None
        future_dates = [s.ID.Date for s in contract_symbols if s.ID.Date.date() > self.Time.date() + timedelta(self.days_to_expiry)]
        if not future_dates:
            self.Debug("Aucune expiration disponible au-dela de la periode demandee.")
            return None
        expiry = min(future_dates)
        filtered_symbols = (
            [s for s in contract_symbols if s.ID.Date == expiry and s.ID.OptionRight == right and
             (s.ID.StrikePrice <= target_price if right == OptionRight.PUT else s.ID.StrikePrice >= target_price)]
        )
        filtered_symbols = sorted(filtered_symbols, key=lambda s: s.ID.StrikePrice, reverse=(right == OptionRight.PUT))
        if not filtered_symbols:
            self.Debug(f"Aucun contrat trouve pour {right} autour de {target_price:.2f} avec expiration {expiry}.")
            return None
        symbol = filtered_symbols[0]
        self.AddOptionContract(symbol)
        return symbol

    def _validate_order(self, required_exposure, order_type="PUT"):
        available_cash = self.Portfolio.MarginRemaining
        total_exposure = sum(
            abs(holding.Quantity) * holding.Price
            for holding in self.Portfolio.Values if holding.Type == SecurityType.Option
        )
        if self.disable_margin and available_cash < required_exposure:
            self.Debug(f"Ordre {order_type} refuse : Liquidites insuffisantes ({available_cash:.2f} disponibles, {required_exposure:.2f} requis).")
            return False
        new_exposure = total_exposure + required_exposure
        if new_exposure > self.Portfolio.TotalPortfolioValue * self.max_exposure_fraction:
            self.Debug(f"Ordre {order_type} refuse : Exposition maximale depassee ({new_exposure:.2f} > {self.Portfolio.TotalPortfolioValue * self.max_exposure_fraction:.2f}).")
            return False
        return True

    def log_portfolio_state(self, action, symbol=None):
        portfolio_value = self.Portfolio.TotalPortfolioValue
        portfolio_cash = self.Portfolio.Cash
        equity_quantity = self._equity.Holdings.Quantity
        options_positions = {
            sym: holding.Quantity
            for sym, holding in self.Portfolio.items() if holding.Type == SecurityType.Option
        }
        message = (
            f"{action} - Portefeuille Total: {portfolio_value:.2f}, Liquidites: {portfolio_cash:.2f}, "
            f"Actions Detenues: {equity_quantity}, Positions Options: {options_positions}"
        )
        if symbol:
            message += f", Instrument : {symbol.Value}"
        self.Debug(message)

    def OnData(self, data):
        if not self.Portfolio.Invested and self.IsMarketOpen(self._equity.Symbol):
            put_target_price = self._equity.Price * (1 - self.otm_threshold)
            put_symbol = self._get_target_contract(OptionRight.PUT, put_target_price)
            if put_symbol is not None:
                required_exposure = put_symbol.ID.StrikePrice * 100
                self.log_portfolio_state("Avant Vente PUT", put_symbol)
                if self._validate_order(required_exposure, "PUT"):
                    quantity_to_sell = math.floor(self.Portfolio.Cash / required_exposure)
                    self.MarketOrder(put_symbol, -quantity_to_sell)
                    self.log_portfolio_state("Apres Vente PUT", put_symbol)
        elif [self._equity.Symbol] == [symbol for symbol, holding in self.Portfolio.items() if holding.Invested]:
            call_target_price = self._equity.Price * (1 + self.otm_threshold)
            call_symbol = self._get_target_contract(OptionRight.CALL, call_target_price)
            if call_symbol is not None:
                quantity_to_cover = math.floor(self._equity.Holdings.Quantity / 100)
                self.log_portfolio_state("Avant Vente CALL", call_symbol)
                if quantity_to_cover > 0:
                    self.MarketOrder(call_symbol, -quantity_to_cover)
                    self.log_portfolio_state("Apres Vente CALL", call_symbol)
