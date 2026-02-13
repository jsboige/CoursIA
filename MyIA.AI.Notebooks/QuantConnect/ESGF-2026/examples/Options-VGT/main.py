# region imports
from AlgorithmImports import *
import math

class GainStrategy(QCAlgorithm):
    def Initialize(self):
        self.SetStartDate(2023, 12, 1)
        self.SetCash(50_000)
        self.SetBenchmark("VGT")
        self.days_to_expiry = int(self.GetParameter("days_to_expiry", 30))
        self.otm_threshold = float(self.GetParameter("otm_threshold", 0.05))
        self.position_fraction = float(self.GetParameter("position_fraction", 0.2))
        self.SetSecurityInitializer(
            BrokerageModelSecurityInitializer(
                self.BrokerageModel,
                FuncSecuritySeeder(self.GetLastKnownPrices)
            )
        )
        self._eqNames = ['NVDA','ORCL','CSCO','AMD','QCOM']
        self.otm_threshold_AddOn = {'NVDA':0.005 ,'ORCL':0.08,'CSCO':0.11,'AMD':0.009,'QCOM':0.05}
        self._equities = {eq_tickers : self.AddEquity(eq_tickers,
            dataNormalizationMode=DataNormalizationMode.Raw) for eq_tickers in self._eqNames}
        self.max_exposure_fraction = float(self.GetParameter("max_exposure_fraction", 1.0))
        self.disable_margin = bool(self.GetParameter("disable_margin", 1))

    def _get_target_contract(self, right, target_price):
        contract_symbols = {eq: self.OptionChainProvider.GetOptionContractList(self._equities[eq].Symbol, self.Time) for eq in self._eqNames}
        for eq in self._eqNames:
            if not contract_symbols[eq]:
                self.Debug(f"Aucun contrat disponible pour {self._equities[eq].Symbol} a {self.Time}.")
                return None
        future_dates = {eq: [s.ID.Date for s in contract_symbols[eq] if s.ID.Date.date() > self.Time.date() + timedelta(self.days_to_expiry)] for eq in self._eqNames}
        for eq in self._eqNames:
            if not future_dates[eq]:
                self.Debug("Aucune expiration disponible au-dela de la periode demandee.")
                return None
        expiry = {eq: min(future_dates[eq]) for eq in self._eqNames}
        filtered_symbols = [s for eq in self._eqNames for s in contract_symbols[eq] if s.ID.Date == expiry[eq] and s.ID.OptionRight == right and
             (s.ID.StrikePrice <= target_price if right == OptionRight.PUT else s.ID.StrikePrice >= target_price)]
        filtered_symbols = sorted(filtered_symbols, key=lambda s: s.ID.StrikePrice, reverse=(right == OptionRight.PUT))
        if not filtered_symbols:
            self.Debug(f"Aucun contrat trouve pour {right} autour de {target_price:.2f}.")
            return None
        symbol = filtered_symbols[0]
        self.AddOptionContract(symbol)
        return symbol

    def _validate_order(self, required_exposure, order_type="PUT"):
        available_cash = self.Portfolio.MarginRemaining
        total_exposure = sum(abs(holding.Quantity) * holding.Price for holding in self.Portfolio.Values if holding.Type == SecurityType.Option)
        if self.disable_margin and available_cash < required_exposure:
            self.Debug(f"Ordre {order_type} refuse : Liquidites insuffisantes ({available_cash:.2f} disponibles, {required_exposure:.2f} requis).")
            return False
        new_exposure = total_exposure + required_exposure
        if new_exposure > self.Portfolio.TotalPortfolioValue * self.max_exposure_fraction:
            self.Debug(f"Ordre {order_type} refuse : Exposition maximale depassee.")
            return False
        return True

    def log_portfolio_state(self, action, symbol=None):
        portfolio_value = self.Portfolio.TotalPortfolioValue
        portfolio_cash = self.Portfolio.Cash
        equity_quantity = {eq: self._equities[eq].Holdings.Quantity for eq in self._eqNames}
        options_positions = {sym: holding.Quantity for sym, holding in self.Portfolio.items() if holding.Type == SecurityType.Option}
        message = (f"{action} - Portefeuille Total: {portfolio_value:.2f}, Liquidites: {portfolio_cash:.2f}, "
                   f"Actions Detenues: {list(equity_quantity.keys())} = {list(equity_quantity.values())}, Positions Options: {options_positions}")
        if symbol:
            message += f", Instrument : {symbol.Value}"
        self.Debug(message)

    def OnData(self, data):
        for eq in self._eqNames:
            if not self.Portfolio.Invested and self.IsMarketOpen(self._equities[eq].Symbol):
                put_target_price = self._equities[eq].Price * (1 - self.otm_threshold - self.otm_threshold_AddOn[eq])
                put_symbol = self._get_target_contract(OptionRight.PUT, put_target_price)
                if put_symbol is not None:
                    required_exposure = put_symbol.ID.StrikePrice * 100
                    self.log_portfolio_state("Avant Vente PUT", put_symbol)
                    if self._validate_order(required_exposure, "PUT"):
                        quantity_to_sell = math.floor(self.Portfolio.Cash / required_exposure)
                        self.MarketOrder(put_symbol, -quantity_to_sell)
                        self.log_portfolio_state("Apres Vente PUT", put_symbol)
            elif [self._equities[eq].Symbol] == [symbol for symbol, holding in self.Portfolio.items() if holding.Invested]:
                call_target_price = self._equities[eq].Price * (1 + self.otm_threshold + self.otm_threshold_AddOn[eq])
                call_symbol = self._get_target_contract(OptionRight.CALL, call_target_price)
                if call_symbol is not None:
                    quantity_to_cover = math.floor(self._equities[eq].Holdings.Quantity / 100)
                    self.log_portfolio_state("Avant Vente CALL", call_symbol)
                    if quantity_to_cover > 0:
                        self.MarketOrder(call_symbol, -quantity_to_cover)
                        self.log_portfolio_state("Apres Vente CALL", call_symbol)
