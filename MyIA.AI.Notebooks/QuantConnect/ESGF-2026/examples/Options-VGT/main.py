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

    def _get_target_contract_for_equity(self, eq, right, target_price):
        """Cherche un contrat d'option pour UNE equity specifique."""
        contract_symbols = self.OptionChainProvider.GetOptionContractList(
            self._equities[eq].Symbol, self.Time)
        if not contract_symbols:
            self.Debug(f"Aucun contrat disponible pour {eq} a {self.Time}.")
            return None
        future_dates = [s.ID.Date for s in contract_symbols
                        if s.ID.Date.date() > self.Time.date() + timedelta(self.days_to_expiry)]
        if not future_dates:
            self.Debug(f"Aucune expiration disponible pour {eq} au-dela de {self.days_to_expiry}j.")
            return None
        expiry = min(future_dates)
        if right == OptionRight.PUT:
            filtered = [s for s in contract_symbols
                        if s.ID.Date == expiry and s.ID.OptionRight == right
                        and s.ID.StrikePrice <= target_price]
            filtered = sorted(filtered, key=lambda s: s.ID.StrikePrice, reverse=True)
        else:
            filtered = [s for s in contract_symbols
                        if s.ID.Date == expiry and s.ID.OptionRight == right
                        and s.ID.StrikePrice >= target_price]
            filtered = sorted(filtered, key=lambda s: s.ID.StrikePrice)
        if not filtered:
            self.Debug(f"Aucun contrat {right} pour {eq} autour de {target_price:.2f}.")
            return None
        symbol = filtered[0]
        self.AddOptionContract(symbol)
        return symbol

    def _has_option_position_on(self, eq):
        """Verifie si on a deja une position option liee a cette equity."""
        eq_symbol = self._equities[eq].Symbol
        for sym, holding in self.Portfolio.items():
            if holding.Invested and holding.Type == SecurityType.Option:
                if sym.Underlying == eq_symbol:
                    return True
        return False

    def _has_equity_shares(self, eq):
        """Verifie si on detient des actions de cette equity (suite a assignation PUT)."""
        return self._equities[eq].Holdings.Quantity > 0

    def _validate_order(self, required_exposure, order_type="PUT"):
        available_cash = self.Portfolio.MarginRemaining
        total_exposure = sum(abs(holding.Quantity) * holding.Price
                            for holding in self.Portfolio.Values
                            if holding.Type == SecurityType.Option)
        if self.disable_margin and available_cash < required_exposure:
            self.Debug(f"Ordre {order_type} refuse : Liquidites insuffisantes "
                       f"({available_cash:.2f} dispo, {required_exposure:.2f} requis).")
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
        options_positions = {sym: holding.Quantity for sym, holding in self.Portfolio.items()
                            if holding.Type == SecurityType.Option}
        message = (f"{action} - Portefeuille Total: {portfolio_value:.2f}, "
                   f"Liquidites: {portfolio_cash:.2f}, "
                   f"Actions: {equity_quantity}, Options: {options_positions}")
        if symbol:
            message += f", Instrument : {symbol.Value}"
        self.Debug(message)

    def OnData(self, data):
        for eq in self._eqNames:
            if not self.IsMarketOpen(self._equities[eq].Symbol):
                continue

            # Si on detient des actions (assignation PUT) -> vendre des CALLs couverts
            if self._has_equity_shares(eq):
                if not self._has_option_position_on(eq):
                    call_target_price = self._equities[eq].Price * (
                        1 + self.otm_threshold + self.otm_threshold_AddOn[eq])
                    call_symbol = self._get_target_contract_for_equity(
                        eq, OptionRight.CALL, call_target_price)
                    if call_symbol is not None:
                        quantity_to_cover = math.floor(
                            self._equities[eq].Holdings.Quantity / 100)
                        if quantity_to_cover > 0:
                            self.log_portfolio_state("Avant Vente CALL", call_symbol)
                            self.MarketOrder(call_symbol, -quantity_to_cover)
                            self.log_portfolio_state("Apres Vente CALL", call_symbol)

            # Si pas de position option sur cette equity -> vendre des PUTs
            elif not self._has_option_position_on(eq):
                put_target_price = self._equities[eq].Price * (
                    1 - self.otm_threshold - self.otm_threshold_AddOn[eq])
                put_symbol = self._get_target_contract_for_equity(
                    eq, OptionRight.PUT, put_target_price)
                if put_symbol is not None:
                    required_exposure = put_symbol.ID.StrikePrice * 100
                    if self._validate_order(required_exposure, "PUT"):
                        # Allouer une fraction du cash par equity
                        cash_per_equity = self.Portfolio.Cash * self.position_fraction
                        quantity_to_sell = max(1, math.floor(
                            cash_per_equity / required_exposure))
                        self.log_portfolio_state("Avant Vente PUT", put_symbol)
                        self.MarketOrder(put_symbol, -quantity_to_sell)
                        self.log_portfolio_state("Apres Vente PUT", put_symbol)
