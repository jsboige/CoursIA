# region imports
from datetime import date
from decimal import Decimal as PyDecimal

from AlgorithmImports import *
# endregion


class WheelStrategyAlgorithm(QCAlgorithm):

    def Initialize(self):
        # La fenêtre par défaut est conservée ; les dates sont paramétrables pour le rejeu.
        start = date.fromisoformat(self.GetParameter("start", "2015-01-01"))
        end = date.fromisoformat(self.GetParameter("end", "2024-12-31"))
        self.SetStartDate(start.year, start.month, start.day)
        self.SetEndDate(end.year, end.month, end.day)
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

        # VIX filter for volatility regime
        try:
            self._vix = self.AddIndex("VIX", Resolution.DAILY).Symbol
            self._vix_value = self.Identity(self._vix)
        except Exception:
            self._vix = None
            self._vix_value = None

        # Parameters - optimized based on research
        self.days_to_expiry = int(self.GetParameter("days_to_expiry", 21))  # 21 DTE (was 30)
        self.otm_threshold = float(self.GetParameter("otm_threshold", 0.05))  # 5% OTM (optimal)
        self.max_exposure_fraction = float(self.GetParameter("max_exposure_fraction", 0.8))  # Reduced from 1.0
        self.disable_margin = bool(self.GetParameter("disable_margin", 1))
        self.vix_high_threshold = 20  # Skip selling puts when VIX > 20 (was 25)
        self.vix_low_threshold = 15  # Aggressive selling when VIX < 15

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

    def _put_collateral(self, symbol: Symbol) -> PyDecimal:
        multiplier = self.Securities[symbol].SymbolProperties.ContractMultiplier
        return PyDecimal(str(symbol.ID.StrikePrice)) * PyDecimal(str(multiplier))

    def _put_quantity(self, symbol: Symbol) -> int:
        per_contract = self._put_collateral(symbol)
        if per_contract <= 0:
            return 0
        reserved = sum(
            (
                PyDecimal(str(-holding.Quantity)) * self._put_collateral(held_symbol)
                for held_symbol, holding in self.Portfolio.items()
                if holding.Type == SecurityType.Option
                and holding.Quantity < 0
                and held_symbol.ID.OptionRight == OptionRight.PUT
            ),
            PyDecimal(0),
        )
        cash = PyDecimal(str(self.Portfolio.Cash)) - reserved
        if self.disable_margin:
            cash = min(cash, PyDecimal(str(self.Portfolio.MarginRemaining)))
        cap = PyDecimal(str(self.Portfolio.TotalPortfolioValue)) * PyDecimal(
            str(self.max_exposure_fraction)
        )
        return int(max(PyDecimal(0), min(cash, cap - reserved)) // per_contract)

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
        # VIX filter: skip selling puts during high volatility
        current_vix = None
        if self._vix_value is not None and self._vix_value.IsReady:
            current_vix = self._vix_value.Current.Value

        # Skip selling puts when VIX is high (market stress)
        if current_vix is not None and current_vix > self.vix_high_threshold:
            self.Debug(f"VIX filter: Skip PUT selling (VIX={current_vix:.1f} > {self.vix_high_threshold})")
            return

        if not self.Portfolio.Invested and self.IsMarketOpen(self._equity.Symbol):
            put_target_price = self._equity.Price * (1 - self.otm_threshold)
            put_symbol = self._get_target_contract(OptionRight.PUT, put_target_price)
            if put_symbol is not None:
                quantity_to_sell = self._put_quantity(put_symbol)
                if quantity_to_sell > 0:
                    self.log_portfolio_state("Avant Vente PUT", put_symbol)
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
