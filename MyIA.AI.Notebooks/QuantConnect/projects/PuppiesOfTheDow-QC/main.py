from AlgorithmImports import *
from datetime import datetime
# https://www.quantconnect.com/strategies/211
# Puppies of the Dow Value-Income Tilt
# OOS 1Y Sharpe 1.99, 5Y CAGR 10.16%, 5Y Drawdown 22.90%, 65% Win Rate
# Systematic value/income tilt using Dow 30: rank by dividend yield,
# select 10 highest yielding (Dogs of the Dow), then 5 lowest priced (Puppies)
# Equal weighted, annual rebalance
# Source: QC Strategy Library #211, cloned 2026-04-05, QC Project ID: 29687759
#
# Instrumentation de mesure (#25130). Avec les defauts, la regle de trading est celle
# d'origine.
#   start, end  = fenetre. Le code d'origine appelait set_start_date(self.end_date - 12*365 j)
#                 AVANT set_end_date(2025, 1, 1) : il lisait la date de fin par defaut de
#                 Lean, et le debut se deplacait avec la date du lancement. Les defauts sont
#                 l'intention lisible du code : 12 x 365 jours avant le 2025-01-01.
#   mode        = base (regle d'origine) | dogs (controle : les 10 plus hauts rendements a
#                 10 % chacun, sans l'etape de prix) | spy, dia (references : l'ETF detenu a
#                 100 %, memes frais, meme instrumentation)
#   yield_field = total (champ du code, valuation_ratios.total_yield) | dividend
#                 (controle : valuation_ratios.trailing_dividend_yield, le rendement du
#                 dividende de la regle d'O'Higgins)
#   n           = taille du portefeuille (5 a l'origine)
#   fee_mult    = multiplicateur des frais du courtier (1 = inchanges)
# Valeur du portefeuille a chaque cloture dans le graphique "shadow" (contrat de rejeu en
# ombre, #18923) ; titres retenus a chaque selection dans le journal.


class _ScaledFeeModel(FeeModel):
    """Frais du courtier (modele IB de Lean), mis a l'echelle (identite a 1.0)."""

    def __init__(self, multiplier):
        self._multiplier = multiplier
        self._base = InteractiveBrokersFeeModel()

    def get_order_fee(self, parameters):
        fee = self._base.get_order_fee(parameters)
        if fee is None or self._multiplier == 1.0:
            return fee
        amount = float(fee.value.amount) * self._multiplier
        return OrderFee(CashAmount(amount, fee.value.currency))


class PuppiesOfTheDow(QCAlgorithm):

    def initialize(self):
        start = datetime.strptime(self.get_parameter("start") or "2013-01-04", "%Y-%m-%d")
        end = datetime.strptime(self.get_parameter("end") or "2025-01-01", "%Y-%m-%d")
        self.set_start_date(start.year, start.month, start.day)
        self.set_end_date(end.year, end.month, end.day)
        self.start_value = 100_000.0
        self.set_cash(100_000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        self.mode = self.get_parameter("mode") or "base"
        self.yield_field = self.get_parameter("yield_field") or "total"
        self.fee_mult = float(self.get_parameter("fee_mult") or 1)
        if self.mode not in ("base", "dogs", "spy", "dia") or self.yield_field not in ("total", "dividend"):
            raise ValueError(f"parametres inconnus : {self.mode}/{self.yield_field}")
        if self.fee_mult != 1.0:
            seeder = FuncSecuritySeeder(self.get_last_known_prices)
            base_init = BrokerageModelSecurityInitializer(self.brokerage_model, seeder)
            fee_mult = self.fee_mult

            def init(security):
                base_init.initialize(security)
                security.set_fee_model(_ScaledFeeModel(fee_mult))

            self.set_security_initializer(init)

        self._portfolio_size = int(self.get_parameter("n") or 5)
        self.settings.seed_initial_prices = True
        self.closes = 0
        self.traded = 0.0
        self.selections = 0
        self.rebalances = 0
        self.invalid = 0

        if self.mode in ("spy", "dia"):
            self._ref = self.add_equity(self.mode.upper()).symbol
        else:
            self.universe_settings.schedule.on(self.date_rules.year_start("SPY"))
            # Add universe using DIA ETF constituents (Dow 30)
            self._universe = self.add_universe(self.universe.etf("DIA"), self._select)
            self.schedule.on(
                self.date_rules.year_start("SPY"),
                self.time_rules.at(8, 0),
                self._rebalance
            )
        self.schedule.on(self.date_rules.every_day("SPY"),
                         self.time_rules.before_market_close("SPY", 1),
                         self._shadow)
        self.set_warm_up(timedelta(365))

    def _yield(self, f):
        ratios = f.valuation_ratios
        return ratios.total_yield if self.yield_field == "total" else ratios.trailing_dividend_yield

    def _select(self, fundamentals: List[Fundamental]) -> List[Symbol]:
        fundamentals = list(fundamentals)
        # Filter for valid price and dividend yield
        dow_fundamentals = [f for f in fundamentals if f.price > 5 and self._yield(f) > 0]
        # Dogs of the Dow: top 10 highest dividend yielders from the Dow 30
        dogs = sorted(dow_fundamentals, key=self._yield)[-10:]
        if self.mode == "dogs":
            chosen = dogs
        else:
            # Puppies: the 5 lowest-priced stocks from the Dogs
            chosen = sorted(dogs, key=lambda x: x.price)[:self._portfolio_size]
        self.selections += 1
        self.log(f"select {self.time.date()} constituents={len(fundamentals)} eligible={len(dow_fundamentals)} "
                 + "chosen=" + ",".join(f"{c.symbol.value}:{c.price:.2f}:{self._yield(c):.4f}" for c in chosen))
        return [p.symbol for p in chosen]

    def _rebalance(self):
        if self.is_warming_up:
            return
        if self.mode in ("spy", "dia"):
            self.set_holdings(self._ref, 1.0)
            return
        # Create equal-weight portfolio targets from selected universe symbols
        size = 10 if self.mode == "dogs" else self._portfolio_size
        targets = [PortfolioTarget(s, 1 / size) for s in self._universe.selected]
        self.rebalances += 1
        self.set_holdings(targets, True)

    def on_warmup_finished(self):
        self._rebalance()

    def _shadow(self):
        if self.is_warming_up:
            return
        self.plot("shadow", f"e{self.closes % 5}", self.portfolio.total_portfolio_value)
        if self.closes % 5 == 0:
            # une cloture sur cinq : reste sous la limite de points par serie
            self.plot("shadow", "fees", self.portfolio.total_fees / self.start_value)
            self.plot("shadow", "turnover", self.traded)
        self.closes += 1

    def on_order_event(self, event):
        if event.status in (OrderStatus.FILLED, OrderStatus.PARTIALLY_FILLED):
            self.traded += abs(event.fill_quantity * event.fill_price) / self.portfolio.total_portfolio_value
        elif event.status == OrderStatus.INVALID:
            self.invalid += 1

    def on_end_of_algorithm(self):
        self.set_runtime_statistic("selections", str(self.selections))
        self.set_runtime_statistic("rebalances", str(self.rebalances))
        self.set_runtime_statistic("invalid", str(self.invalid))
        self.set_runtime_statistic("closes", str(self.closes))
