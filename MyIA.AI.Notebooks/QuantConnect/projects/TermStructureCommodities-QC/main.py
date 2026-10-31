# region imports
from AlgorithmImports import *

from math import floor
from statistics import median
# endregion
# https://www.quantconnect.com/strategies/26
# Term Structure Effect in Commodities
# OOS 5Y CAGR -15.71%, 5Y Drawdown 80.80%, 5Y Sharpe -0.041
# Recent OOS: 38.85% 3M Return, 1.49 1Y Sharpe, 10.52 3M Sharpe
# Long-short commodity futures based on roll returns (backwardation/contango)
# Calculates annualized roll returns from near vs distant contract price ratios
# Top quintile backwardation = long, top quintile contango = short, monthly rebalance
# Source: Quantpedia Strategy #22, QC Strategy Library #26, cloned 2026-04-05, QC Project ID: 29688398
#
# Measurement parameters (#23594, protocol fixed before any run):
#   fix=off  original code, unchanged orders, plus passive counters.
#   fix=on   same roll-return signal (contracts expiring within 90 days,
#            nearest vs farthest, quintiles) with three corrections:
#            1. notional sizing, fully collateralized, +/-0.5/count per side;
#               set_holdings sizes a futures position by initial margin, which
#               gave 1.4x-5x gross notional instead of the intended 0.2x;
#            2. the traded contract is the first one expiring at least 35 days
#               after the rebalance (chain filter widened to 150 days), so the
#               book is not cut by an expiry before the next rebalance;
#            3. signal dictionaries initialized before the loop.
#   ref=dbc  reference arm: DBC held over the same window, no futures.
#   start, end (YYYY-MM-DD), cash: measurement window and capital.
# Counters published as runtime statistics: gross_median, gross_max
# (gross notional / portfolio value, 90 minutes after each rebalance fires),
# expiry_cuts, delist_orders, invalid_orders, no_tradable, no_price.


class CommodityTermStructureAlgorithm(QCAlgorithm):

    def initialize(self):
        self._fix = self.get_parameter("fix", "on").strip().lower()
        self._ref = self.get_parameter("ref", "none").strip().lower()
        # Aligned baseline period 2018-2025 (#1630). Original used a dynamic
        # start (end_date - 15*365 ~= 2010); standardized to 2018-01-01 for
        # cross-strategy comparison. Also fixes the fragile self.end_date
        # reference-before-set in the original clone.
        self.set_start_date(self._parse_date(self.get_parameter("start", "2018-01-01")))
        self.set_end_date(self._parse_date(self.get_parameter("end", "2025-01-01")))
        default_cash = "1000000" if self._fix == "off" else "10000000"
        self.set_cash(int(self.get_parameter("cash", default_cash)))
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        self.settings.seed_initial_prices = True

        self._gross = []
        self._expiry_cuts = 0
        self._delist_orders = 0
        self._invalid_orders = 0
        self._no_tradable = 0
        self._no_price = 0
        self._rebalances = 0
        self._active_rebalances = 0

        if self._ref == "dbc":
            self._dbc = self.add_equity("DBC", Resolution.DAILY).symbol
            return

        tickers = [
            Futures.Softs.COCOA,
            Futures.Softs.COFFEE,
            Futures.Grains.CORN,
            Futures.Softs.COTTON_2,
            Futures.Grains.OATS,
            Futures.Softs.ORANGE_JUICE,
            Futures.Grains.SOYBEAN_MEAL,
            Futures.Grains.SOYBEAN_OIL,
            Futures.Grains.SOYBEANS,
            Futures.Softs.SUGAR_11,
            Futures.Grains.WHEAT,
            Futures.Meats.FEEDER_CATTLE,
            Futures.Meats.LEAN_HOGS,
            Futures.Meats.LIVE_CATTLE,
            Futures.Energies.CRUDE_OIL_WTI,
            Futures.Energies.HEATING_OIL,
            Futures.Energies.NATURAL_GAS,
            Futures.Energies.GASOLINE,
            Futures.Metals.GOLD,
            Futures.Metals.PALLADIUM,
            Futures.Metals.SILVER
        ]
        max_days = 90 if self._fix == "off" else 150
        for ticker in tickers:
            future = self.add_future(ticker)
            future.set_filter(timedelta(0), timedelta(days=max_days))
        rebalance = self._rebalance if self._fix == "off" else self._rebalance_fixed
        self.schedule.on(self.date_rules.month_start("SPY"), self.time_rules.after_market_open("SPY", 30), rebalance)
        self.schedule.on(self.date_rules.month_start("SPY"), self.time_rules.after_market_open("SPY", 120), self._measure_gross)

    @staticmethod
    def _parse_date(text):
        year, month, day = (int(part) for part in text.strip().split("-"))
        return datetime(year, month, day)

    def on_data(self, slice):
        if self._ref == "dbc":
            if not self.portfolio[self._dbc].invested:
                self.set_holdings(self._dbc, 1.0)
            return
        for symbol, delisting in slice.delistings.items():
            if delisting.type == DelistingType.WARNING and self.portfolio[symbol].invested:
                self._expiry_cuts += 1

    def on_order_event(self, order_event):
        if order_event.status == OrderStatus.INVALID:
            self._invalid_orders += 1
        elif order_event.status == OrderStatus.FILLED:
            order = self.transactions.get_order_by_id(order_event.order_id)
            if order is not None and order.tag and "delist" in order.tag.lower():
                self._delist_orders += 1

    def _measure_gross(self):
        value = self.portfolio.total_portfolio_value
        if value <= 0:
            return
        gross = sum(abs(holding.holdings_value) for holding in self.portfolio.values() if holding.invested)
        self._gross.append(float(gross / value))

    def _rebalance(self):
        # Original code (fix=off), orders unchanged.
        self._rebalances += 1
        roll_returns = {}
        chains = {}
        for symbol, chain in self.current_slice.future_chains.items():
            if chain.contracts.count < 2:
                continue
            chains[symbol] = contracts = sorted([c for c in chain], key=lambda c: c.expiry)

            # R = (log(Pn) - log(Pd)) * 365 / (Td - Tn)
            near_contract = contracts[0]
            distant_contract = contracts[-1]

            price_near = near_contract.last_price if near_contract.last_price > 0 else 0.5 * float(near_contract.ask_price + near_contract.bid_price)
            price_distant = distant_contract.last_price if distant_contract.last_price > 0 else 0.5 * float(distant_contract.ask_price + distant_contract.bid_price)

            if distant_contract.expiry == near_contract.expiry:
                self.debug("ERROR: Near and distant contracts have the same expiry!" + str(near_contract))
                continue
            expire_range = 365 / (distant_contract.expiry - near_contract.expiry).days
            roll_returns[symbol] = (np.log(float(price_near)) - np.log(float(price_distant))) * expire_range
            positive_roll_returns = {symbol: returns for symbol, returns in roll_returns.items() if returns > 0}
            negative_roll_returns = {symbol: returns for symbol, returns in roll_returns.items() if returns < 0}

        quintile = floor(len(roll_returns) / 5)

        backwardation = sorted(positive_roll_returns, key=lambda x: positive_roll_returns[x], reverse=True)[:quintile]
        contango = sorted(negative_roll_returns, key=lambda x: negative_roll_returns[x])[:quintile]
        count = min(len(backwardation), len(contango))
        if count != quintile:
            backwardation = backwardation[:count]
            contango = contango[:count]

        if count == 0:
            return

        self._active_rebalances += 1
        targets = []
        for short_symbol in contango:
            sort = sorted(chains[short_symbol], key=lambda x: x.expiry)
            targets.append(PortfolioTarget(sort[0].symbol, -0.1 / count))
        for long_symbol in backwardation:
            sort = sorted(chains[long_symbol], key=lambda x: x.expiry)
            targets.append(PortfolioTarget(sort[0].symbol, 0.1 / count))
        self.set_holdings(targets, True)

    @staticmethod
    def _contract_price(contract):
        if contract.last_price > 0:
            return float(contract.last_price)
        return 0.5 * float(contract.ask_price + contract.bid_price)

    def _rebalance_fixed(self):
        # fix=on: same signal, notional sizing, contract held past the next rebalance.
        self._rebalances += 1
        roll_returns = {}
        positive_roll_returns = {}
        negative_roll_returns = {}
        tradable = {}
        signal_horizon = self.time + timedelta(days=90)
        min_expiry = self.time + timedelta(days=35)
        for symbol, chain in self.current_slice.future_chains.items():
            contracts = sorted([c for c in chain], key=lambda c: c.expiry)
            signal_contracts = [c for c in contracts if c.expiry <= signal_horizon]
            if len(signal_contracts) < 2:
                continue

            # R = (log(Pn) - log(Pd)) * 365 / (Td - Tn)
            near_contract = signal_contracts[0]
            distant_contract = signal_contracts[-1]
            price_near = self._contract_price(near_contract)
            price_distant = self._contract_price(distant_contract)
            if distant_contract.expiry == near_contract.expiry:
                continue
            if price_near <= 0 or price_distant <= 0:
                self._no_price += 1
                continue
            expire_range = 365 / (distant_contract.expiry - near_contract.expiry).days
            roll_returns[symbol] = (np.log(price_near) - np.log(price_distant)) * expire_range
            traded = next((c for c in contracts if c.expiry >= min_expiry), None)
            if traded is not None:
                tradable[symbol] = traded

        positive_roll_returns = {symbol: returns for symbol, returns in roll_returns.items() if returns > 0}
        negative_roll_returns = {symbol: returns for symbol, returns in roll_returns.items() if returns < 0}
        quintile = floor(len(roll_returns) / 5)
        backwardation = sorted(positive_roll_returns, key=lambda x: positive_roll_returns[x], reverse=True)[:quintile]
        contango = sorted(negative_roll_returns, key=lambda x: negative_roll_returns[x])[:quintile]
        count = min(len(backwardation), len(contango))
        backwardation = backwardation[:count]
        contango = contango[:count]
        if count == 0:
            return

        self._active_rebalances += 1
        value = self.portfolio.total_portfolio_value
        targets = {}
        for side, roots in ((-1, contango), (1, backwardation)):
            for root in roots:
                contract = tradable.get(root)
                if contract is None:
                    self._no_tradable += 1
                    continue
                price = self._contract_price(contract)
                multiplier = self.securities[contract.symbol].symbol_properties.contract_multiplier
                if price <= 0 or multiplier <= 0:
                    self._no_price += 1
                    continue
                targets[contract.symbol] = int(round(side * 0.5 / count * value / (price * multiplier)))

        self.transactions.cancel_open_orders()
        for holding in list(self.portfolio.values()):
            if holding.invested and holding.symbol not in targets:
                self.liquidate(holding.symbol)
        for symbol, quantity in targets.items():
            delta = quantity - self.portfolio[symbol].quantity
            if delta != 0:
                self.market_order(symbol, delta)

    def on_end_of_algorithm(self):
        self.set_runtime_statistic("gross_median", f"{median(self._gross):.3f}" if self._gross else "n/a")
        self.set_runtime_statistic("gross_max", f"{max(self._gross):.3f}" if self._gross else "n/a")
        self.set_runtime_statistic("gross_samples", str(len(self._gross)))
        self.set_runtime_statistic("expiry_cuts", str(self._expiry_cuts))
        self.set_runtime_statistic("delist_orders", str(self._delist_orders))
        self.set_runtime_statistic("invalid_orders", str(self._invalid_orders))
        self.set_runtime_statistic("no_tradable", str(self._no_tradable))
        self.set_runtime_statistic("no_price", str(self._no_price))
        self.set_runtime_statistic("rebalances", f"{self._active_rebalances}/{self._rebalances}")
