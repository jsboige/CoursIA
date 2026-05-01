# region imports
from AlgorithmImports import *

from math import floor
# endregion
# https://www.quantconnect.com/strategies/26
# Term Structure Effect in Commodities
# OOS 5Y CAGR -15.71%, 5Y Drawdown 80.80%, 5Y Sharpe -0.041
# Recent OOS: 38.85% 3M Return, 1.49 1Y Sharpe, 10.52 3M Sharpe
# Long-short commodity futures based on roll returns (backwardation/contango)
# Calculates annualized roll returns from near vs distant contract price ratios
# Top quintile backwardation = long, top quintile contango = short, monthly rebalance
# Source: Quantpedia Strategy #22, QC Strategy Library #26, cloned 2026-04-05, QC Project ID: 29688398


class CommodityTermStructureAlgorithm(QCAlgorithm):

    def initialize(self):
        self.set_start_date(2005, 1, 1)
        self.set_cash(1000000)
        self.settings.seed_initial_prices = True
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
        for ticker in tickers:
            future = self.add_future(ticker)
            future.set_filter(timedelta(0), timedelta(days=90))
        self.schedule.on(self.date_rules.month_start("SPY"), self.time_rules.after_market_open("SPY", 30), self._rebalance)

    def _rebalance(self):
        roll_returns = {}
        chains = {}
        for symbol, chain in self.current_slice.future_chains.items():
            if chain.contracts.count < 2:
                continue
            chains[symbol] = contracts = sorted([c for c in chain], key=lambda c: c.expiry)

            near_contract = contracts[0]
            distant_contract = contracts[-1]

            price_near = near_contract.last_price if near_contract.last_price > 0 else 0.5 * float(near_contract.ask_price + near_contract.bid_price)
            price_distant = distant_contract.last_price if distant_contract.last_price > 0 else 0.5 * float(distant_contract.ask_price + distant_contract.bid_price)

            if distant_contract.expiry == near_contract.expiry:
                self.debug("ERROR: Near and distant contracts have the same expiry!" + str(near_contract))
                continue
            expire_range = 365 / (distant_contract.expiry - near_contract.expiry).days
            roll_returns[symbol] = (np.log(float(price_near)) - np.log(float(price_distant))) * expire_range

        if not roll_returns:
            return

        positive_roll_returns = {s: r for s, r in roll_returns.items() if r > 0}
        negative_roll_returns = {s: r for s, r in roll_returns.items() if r < 0}
        quintile = floor(len(roll_returns) / 5)

        backwardation = sorted(positive_roll_returns, key=lambda x: positive_roll_returns[x], reverse=True)[:quintile]
        contango = sorted(negative_roll_returns, key=lambda x: negative_roll_returns[x])[:quintile]
        count = min(len(backwardation), len(contango))
        if count != quintile:
            backwardation = backwardation[:count]
            contango = contango[:count]

        if count == 0:
            return

        targets = []
        for short_symbol in contango:
            sort = sorted(chains[short_symbol], key=lambda x: x.expiry)
            targets.append(PortfolioTarget(sort[0].symbol, -0.1 / count))
        for long_symbol in backwardation:
            sort = sorted(chains[long_symbol], key=lambda x: x.expiry)
            targets.append(PortfolioTarget(sort[0].symbol, 0.1 / count))
        self.set_holdings(targets, True)
