#region imports
    using System;
    using System.Collections;
    using System.Collections.Generic;
    using System.Linq;
    using System.Globalization;
    using System.Drawing;
    using QuantConnect;
    using QuantConnect.Algorithm.Framework;
    using QuantConnect.Algorithm.Framework.Selection;
    using QuantConnect.Algorithm.Framework.Alphas;
    using QuantConnect.Algorithm.Framework.Portfolio;
    using QuantConnect.Algorithm.Framework.Execution;
    using QuantConnect.Algorithm.Framework.Risk;
    using QuantConnect.Parameters;
    using QuantConnect.Benchmarks;
    using QuantConnect.Brokerages;
    using QuantConnect.Util;
    using QuantConnect.Interfaces;
    using QuantConnect.Algorithm;
    using QuantConnect.Algorithm.CSharp.Helpers;
    using QuantConnect.Indicators;
    using QuantConnect.Data;
    using QuantConnect.Data.Consolidators;
    using QuantConnect.Data.Custom;
    using QuantConnect.DataSource;
    using QuantConnect.Data.Fundamental;
    using QuantConnect.Data.Market;
    using QuantConnect.Data.UniverseSelection;
    using QuantConnect.Notifications;
    using QuantConnect.Orders;
    using QuantConnect.Orders.Fees;
    using QuantConnect.Orders.Fills;
    using QuantConnect.Orders.Slippage;
    using QuantConnect.Scheduling;
    using QuantConnect.Securities;
    using QuantConnect.Securities.Equity;
    using QuantConnect.Securities.Future;
    using QuantConnect.Securities.Option;
    using QuantConnect.Securities.Forex;
    using QuantConnect.Securities.Crypto;
    using QuantConnect.Securities.Interfaces;
    using QuantConnect.Storage;
    using QuantConnect.Data.Custom.AlphaStreams;
    using QCAlgorithmFramework = QuantConnect.Algorithm.QCAlgorithm;
    using QCAlgorithmFrameworkBridge = QuantConnect.Algorithm.QCAlgorithm;
#endregion

namespace QuantConnect.Algorithm.CSharp
{
    public class StocksOnTheMoveAlgorithm : QCAlgorithm
    {
        ///Momentum is calculated based on 90 past days annualized exponential regression slope;
        private int _annualizedSlopeWindow = 90;

        /// If the stock is below its 150 days moving average, sell it;
        private int _movingAverageWindow = 150;

        /// ATR window
        private int _atrWindow = 20;

        /// Daily Risk of each trade on the portfolio (0,5%)
        private const decimal RiskPerContractOnPortfolio = 0.010m;

        /// Total number of security symbols in the Universe
        private static int _universeSelectMaxStocks = 100;

        /// Holds our security custom indicators per symbol
        private Dictionary<Symbol, CustomMomentumIndicator> _customIndicators = new Dictionary<QuantConnect.Symbol, CustomMomentumIndicator>(_universeSelectMaxStocks);

        // If the SP500 is above the 200 days moving average we buy stocks, otherwise not;
        private MarketRegimeFilter _marketRegimeFilter;

        //If the stock is not in the top 100/ 20% ranking, sell it;
        private int _topNStockOfSp500 = 20;

        ///If the stock gapped > 15% over period (90d) Do not buy: Maximum Gap in percentage
        private decimal _maximumGap = 0.15m;
        private int _gapWindow = 90;

        ///Minimum annualized slope before buying stock.
        private decimal _minimumAnnualizedSlope = 10m;

        ///Twice a month rebalance the positions sizes (risk);
        private bool _rebalanceWeek = false;
        public bool RebalanceWeek { get { return _rebalanceWeek; } }

        // === Capital-gain filter (#12034, consolidation QC research 21160) ===
        // Cannon & Lynch (2025, Review of Finance 29(4)): return extrapolation — and thus
        // the momentum premium — concentrates in non-dividend-paying ("capital-gain")
        // stocks (1.417%/month vs 0.684% among dividend payers). When enabled, the
        // weekly ranking excludes any stock that distributed at least one dividend over
        // the trailing twelve months (history request on Dividend objects).
        // Default OFF: the baseline strategy (slope momentum on OEF constituents) is
        // unchanged unless the flag is flipped — the arms are compared honestly.
        // Exposed as a QC parameter (#11698) so every arm runs from the same compile:
        // backtests pass parameters={"filter-dividend-payers": "true"} for the ON arm.
        [Parameter("filter-dividend-payers")]
        private bool _filterDividendPayers = false;
        private DateTime _lastDividendScan = DateTime.MinValue;
        private readonly Dictionary<Symbol, bool> _paysDividend = new Dictionary<Symbol, bool>();
        private static readonly TimeSpan DividendScanInterval = TimeSpan.FromDays(7);

        // === Universe selection (#11698 QC500 retest) ===
        // Baseline (default): OEF constituents (S&P 100), byte-identical behavior.
        // Opt-in "QC500": Universe.QC500 — LEAN selects the 500 most liquid US
        // equities by dollar volume, reconstituted monthly, and inherits the algorithm
        // UniverseSettings (here Resolution.Daily). A wider pool where non-dividend
        // payers ("capital-gain stocks") are properly represented — closer to the
        // 1000-most-liquid terrain the Cannon & Lynch (2025) claim was measured on.
        [Parameter("universe")]
        private string _universeName = "OEF";

        ///Broker fee to take into account to check if Cash is avalaible
        private const decimal BrokerFee = 0.005m;

        // Debug parameters
        private bool _isLogging = false;
        /// Is debugging set?
        public bool IsLooging { get { return _isLogging; } }
        public new void Log(string message)
        {
            if (IsLooging)
                base.Log(message);
        }


        /// Initialise the data and resolution required, as well as the cash and start-end dates for your algorithm.
        public override void Initialize()
        {
            _isLogging = false;
            // Extended: covers 2015 bear, 2016-2017 bull, 2018 vol, 2019 rally,
            // COVID crash 2020, 2021 bull, 2022 bear, 2023-2025 recovery
            SetStartDate(2015, 1, 1);
            SetEndDate(DateTime.Now);

            //Set cash and brokermodel
            SetCash(1000000);
            SetBrokerageModel(BrokerageName.InteractiveBrokersBrokerage, AccountType.Margin);

            //Set Benchmark
            Security security = AddEquity("SPY", Resolution.Daily);
            SetBenchmark(security.Symbol);

            // Set the MarketRegimeFilter
            SimpleMovingAverage spyMovingAverage200 = SMA("SPY", 200, Resolution.Daily);

            //Warm up SMA
            SetWarmUp(200);
            IEnumerable<TradeBar> history = History("SPY", 200, Resolution.Daily);
            foreach (TradeBar tradeBar in history)
            {
                spyMovingAverage200.Update(tradeBar.EndTime, tradeBar.Close);
            }
            _marketRegimeFilter = new MarketRegimeFilter(spyMovingAverage200);

            //Setup universe based on ETF: https://www.quantconnect.com/docs#Universes
            UniverseSettings.Resolution = Resolution.Daily;
            bool useQc500 = _universeName.Trim().Equals("QC500", StringComparison.OrdinalIgnoreCase);
            if (useQc500)
            {
                // #11698: QC500 universe (500 most liquid US equities by dollar volume,
                // monthly reconstitution) — same settings, wider pool than OEF (S&P 100).
                AddUniverse(Universe.QC500);
            }
            else
            {
                AddUniverse(Universe.ETF("OEF", Market.USA, UniverseSettings));
            }
            // Echo the active configuration so each backtest log proves which arm ran.
            Debug("CTG-Momentum config: universe=" + _universeName + " (QC500=" + useQc500
                + "), filter-dividend-payers=" + _filterDividendPayers);

            //Trade only on Wednesday at opening after 1 minutes
            Schedule.On(DateRules.Every(DayOfWeek.Thursday),
                TimeRules.AfterMarketOpen("SPY", 1), ScheduledOnWednesday1MinuteAfterMarketOpen);
        }

        // Capital-gain filter (#12034): refresh the TTM dividend-payer cache weekly.
        // A stock that distributed >= 1 dividend over the trailing 365 days is a payer.
        private void UpdateDividendPayerCache()
        {
            if (Time - _lastDividendScan < DividendScanInterval) return;
            _lastDividendScan = Time;
            _paysDividend.Clear();
            var dividends = History<Dividend>(_customIndicators.Keys.ToList(), TimeSpan.FromDays(365));
            foreach (var dataDict in dividends)
            {
                foreach (var kvp in dataDict)
                {
                    _paysDividend[kvp.Key] = true;
                }
            }
        }

        // SECURITY RANKING, SELL, REBALANCE AND BUY
        private void ScheduledOnWednesday1MinuteAfterMarketOpen()
        {
            if (IsWarmingUp) return;

            if (_filterDividendPayers) UpdateDividendPayerCache();

            // First, we order by slope and we take top 20% ranked
            var sortedEquityListBySlope = _customIndicators.Where(x => x.Value.IsReady)
            .OrderByDescending(x => x.Value.AnnualizedSlope)
            .Take(_topNStockOfSp500)
            .ToList();
            // Second, we filter by minimum slope, above moving average and max gap,
            // and (flag on) by the capital-gain criterion: exclude TTM dividend payers.
            sortedEquityListBySlope = sortedEquityListBySlope
            .Where(x => x.Value.AnnualizedSlope > _minimumAnnualizedSlope
                && Securities[x.Key].Price > x.Value.MovingAverage
                && x.Value.Gap < _maximumGap
                && (!_filterDividendPayers || !_paysDividend.ContainsKey(x.Key))).ToList();

            //Sell if security is not in list
            foreach (var security in Portfolio.Values.Where(x => x.Invested))
            {
                var symbolHold = security.Symbol;
                if (!sortedEquityListBySlope.Exists(x => x.Value.Symbol == symbolHold))
                {
                    Liquidate(symbolHold);
                }
            }

            bool riskON = _marketRegimeFilter.RiskON(Securities["SPY"].Price);

            //Twice a month rebalance the positions sizes (risk);
            if (RebalanceWeek) {
                _rebalanceWeek = false;
                var risk = Portfolio.TotalPortfolioValue * RiskPerContractOnPortfolio;

                foreach (var security in Portfolio.Values.Where(x => x.Invested))
                {
                    var symbolHold = security.Symbol;
                    var quantityHold = security.Quantity;
                    var priceHold = Securities[symbolHold].Price;

                    foreach (var customIndicator in sortedEquityListBySlope.Where(x => x.Key == symbolHold))
                    {
                        var numberStocks = (int)Math.Floor(risk / customIndicator.Value.Atr);
                        if (Math.Abs(quantityHold - numberStocks) > 0 && quantityHold > 1)
                        {
                            // Sell or Buy the stocks diff
                            if (quantityHold > numberStocks)
                            {
                                Sell(symbolHold, (quantityHold - numberStocks));
                            }
                            else
                            {
                                //If the MarketRegimeIndicator indicator is RiskON, we buy stocks, otherwise not;
                                if (riskON)
                                {
                                    if (quantityHold < numberStocks)
                                    {
                                        decimal portfolioCashBalance = Portfolio.TotalPortfolioValue - Portfolio.TotalHoldingsValue;
                                        // Do we have cash to trade?
                                        if (portfolioCashBalance > ((numberStocks - quantityHold) * priceHold + (numberStocks - quantityHold) * priceHold * BrokerFee))
                                        {
                                            Order(symbolHold, (numberStocks - quantityHold));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            else { _rebalanceWeek = true; }

            //If the MarketRegimeIndicator indicator is RiskON, we buy stocks, otherwise not;
            if (riskON)
            {
                foreach (var customIndicatorItem in sortedEquityListBySlope)
                {
                    CustomMomentumIndicator customIndicator = customIndicatorItem.Value;
                    var symbol = customIndicator.Symbol;
                    var inPortfolio = false;
                    foreach (var security in Portfolio.Values.Where(x => x.Invested))
                    {
                        if (security.Symbol == symbol)
                        {
                            inPortfolio = true;
                        }
                    }
                    if (!inPortfolio)
                    {
                        var risk = Portfolio.TotalPortfolioValue * RiskPerContractOnPortfolio;
                        var numberStocks = (int)Math.Floor(risk / customIndicator.Atr);
                        var price = Securities[symbol].Price;
                        if (numberStocks > 0)
                        {
                            decimal portfolioCashBalance = Portfolio.TotalPortfolioValue - Portfolio.TotalHoldingsValue;
                            // Do we have cash to trade?
                            if (portfolioCashBalance > (numberStocks * price + (numberStocks * price) * BrokerFee))
                            {
                                Order(symbol, numberStocks);
                            }
                        }
                    }
                }
            }
        }

        // creating custom indicators for each symbol
        public override void OnSecuritiesChanged(SecurityChanges changes)
        {
            if (changes.AddedSecurities.Count > 0)
            {
                    foreach (Security security in changes.AddedSecurities)
                {
                    if (!_customIndicators.ContainsKey(security.Symbol) && (security.Symbol.Value != "SPY"))
                    {
                        var customIndicator = new CustomMomentumIndicator(security.Symbol, _annualizedSlopeWindow, _movingAverageWindow, _gapWindow, _atrWindow);
                        //warm up indicator
                        var history = History(security.Symbol, customIndicator.Window, Resolution.Daily);
                        foreach (TradeBar tradeBar in history)
                            customIndicator.Update(tradeBar);

                        _customIndicators.Add(security.Symbol, customIndicator);
                        RegisterIndicator(security.Symbol, customIndicator, Resolution.Daily);
                    }
                }
            }
            if (changes.RemovedSecurities.Count > 0)
            {
                foreach (var security in changes.RemovedSecurities)
                {
                    if (security.Invested)
                    {
                        Liquidate(security.Symbol);
                    }
                    if (_customIndicators.ContainsKey(security.Symbol))
                    {
                        _customIndicators.Remove(security.Symbol);
                    }
                }
            }
        }
    }
}
