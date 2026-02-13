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
    using QuantConnect.Algorithm.Framework.Portfolio.SignalExports;
    using QuantConnect.Algorithm.Framework.Execution;
    using QuantConnect.Algorithm.Framework.Risk;
    using QuantConnect.Algorithm.Selection;
    using QuantConnect.Api;
    using QuantConnect.Parameters;
    using QuantConnect.Benchmarks;
    using QuantConnect.Brokerages;
    using QuantConnect.Configuration;
    using QuantConnect.Util;
    using QuantConnect.Interfaces;
    using QuantConnect.Algorithm;
    using QuantConnect.Indicators;
    using QuantConnect.Data;
    using QuantConnect.Data.Auxiliary;
    using QuantConnect.Data.Consolidators;
    using QuantConnect.Data.Custom;
    using QuantConnect.Data.Custom.IconicTypes;
    using QuantConnect.DataSource;
    using QuantConnect.Data.Fundamental;
    using QuantConnect.Data.Market;
    using QuantConnect.Data.Shortable;
    using QuantConnect.Data.UniverseSelection;
    using QuantConnect.Notifications;
    using QuantConnect.Orders;
    using QuantConnect.Orders.Fees;
    using QuantConnect.Orders.Fills;
    using QuantConnect.Orders.OptionExercise;
    using QuantConnect.Orders.Slippage;
    using QuantConnect.Orders.TimeInForces;
    using QuantConnect.Python;
    using QuantConnect.Scheduling;
    using QuantConnect.Securities;
    using QuantConnect.Securities.Equity;
    using QuantConnect.Securities.Future;
    using QuantConnect.Securities.Option;
    using QuantConnect.Securities.Positions;
    using QuantConnect.Securities.Forex;
    using QuantConnect.Securities.Crypto;
    using QuantConnect.Securities.CryptoFuture;
    using QuantConnect.Securities.Interfaces;
    using QuantConnect.Securities.Volatility;
    using QuantConnect.Storage;
    using QuantConnect.Statistics;
    using QCAlgorithmFramework = QuantConnect.Algorithm.QCAlgorithm;
    using QCAlgorithmFrameworkBridge = QuantConnect.Algorithm.QCAlgorithm;
#endregion
namespace QuantConnect
{
    public class BtcEmaCrossDaily1Algorithm : QCAlgorithm
    {
        private Symbol _btcUsdSymbol;
        private readonly Resolution _resolution = Resolution.Daily;

        [Parameter("ema-fast")]
        public int FastPeriod = 18;

        [Parameter("ema-slow")]
        public int SlowPeriod = 23;

        [Parameter("ema-upcross-margin")]
        public decimal UpCrossMargin = 1.001m;

        [Parameter("ema-downcross-margin")]
        public decimal DownCrossMargin = 0.999m;

        private ExponentialMovingAverage _fastEma;
        private ExponentialMovingAverage _slowEma;

        private const string ChartName = "EMA Plot";
        private const string PriceSeriesName = "Price";
        private const string PortfolioValueSeriesName = "Portfolio Value";
        private const string FastEmaSeriesName = "Fast EMA";
        private const string SlowEmaSeriesName = "Slow EMA";

        public override void Initialize()
        {
            InitPeriod();
            SetWarmUp(TimeSpan.FromDays(Math.Max(FastPeriod, SlowPeriod)));
            SetBrokerageModel(BrokerageName.Binance, AccountType.Cash);
            SetAccountCurrency("USDT");
            SetCash(600000);
            DefaultOrderProperties = new BinanceOrderProperties
            {
                TimeInForce = TimeInForce.GoodTilCanceled,
                PostOnly = false
            };
            _btcUsdSymbol = AddCrypto("BTCUSDT", _resolution, Market.Binance).Symbol;
            _fastEma = EMA(_btcUsdSymbol, FastPeriod, _resolution);
            _slowEma = EMA(_btcUsdSymbol, SlowPeriod, _resolution);
            this.SetBenchmark(_btcUsdSymbol);
            InitializeCharts();
        }

        public override void OnData(Slice data)
        {
            if (IsWarmingUp || !_fastEma.IsReady || !_slowEma.IsReady)
                return;
            if (!data.ContainsKey(_btcUsdSymbol))
                return;
            var fastEmaValue = _fastEma.Current.Value;
            var slowEmaValue = _slowEma.Current.Value;
            if (!Portfolio.Invested && fastEmaValue > slowEmaValue * UpCrossMargin)
            {
                SetHoldings(_btcUsdSymbol, 1);
                Debug($"Achat de {_btcUsdSymbol} au prix de {Securities[_btcUsdSymbol].Price}");
            }
            else if (Portfolio.Invested && fastEmaValue < slowEmaValue * DownCrossMargin)
            {
                Liquidate(_btcUsdSymbol);
                Debug($"Vente de {_btcUsdSymbol} au prix de {Securities[_btcUsdSymbol].Price}");
            }
        }

        public override void OnOrderEvent(OrderEvent orderEvent)
        {
            if (orderEvent.Status == OrderStatus.Filled)
            {
                string operation = orderEvent.Direction == OrderDirection.Buy ? "Achat" : "Vente";
                var message = $"{Time.ToShortDateString()} - {operation} de {Math.Abs(orderEvent.FillQuantity)} unites de {_btcUsdSymbol} au prix de {orderEvent.FillPrice} USDT.";
                message += $" Valeur totale du portefeuille : {Portfolio.TotalPortfolioValue:N2} USDT.";
                Debug(message);
            }
        }

        private void InitializeCharts()
        {
            var chart = new Chart(ChartName);
            var priceSeries = new Series(PriceSeriesName, SeriesType.Line, "$", Color.Blue);
            var portfolioValueSeries = new Series(PortfolioValueSeriesName, SeriesType.Line, "$", Color.Green);
            var fastEmaSeries = new Series(FastEmaSeriesName, SeriesType.Line, "$", Color.Red);
            var slowEmaSeries = new Series(SlowEmaSeriesName, SeriesType.Line, "$", Color.Yellow);
            chart.AddSeries(priceSeries);
            chart.AddSeries(portfolioValueSeries);
            chart.AddSeries(fastEmaSeries);
            chart.AddSeries(slowEmaSeries);
            AddChart(chart);
            Schedule.On(DateRules.EveryDay(), TimeRules.At(0, 0), DoPlots);
        }

        private void DoPlots()
        {
            if (!Securities.ContainsKey(_btcUsdSymbol) || !Securities[_btcUsdSymbol].HasData)
                return;
            var price = Securities[_btcUsdSymbol].Price;
            var portfolioValue = Portfolio.TotalPortfolioValue;
            var fastEmaValue = _fastEma.Current.Value;
            var slowEmaValue = _slowEma.Current.Value;
            Plot(ChartName, PriceSeriesName, price);
            Plot(ChartName, PortfolioValueSeriesName, portfolioValue);
            Plot(ChartName, FastEmaSeriesName, fastEmaValue);
            Plot(ChartName, SlowEmaSeriesName, slowEmaValue);
        }

        private void InitPeriod()
        {
            SetStartDate(2021, 10, 16);
        }
    }
}
