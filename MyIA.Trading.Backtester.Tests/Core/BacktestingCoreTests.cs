using System;
using System.Collections.Generic;
using MyIA.Trading.Backtester;
using Xunit;

namespace MyIA.Trading.Backtester.Tests.Core
{
    public sealed class BacktestingCoreTests
    {
        [Fact]
        public void WalletClone_CopiesMutableCollections()
        {
            var wallet = new Wallet
            {
                PrimaryBalance = 2m,
                SecondaryBalance = 500m,
                Orders = new List<Order>
                {
                    new Order(OrderType.Buy, 100m, 1m)
                }
            };
            wallet.LastTrades.Add(new OrderTrade { Price = 100m, Amount = 1m });
            wallet.LastTransactions.Add(new Transaction { Amount = 25m });

            var clone = (Wallet)wallet.Clone();
            clone.Orders.Clear();
            clone.LastTrades.Clear();
            clone.LastTransactions.Clear();

            Assert.Single(wallet.Orders);
            Assert.Single(wallet.LastTrades);
            Assert.Single(wallet.LastTransactions);
            Assert.Equal(wallet.PrimaryBalance, clone.PrimaryBalance);
            Assert.Equal(wallet.SecondaryBalance, clone.SecondaryBalance);
        }

        [Fact]
        public void MatchOrders_ReturnsOnlyOrdersCrossingMarketPrice()
        {
            var wallet = new Wallet
            {
                Orders = new List<Order>
                {
                    new Order(OrderType.Buy, 110m, 1m),
                    new Order(OrderType.Buy, 90m, 1m),
                    new Order(OrderType.Sell, 80m, 1m),
                    new Order(OrderType.Sell, 120m, 1m)
                }
            };
            var exchange = new ExchangeInfo();

            var matches = exchange.MatchOrders(ref wallet, 100m);

            Assert.Equal(2, matches.Count);
            Assert.Contains(matches, order => order.OrderType == OrderType.Buy && order.Price == 110m);
            Assert.Contains(matches, order => order.OrderType == OrderType.Sell && order.Price == 80m);
        }

        [Fact]
        public void ExecuteOrders_AppliesBalancesFeesAndHistory()
        {
            var executionTime = new DateTime(2025, 1, 1, 12, 0, 0, DateTimeKind.Utc);
            var wallet = new Wallet
            {
                PrimaryBalance = 10m,
                SecondaryBalance = 1_000m,
                Orders = new List<Order>
                {
                    new Order(OrderType.Buy, 110m, 2m),
                    new Order(OrderType.Sell, 90m, 1m)
                }
            };
            var market = new MarketInfo(executionTime, new Ticker(100m), null, null)
            {
                PrimaryCode = "BTC",
                SecondaryCode = "USD"
            };
            var exchange = new ExchangeInfo
            {
                BidCommission = 1m,
                AskCommission = 2m
            };
            var history = new TradingHistory();

            exchange.ExecuteOrders(market, ref wallet, ref history);

            Assert.Equal(10.98m, wallet.PrimaryBalance);
            Assert.Equal(868.20m, wallet.SecondaryBalance);
            Assert.Empty(wallet.Orders);
            Assert.Equal(executionTime, wallet.Time);
            Assert.Equal(2, history.Trades.Count);
            Assert.Equal(2, history.Fees.Count);
            Assert.Equal(0.02m, history.Fees[0].Amount);
            Assert.Equal(1.80m, history.Fees[1].Amount);
        }

        [Fact]
        public void MarketDepth_BidsDeserializeAsBuyOrders()
        {
            var depth = new MarketDepth
            {
                Bids = new[] { new[] { 99m, 2m, 0m } }
            };

            Assert.Single(depth.BidOrders);
            Assert.Equal(OrderType.Buy, depth.BidOrders[0].OrderType);
        }

        [Fact]
        public void TradingSeries_RespectsPeriodAndMaximumSize()
        {
            var start = new DateTime(2025, 1, 1, 0, 0, 0, DateTimeKind.Utc);
            var series = new TradingSeries(2, TimeSpan.FromMinutes(5));

            series.AddEvent(CreateEvent(start, 100m));
            series.AddEvent(CreateEvent(start.AddMinutes(3), 101m));
            series.AddEvent(CreateEvent(start.AddMinutes(6), 102m));
            series.AddEvent(CreateEvent(start.AddMinutes(12), 103m));

            Assert.Equal(2, series.Instances.Count);
            Assert.Equal(start.AddMinutes(12), series.Instances[0].Time);
            Assert.Equal(start.AddMinutes(6), series.Instances[1].Time);
        }

        [Fact]
        public void ExchangeSimulator_DoesNotUseFutureTradePrice()
        {
            var start = new DateTime(2025, 1, 1, 0, 0, 0, DateTimeKind.Utc);
            var simulator = new ExchangeSimulator
            {
                Trades = new List<OrderTrade>
                {
                    new OrderTrade { Time = start, Price = 100m, Amount = 1m },
                    new OrderTrade { Time = start.AddMinutes(10), Price = 150m, Amount = 1m }
                }
            };

            var market = simulator.GetMarket(start.AddMinutes(5));

            Assert.Equal(100m, market.Ticker.Last);
            Assert.Single(market.RecentTrades);
        }

        [Fact]
        public void RunSimulations_KeepsSetupsIndependent()
        {
            var trades = CreateTrades();
            var firstStrategy = new CountingStrategy();
            var secondStrategy = new CountingStrategy();
            var firstWallet = new Wallet { PrimaryBalance = 1m, SecondaryBalance = 100m };
            var secondWallet = new Wallet { PrimaryBalance = 2m, SecondaryBalance = 200m };
            var setups = new List<SimulationSetup>
            {
                new SimulationSetup { Walllet = firstWallet, Strategy = firstStrategy },
                new SimulationSetup { Walllet = secondWallet, Strategy = secondStrategy }
            };
            var simulation = CreateSimulation(trades, TimeSpan.FromMinutes(5));

            var histories = simulation.RunSimulations(setups, new ExchangeInfo(), trades);

            Assert.Equal(2, histories.Count);
            Assert.NotSame(histories[0], histories[1]);
            Assert.Equal(firstStrategy.CallCount, secondStrategy.CallCount);
            Assert.True(firstStrategy.CallCount > 0);
            Assert.Equal(1m, setups[0].Walllet.PrimaryBalance);
            Assert.Equal(2m, setups[1].Walllet.PrimaryBalance);
        }

        [Fact]
        public void RunSimulation_BotPeriodControlsStrategyFrequency()
        {
            var trades = CreateTrades();
            var frequentStrategy = new CountingStrategy();
            var sparseStrategy = new CountingStrategy();

            CreateSimulation(trades, TimeSpan.FromMinutes(5)).RunSimulation(
                new Wallet(), frequentStrategy, new ExchangeInfo(), trades);
            CreateSimulation(trades, TimeSpan.FromMinutes(10)).RunSimulation(
                new Wallet(), sparseStrategy, new ExchangeInfo(), trades);

            Assert.Equal(4, frequentStrategy.CallCount);
            Assert.Equal(2, sparseStrategy.CallCount);
        }

        private static TradingEvent CreateEvent(DateTime time, decimal total)
        {
            return new TradingEvent(time, new Balance(0m, new Ticker(1m), total));
        }

        private static List<OrderTrade> CreateTrades()
        {
            var start = new DateTime(2025, 1, 1, 0, 0, 0, DateTimeKind.Utc);
            return new List<OrderTrade>
            {
                new OrderTrade { Time = start, Price = 100m, Amount = 1m },
                new OrderTrade { Time = start.AddMinutes(6), Price = 101m, Amount = 1m },
                new OrderTrade { Time = start.AddMinutes(12), Price = 102m, Amount = 1m },
                new OrderTrade { Time = start.AddMinutes(18), Price = 103m, Amount = 1m },
                new OrderTrade { Time = start.AddMinutes(24), Price = 104m, Amount = 1m }
            };
        }

        private static SimulationInfo CreateSimulation(IReadOnlyList<OrderTrade> trades, TimeSpan botPeriod)
        {
            return new SimulationInfo
            {
                StartDate = trades[0].Time.AddSeconds(-1),
                EndDate = trades[^1].Time.AddSeconds(-1),
                BotPeriod = botPeriod,
                FastSimulation = false
            };
        }

        private sealed class CountingStrategy : ITradingStrategy
        {
            public int CallCount { get; private set; }

            public Wallet ComputeNewOrders(
                Wallet currentOrders,
                MarketInfo objMarket,
                ExchangeInfo objExchange,
                TradingHistory history)
            {
                CallCount++;
                return new Wallet();
            }
        }
    }
}
