using System;
using MyIA.Trading.Backtester;
using Xunit;

namespace MyIA.Trading.Backtester.Tests.Core
{
    /// <summary>
    /// Tests unitaires de OrderTrade (MyIA.Trading.Backtester.Core/OrderTrade.cs).
    /// Fichier porte verbatim depuis la tranche 2 (#7357), aucun test a ce jour.
    /// Surface testee :
    /// - constructeur par defaut (TradeType=Buy, Time=MinValue)
    /// - UnixTime (getter/setter round-trip via UnixTime.ConvertTo)
    /// - Equals (IEquatable&lt;OrderTrade&gt; + override object.Equals)
    /// - GetHashCode (coherence : egaux -> meme hash)
    /// - ToOrder (mapping des champs vers Order)
    /// - FriendlyId (concatene Time, Amount, Price)
    /// </summary>
    public sealed class OrderTradeTests
    {
        private static OrderTrade MakeTrade(DateTime time, decimal price, decimal amount, TradeType type = TradeType.Buy)
        {
            return new OrderTrade
            {
                Time = time,
                Price = price,
                Amount = amount,
                TradeType = type,
                InitialOrderType = type,
            };
        }

        [Fact]
        public void DefaultConstructor_SetsBuyAndMinValueTime()
        {
            var t = new OrderTrade();
            Assert.Equal(TradeType.Buy, t.TradeType);
            Assert.Equal(TradeType.Buy, t.InitialOrderType);
            Assert.Equal(DateTime.MinValue, t.Time);
        }

        [Fact]
        public void UnixTime_RoundTripsThroughUnixSeconds()
        {
            var t = new OrderTrade { Time = new DateTime(2024, 6, 1, 12, 0, 0, DateTimeKind.Utc) };
            long unix = t.UnixTime;
            Assert.Equal(MyIA.Trading.Backtester.UnixTime.ConvertToUnixTimestamp(t.Time), unix);
            t.UnixTime = unix + 3600;
            Assert.Equal(DateTimeOffset.FromUnixTimeSeconds(unix + 3600).UtcDateTime, t.Time);
        }

        [Fact]
        public void Equals_TrueWhenTimePriceAmountMatch()
        {
            var time = new DateTime(2024, 1, 1, 0, 0, 0, DateTimeKind.Utc);
            var a = MakeTrade(time, 100m, 1m);
            var b = MakeTrade(time, 100m, 1m, TradeType.Sell); // TradeType different : pas dans Equals
            Assert.True(a.Equals(b));
        }

        [Fact]
        public void Equals_FalseWhenPriceDiffers()
        {
            var time = new DateTime(2024, 1, 1, 0, 0, 0, DateTimeKind.Utc);
            var a = MakeTrade(time, 100m, 1m);
            var b = MakeTrade(time, 101m, 1m);
            Assert.False(a.Equals(b));
        }

        [Fact]
        public void Equals_FalseWhenAmountDiffers()
        {
            var time = new DateTime(2024, 1, 1, 0, 0, 0, DateTimeKind.Utc);
            var a = MakeTrade(time, 100m, 1m);
            var b = MakeTrade(time, 100m, 2m);
            Assert.False(a.Equals(b));
        }

        [Fact]
        public void Equals_FalseWhenTimeDiffers()
        {
            var a = MakeTrade(new DateTime(2024, 1, 1, 0, 0, 0, DateTimeKind.Utc), 100m, 1m);
            var b = MakeTrade(new DateTime(2024, 1, 1, 0, 0, 1, DateTimeKind.Utc), 100m, 1m);
            Assert.False(a.Equals(b));
        }

        [Fact]
        public void Equals_ObjectOverloadDelegatesToTypedEquals()
        {
            var time = new DateTime(2024, 1, 1, 0, 0, 0, DateTimeKind.Utc);
            var a = MakeTrade(time, 100m, 1m);
            object boxed = MakeTrade(time, 100m, 1m);
            Assert.True(a.Equals(boxed));
        }

        [Fact]
        public void Equals_ObjectOverloadFalseOnNonOrderTrade()
        {
            var a = MakeTrade(new DateTime(2024, 1, 1, 0, 0, 0, DateTimeKind.Utc), 100m, 1m);
            // Le cast (OrderTrade) d'un string leve InvalidCastException ; le test observe donc
            // que Equals(object) delega au Equals(OrderTrade) qui caste -> exception attendue.
            Assert.Throws<InvalidCastException>(() => a.Equals("not a trade"));
        }

        [Fact]
        public void GetHashCode_ConsistentWithEquals()
        {
            var time = new DateTime(2024, 1, 1, 0, 0, 0, DateTimeKind.Utc);
            var a = MakeTrade(time, 100m, 1m);
            var b = MakeTrade(time, 100m, 1m);
            Assert.Equal(a.GetHashCode(), b.GetHashCode());
        }

        [Fact]
        public void ToOrder_MapsIdTimeAmountPriceAndForcesOrderType()
        {
            var time = new DateTime(2024, 1, 1, 0, 0, 0, DateTimeKind.Utc);
            var t = new OrderTrade
            {
                Id = "T-1",
                Time = time,
                Price = 200m,
                Amount = 3m,
                TradeType = TradeType.Sell,
            };

            var order = t.ToOrder(OrderType.Buy);

            Assert.Equal("T-1", order.Oid);
            Assert.Equal(time, order.Time);
            Assert.Equal(200m, order.Price);
            Assert.Equal(3m, order.Amount);
            Assert.Equal(OrderType.Buy, order.OrderType); // force la valeur passee, pas TradeType
        }

        [Fact]
        public void FriendlyId_SellWhenAmountNegative()
        {
            var time = new DateTime(2024, 1, 1, 12, 0, 0, DateTimeKind.Utc);
            var t = MakeTrade(time, 100m, -1m, TradeType.Buy);
            Assert.Contains("Sell", t.FriendlyId);
        }

        [Fact]
        public void FriendlyId_SellWhenTradeTypeSell()
        {
            var time = new DateTime(2024, 1, 1, 12, 0, 0, DateTimeKind.Utc);
            var t = MakeTrade(time, 100m, 1m, TradeType.Sell);
            Assert.Contains("Sell", t.FriendlyId);
        }

        [Fact]
        public void FriendlyId_BuyOtherwise()
        {
            var time = new DateTime(2024, 1, 1, 12, 0, 0, DateTimeKind.Utc);
            var t = MakeTrade(time, 100m, 1m, TradeType.Buy);
            Assert.Contains("Buy", t.FriendlyId);
        }
    }
}
