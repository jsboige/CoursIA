using System;
using MyIA.Trading.Backtester;
using Xunit;

namespace MyIA.Trading.Backtester.Tests.Core
{
    /// <summary>
    /// Tests unitaires de Order (MyIA.Trading.Backtester.Core/Order.cs).
    /// Fichier porte verbatim depuis la tranche 2 (#7357), aucun test a ce jour.
    /// Surface testee :
    /// - constructeurs (sans argument, complet, complet + date)
    /// - getters/setters (Time, OrderType, IsCancel, Value)
    /// - IComparable&lt;Order&gt;.CompareTo (signature explicite, sur Price)
    /// - FriendlyId (concatene les champs)
    /// Comportements NON testes :
    /// - Equals/GetHashCode (non overrides -> reference, valeur non pertinente)
    /// - CompareDates / CompareOrderDates (static interne, exposure privee)
    /// </summary>
    public sealed class OrderTests
    {
        [Fact]
        public void DefaultConstructor_SetsOrderTypeToBuy()
        {
            var order = new Order();
            Assert.Equal(OrderType.Buy, order.OrderType);
            Assert.False(order.IsCancel);
        }

        [Fact]
        public void FullConstructor_AssignsAllProvidedFields()
        {
            var price = 123.45m;
            var amount = 0.5m;
            var order = new Order(OrderType.Sell, price, amount);

            Assert.Equal(OrderType.Sell, order.OrderType);
            Assert.Equal(price, order.Price);
            Assert.Equal(amount, order.Amount);
            Assert.False(order.IsCancel);
        }

        [Fact]
        public void ConstructorWithDate_StoresUnixTimestamp()
        {
            var date = new DateTime(2024, 1, 15, 12, 0, 0, DateTimeKind.Utc);
            var order = new Order(OrderType.Buy, 100m, 1m, date);

            Assert.Equal(MyIA.Trading.Backtester.UnixTime.ConvertToUnixTimestamp(date), order.Date);
        }

        [Fact]
        public void Value_IsProductOfPriceAndAmount()
        {
            var order = new Order(OrderType.Buy, 100m, 2.5m);
            Assert.Equal(250m, order.Value);
        }

        [Fact]
        public void Time_GetterSetterRoundTripsUnixTimestamp()
        {
            var original = new DateTime(2025, 6, 1, 0, 0, 0, DateTimeKind.Utc);
            var order = new Order { Time = original };
            Assert.Equal(original, order.Time);
        }

        [Fact]
        public void OrderType_GetterReturnsTypeUnlessIsCancel()
        {
            var order = new Order { Type = (int)OrderType.Sell };
            Assert.Equal(OrderType.Sell, order.OrderType);

            order.IsCancel = true;
            Assert.Equal(OrderType.Cancel, order.OrderType);
        }

        [Fact]
        public void OrderType_SetterCancelSetsIsCancelTrue()
        {
            var order = new Order();
            order.OrderType = OrderType.Cancel;
            Assert.True(order.IsCancel);
            Assert.NotEqual((int)OrderType.Cancel, order.Type);
        }

        [Fact]
        public void OrderType_SetterNonCancelStoresType()
        {
            var order = new Order { IsCancel = true };
            order.OrderType = OrderType.Buy;
            Assert.False(order.IsCancel);
            Assert.Equal((int)OrderType.Buy, order.Type);
        }

        [Fact]
        public void CompareTo_NegativeWhenThisPriceLower()
        {
            var a = new Order(OrderType.Buy, 100m, 1m);
            var b = new Order(OrderType.Buy, 110m, 1m);
            Assert.Equal(-1, ((IComparable<Order>)a).CompareTo(b));
        }

        [Fact]
        public void CompareTo_PositiveWhenThisPriceHigher()
        {
            var a = new Order(OrderType.Buy, 110m, 1m);
            var b = new Order(OrderType.Buy, 100m, 1m);
            Assert.Equal(1, ((IComparable<Order>)a).CompareTo(b));
        }

        [Fact]
        public void CompareTo_ZeroWhenPricesEqual()
        {
            var a = new Order(OrderType.Buy, 100m, 1m);
            var b = new Order(OrderType.Sell, 100m, 5m);
            // CompareTo ne regarde QUE Price, ignore OrderType et Amount.
            Assert.Equal(0, ((IComparable<Order>)a).CompareTo(b));
        }

        [Fact]
        public void FriendlyId_ContainsOidTypeAmountPrice()
        {
            var order = new Order(OrderType.Buy, 100m, 2m) { Oid = "OID-42" };
            string id = order.FriendlyId;
            Assert.Contains("OID-42", id);
            Assert.Contains("Buy", id);
            Assert.Contains("100", id);
            Assert.Contains("2", id);
        }
    }
}
