using System;
using MyIA.Trading.Backtester;

namespace MyIA.Trading.Backtester
{
    public class SimpleStopStrategy : TradingStrategyBase
    {

        public Action<string> Logger { get; set; }
        private DateTime _WeeklyTargetMarket = DateTime.MinValue;

        public decimal StopRate { get; set; } = 0.2m;

        public TimeSpan RefactoryPeriod { get; set; } = TimeSpan.FromDays(5);

        private OrderType nextOrderType;
        private decimal currentStop;
        private Order lastOrder;
        private bool raiseRate;

        public override void ComputeNewOrders(ref TradingContext tContext)
        {

            //if (tContext.Market.Time > _WeeklyTargetMarket)
            //{
            //    _WeeklyTargetMarket = tContext.Market.Time.Add(TimeSpan.FromDays(7));
            //    Logger($"Date: {tContext.Market.Time}, Price: {tContext.Market.Ticker.Last}");
            //}
            Order newOrder = null;
            var currentPrice = tContext.Market.Ticker.Last;
            var objBalance = tContext.NewOrders.GetBalance(tContext.Market.Ticker);
            if (tContext.CurrentOrders.Orders.Count > 0)
            {
                throw new InvalidOperationException("strategy should not keep open orders");
            }

            if (currentStop == 0)
            {
                if (objBalance.Value > (objBalance.Secondary * 2))
                {
                    nextOrderType = OrderType.Sell;
                }
                else
                {
                    nextOrderType = OrderType.Buy;
                }
                currentStop = nextOrderType == OrderType.Buy ? currentPrice * (1 + StopRate) : currentPrice * (1 - StopRate);
            }

            if (lastOrder == null || tContext.Market.Time > lastOrder.Time + RefactoryPeriod)
            {
                if ((nextOrderType == OrderType.Buy && currentPrice > currentStop) || (nextOrderType == OrderType.Sell && currentPrice < currentStop))
                {

                    // stop hit, engage

                    //if ((nextOrderType == OrderType.Buy && lastOrder.Price<currentPrice) || (nextOrderType == OrderType.Sell && lastOrder.Price > currentPrice))
                    //{
                    //    // losing stop, change rate
                    //    //StopRate = raiseRate ? StopRate * 1.3m : StopRate / 1.3m;
                    //    //raiseRate = ((StopRate < 0.1m) || (StopRate > 0.4m)) ? !raiseRate : raiseRate;
                    //}
                    newOrder = Engage(ref tContext, nextOrderType);
                    nextOrderType = nextOrderType == OrderType.Buy ? OrderType.Sell : OrderType.Buy;
                    currentStop = nextOrderType == OrderType.Buy ? currentPrice * (1 + StopRate) : currentPrice * (1 - StopRate);
                }
                else
                {

                    //no stop, adjust if necessary

                    if (nextOrderType == OrderType.Buy)
                    {
                        var newStop = currentPrice * (1 + StopRate);
                        if (newStop < currentStop)
                        {
                            currentStop = newStop;
                        }
                    }
                    else
                    {
                        var newStop = currentPrice * (1 - StopRate);
                        if (newStop > currentStop)
                        {
                            currentStop = newStop;
                        }
                    }
                }

            }

            if (newOrder != null)
            {
                //Logger($"{this.GetType().Name}");
                //Logger($" Date: {tContext.Market.Time.ToString(CultureInfo.InvariantCulture)}, {newOrder.FriendlyId}, Wallet: {objBalance.Primary}BTC {objBalance.Secondary}USD, Total {objBalance.Total}USD   ");
                tContext.NewOrders.Orders.Add(newOrder);
                lastOrder = newOrder;
            }
        }


        private Order Engage(ref TradingContext tContext, OrderType orderType)
        {
            var objBalance = tContext.NewOrders.GetBalance(tContext.Market.Ticker);
            Order newOrder = null;
            if (orderType == OrderType.Sell)
            {
                if (objBalance.Value > (objBalance.Secondary * 2))
                {
                    var objPrice = tContext.Market.Ticker.Last * 0.99M;
                    newOrder = new Order() { OrderType = orderType, Price = objPrice, Amount = tContext.NewOrders.PrimaryBalance, Time = tContext.Market.Time};
                }
            }
            else
            {
                if (objBalance.Secondary > (objBalance.Value * 2))
                {
                    var objPrice = tContext.Market.Ticker.Last * 1.01M;
                    newOrder = new Order() { OrderType = orderType, Price = objPrice, Amount = tContext.NewOrders.SecondaryBalance / objPrice , Time = tContext.Market.Time };
                }
            }

            return newOrder;

        }
    }
}