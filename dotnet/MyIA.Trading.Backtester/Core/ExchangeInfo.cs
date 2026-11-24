using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;

namespace MyIA.Trading.Backtester
{
    [Serializable]
    public class ExchangeInfo
    {
        public int AmountDecil { get; set; }

        public decimal AskCommission { get; set; }

        public decimal BidCommission { get; set; }

        public decimal MinOrderAmount { get; set; }

        public decimal MinOrderValue { get; set; }

        public int PriceDecil { get; set; }

        public Dictionary<TradingAPIUrls, string> TradingUrls { get; set; }

        public ExchangeInfo()
        {
            MinOrderAmount = new decimal(1, 0, 0, false, 1);
            MinOrderValue = 0m;
            AskCommission = new decimal(65, 0, 0, false, 2);
            BidCommission = new decimal(65, 0, 0, false, 2);
            AmountDecil = 1;
            PriceDecil = 5;
            TradingUrls = new Dictionary<TradingAPIUrls, string>();
        }

        public void ExecuteOrders(MarketInfo objMarket, ref Wallet targetWallet, ref TradingHistory history)
        {
            var trades = new List<OrderTrade>();
            var fees = new List<Payment>();
            var matchedOrders = MatchOrders(ref targetWallet, objMarket.Ticker.Last);
            foreach (var matchedOrder in matchedOrders)
            {
                var trade = new OrderTrade
                {
                    Time = objMarket.Time,
                    Price = matchedOrder.Price,
                    Amount = matchedOrder.Amount
                };
                var fee = new Payment
                {
                    Time = objMarket.Time,
                    Label = matchedOrder.FriendlyId
                };

                if (matchedOrder.OrderType == OrderType.Buy)
                {
                    trade.TradeType = TradeType.Buy;
                    fee.Currency = objMarket.PrimaryCode;
                    fee.Amount = matchedOrder.Amount * BidCommission / 100m;
                    fee.Label = string.Format(
                        "{0} - Bid Fee: {1} % = {2} {3}",
                        fee.Label,
                        BidCommission.ToString(CultureInfo.InvariantCulture),
                        fee.Amount,
                        fee.Currency);
                    targetWallet.SecondaryBalance -= matchedOrder.Value;
                    targetWallet.PrimaryBalance += matchedOrder.Amount - fee.Amount;
                }
                else if (matchedOrder.OrderType == OrderType.Sell)
                {
                    trade.TradeType = TradeType.Sell;
                    fee.Currency = objMarket.SecondaryCode;
                    fee.Amount = matchedOrder.Value * AskCommission / 100m;
                    fee.Label = string.Format(
                        "{0} - Ask Fee: {1} % = {2} {3}",
                        fee.Label,
                        AskCommission.ToString(CultureInfo.InvariantCulture),
                        fee.Amount,
                        fee.Currency);
                    targetWallet.SecondaryBalance += matchedOrder.Value - fee.Amount;
                    targetWallet.PrimaryBalance -= matchedOrder.Amount;
                }

                trades.Add(trade);
                fees.Add(fee);
                targetWallet.Orders.Remove(matchedOrder);
            }

            targetWallet.Time = objMarket.Time;
            history.Update(targetWallet, objMarket, trades, fees);
        }

        public ExchangeInfo FromCustomFees(decimal newCommission)
        {
            return FromCustomFees(newCommission, newCommission);
        }

        public ExchangeInfo FromCustomFees(decimal askFee, decimal bidFee)
        {
            return new ExchangeInfo
            {
                MinOrderAmount = MinOrderAmount,
                MinOrderValue = MinOrderValue,
                AmountDecil = AmountDecil,
                PriceDecil = PriceDecil,
                TradingUrls = TradingUrls,
                AskCommission = askFee,
                BidCommission = bidFee
            };
        }

        public List<Order> MatchOrders(ref Wallet objWallet, decimal price)
        {
            var matches = objWallet.OrderedBids.Where(order => order.Price > price).ToList();
            matches.AddRange(objWallet.OrderedAsks.Where(order => order.Price < price));
            return matches;
        }
    }
}
