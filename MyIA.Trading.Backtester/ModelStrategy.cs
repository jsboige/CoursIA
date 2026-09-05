using System;
using System.Collections.Generic;
using System.Globalization;
using Accord.MachineLearning;
using MyIA.Trading.Backtester;

namespace MyIA.Trading.Backtester
{
    public class ModelStrategy : TradingStrategyBase
    {

        public string FriendlyId => $"{TrainingConfig.GetModelName()}";

        public Action<string> Logger { get; set; }

        public TradingTrainingConfig TrainingConfig { get; set; }
        public ITradingModel Model { get; set; }

        private DateTime _TargetTime = DateTime.MinValue;

        protected Order TargetOrder;

        private DateTime _WeeklyTargetMarket = DateTime.MinValue;
        public override void ComputeNewOrders(ref TradingContext tContext)
        {
            if (tContext.Market.Time> _WeeklyTargetMarket)
            {
                _WeeklyTargetMarket = tContext.Market.Time.Add(TimeSpan.FromDays(7));
                Logger($"Date: {tContext.Market.Time}, Price: {tContext.Market.Ticker.Last}");
            }
            Order newOrder = null;
            var objBalance = tContext.NewOrders.GetBalance(tContext.Market.Ticker);
            if (tContext.CurrentOrders.Orders.Count > 0)
            {
                foreach (Order order in tContext.CurrentOrders.Orders)
                {
                    tContext.NewOrders.CancelExistingOrders(order);

                    if (order.OrderType == OrderType.Sell)
                    {
                        var objPrice = tContext.Market.Ticker.Last * 0.995M;
                        newOrder = new Order() { OrderType = OrderType.Sell, Price = objPrice, Amount = tContext.NewOrders.PrimaryBalance };
                    }
                    else
                    {

                        var objPrice = tContext.Market.Ticker.Last * 1.005M;
                        newOrder = new Order() { OrderType = OrderType.Buy, Price = objPrice, Amount = tContext.NewOrders.SecondaryBalance / objPrice };

                    }

                }
                //_TargetTime = DateTime.MinValue;
            }
            else
            {
                if (tContext.Market.Time > _TargetTime)
                {
                    if (TargetOrder != null)
                    {
                        if (
                            //    (_TargetOrder.OrderType == OrderType.Sell && tContext.Market.Ticker.Last / _TargetOrder.Price < (1 - TrainingConfig.OutputThresold)/100)
                            //|| (_TargetOrder.OrderType == OrderType.Buy && tContext.Market.Ticker.Last / _TargetOrder.Price > (1 + TrainingConfig.OutputThresold) / 100)
                            (TargetOrder.OrderType == OrderType.Sell && tContext.Market.Ticker.Last < TargetOrder.Price * (100 - TrainingConfig.StopLossRate) / 100)
                            || (TargetOrder.OrderType == OrderType.Buy && tContext.Market.Ticker.Last > TargetOrder.Price * (100 + TrainingConfig.StopLossRate) / 100)
                            )
                        {
                            Logger($" Date: {tContext.Market.Time.ToString(CultureInfo.InvariantCulture)}, Cancellation {tContext.Market.Ticker.Last} vs {TargetOrder.Price}, Wallet: {objBalance.Primary}BTC {objBalance.Secondary}USD, Total {objBalance.Total}USD   ");
                            newOrder = Engage(ref tContext, TargetOrder.OrderType);
                            TargetOrder = null;
                        }
                    }
                    if (newOrder == null)
                    {
                        var objSample = TrainingConfig.DataConfig.SampleConfig.CreateInput(tContext.Market.RecentTrades, tContext.Market.RecentTrades.Count - 1);
                        if (objSample != null)
                        {
                            var objInputs = TrainingConfig.DataConfig.GetTrainingData(objSample);

                            var result = GetResult(objInputs, tContext.Market.Time);
                            switch (result)
                            {
                                case 1:
                                    newOrder = Engage(ref tContext, OrderType.Buy);
                                    break;
                                case 2:
                                    newOrder = Engage(ref tContext, OrderType.Sell);
                                    break;
                            }

                        }
                    }

                }

            }
            if (newOrder != null)
            {
                Logger($"{FriendlyId}");
                Logger($" Date: {tContext.Market.Time.ToString(CultureInfo.InvariantCulture)}, {newOrder.FriendlyId}, Wallet: {objBalance.Primary}BTC {objBalance.Secondary}USD, Total {objBalance.Total}USD   ");
                tContext.NewOrders.Orders.Add(newOrder);
            }


        }

        public virtual int GetResult(TradingTrainingSample objInputs, DateTime time)
        {
            var objData = new List<TradingTrainingSample>();
            objData.Add(objInputs);
            var result = Model.Predict(objData);
            return (int)result[0].Output;
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
                    newOrder = new Order() { OrderType = orderType, Price = objPrice, Amount = tContext.NewOrders.PrimaryBalance };
                }
            }
            else
            {
                if (objBalance.Secondary > (objBalance.Value * 2))
                {
                    var objPrice = tContext.Market.Ticker.Last * 1.01M;
                    newOrder = new Order() { OrderType = orderType, Price = objPrice, Amount = tContext.NewOrders.SecondaryBalance / objPrice };
                }
            }
            if (newOrder != null)
            {
                _TargetTime = tContext.Market.Time.Add(TrainingConfig.DataConfig.OutputPrediction);
                decimal targetPrice;
                if (newOrder.OrderType == OrderType.Buy)
                {
                    targetPrice = newOrder.Price; /*objBalance.Ticker.Last * (1 + TrainingConfig.OutputThresold / 100);*/
                    TargetOrder = new Order() { OrderType = OrderType.Sell, Price = targetPrice, Amount = tContext.NewOrders.PrimaryBalance };
                }
                else
                {
                    targetPrice = newOrder.Price;// objBalance.Ticker.Last * (1 - TrainingConfig.OutputThresold / 100);
                    TargetOrder = new Order() { OrderType = OrderType.Buy, Price = targetPrice, Amount = tContext.NewOrders.SecondaryBalance / targetPrice };
                }

            }
            return newOrder;

        }

    }


}
