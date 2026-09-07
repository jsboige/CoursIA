using System;

namespace MyIA.Trading.Backtester
{
    /// <summary>
    /// Strategie de market-making par bande : maintien d'une bande d'ordres ask/bid
    /// autour du dernier prix, dont prix et montants sont calcules par expressions
    /// dynamiques (SimpleExpression) evaluees contre le contexte. Les attributs de
    /// grille UI DNN (ExtendedCategory, ConditionalVisible, AutoPostBack) du port
    /// d'origine ne sont pas portes : ils ne portaient que de l'affichage.
    /// </summary>
    [Serializable]
    public class TradingStrategy : TradingStrategyBase
    {
        private const string ConstantDistribNextAsk = "Price + 0.10";

        private const string ConstantDistribNextBid = "Price - 0.10";

        private const string ConstantDistribMinAsk = "LowestAsk.price - 0.10";

        private const string ConstantDistribMaxBid = "HighestBid.price + 0.10";

        private const string LinearDistribNextAsk = "Price * 100 / 99";

        private const string LinearDistribNextBid = "Price * 99 / 100";

        private const string LinearDistribMinAsk = "LowestAsk.price * 99 / 100";

        private const string LinearDistribMaxBid = "HighestBid.price * 100 / 99";

        private const string ExponentialDistribNextAsk = "2*Price - Market.Ticker.Last";

        private const string ExponentialDistribNextBid = "2*Price - Market.Ticker.Last";

        private const string ExponentialDistribMinAsk = "(LowestAsk.price + Market.Ticker.Last)/2";

        private const string ExponentialDistribMaxBid = "(HighestBid.price + Market.Ticker.Last)/2";

        private OrdersDistribution _ordersDistribution;

        public bool AccountForTrend { get; set; }

        public decimal AdjustOrderLimitRate { get; set; }

        public SimpleExpression<decimal> AskOrderAmountExpression { get; set; }

        public SimpleExpression<decimal> BidOrderAmountExpression { get; set; }

        public decimal CancelOrderLimitRate { get; set; }

        public decimal DefaultBandWidthRate { get; set; }

        public decimal DefaultMaxOrderValueRate { get; set; }

        public override decimal LimitOrderMarginRate
        {
            get
            {
                return base.LimitOrderMarginRate;
            }
            set
            {
                base.LimitOrderMarginRate = value;
            }
        }

        public decimal LimitOrderValueRate { get; set; }

        public decimal MaxBandWidthRate { get; set; }

        public SimpleExpression<decimal> MaxBidOrderPriceExpression { get; set; }

        public SimpleExpression<decimal> MinAskOrderPriceExpression { get; set; }

        public decimal MinBandWidthRate { get; set; }

        public SimpleExpression<decimal> NextAskOrderPriceExpression { get; set; }

        public SimpleExpression<decimal> NextBidOrderPriceExpression { get; set; }

        public OrdersDistribution OrdersDistribution
        {
            get
            {
                switch (this._ordersDistribution)
                {
                    case OrdersDistribution.Constant:
                        {
                            if (!(NextAskOrderPriceExpression.Expression == ConstantDistribNextAsk
                                && NextBidOrderPriceExpression.Expression == ConstantDistribNextBid
                                && MinAskOrderPriceExpression.Expression == ConstantDistribMinAsk
                                && MaxBidOrderPriceExpression.Expression == ConstantDistribMaxBid))
                            {
                                this._ordersDistribution = OrdersDistribution.Custom;
                            }
                            break;
                        }
                    case OrdersDistribution.Linear:
                        {
                            if (!(NextAskOrderPriceExpression.Expression == LinearDistribNextAsk
                                && NextBidOrderPriceExpression.Expression == LinearDistribNextBid
                                && MinAskOrderPriceExpression.Expression == LinearDistribMinAsk
                                && MaxBidOrderPriceExpression.Expression == LinearDistribMaxBid))
                            {
                                this._ordersDistribution = OrdersDistribution.Custom;
                            }
                            break;
                        }
                    case OrdersDistribution.Exponential:
                        {
                            if (!(NextAskOrderPriceExpression.Expression == ExponentialDistribNextAsk
                                && NextBidOrderPriceExpression.Expression == ExponentialDistribNextBid
                                && MinAskOrderPriceExpression.Expression == ExponentialDistribMinAsk
                                && MaxBidOrderPriceExpression.Expression == ExponentialDistribMaxBid))
                            {
                                this._ordersDistribution = OrdersDistribution.Custom;
                            }
                            break;
                        }
                }
                return this._ordersDistribution;
            }
            set
            {
                if (value != this._ordersDistribution)
                {
                    this._ordersDistribution = value;
                    switch (value)
                    {
                        case OrdersDistribution.Constant:
                            {
                                NextAskOrderPriceExpression.Expression = ConstantDistribNextAsk;
                                NextBidOrderPriceExpression.Expression = ConstantDistribNextBid;
                                MinAskOrderPriceExpression.Expression = ConstantDistribMinAsk;
                                MaxBidOrderPriceExpression.Expression = ConstantDistribMaxBid;
                                break;
                            }
                        case OrdersDistribution.Linear:
                            {
                                this.NextAskOrderPriceExpression.Expression = LinearDistribNextAsk;
                                this.NextBidOrderPriceExpression.Expression = LinearDistribNextBid;
                                this.MinAskOrderPriceExpression.Expression = LinearDistribMinAsk;
                                this.MaxBidOrderPriceExpression.Expression = LinearDistribMaxBid;
                                break;
                            }
                        case OrdersDistribution.Exponential:
                            {
                                this.NextAskOrderPriceExpression.Expression = ExponentialDistribNextAsk;
                                this.NextBidOrderPriceExpression.Expression = ExponentialDistribNextBid;
                                this.MinAskOrderPriceExpression.Expression = ExponentialDistribMinAsk;
                                this.MaxBidOrderPriceExpression.Expression = ExponentialDistribMaxBid;
                                break;
                            }
                    }
                }
            }
        }

        public override bool TakeMarginOnOppositeOrder
        {
            get
            {
                return base.TakeMarginOnOppositeOrder;
            }
            set
            {
                base.TakeMarginOnOppositeOrder = value;
            }
        }

        public TradingBandDirection TradingBandDirection { get; set; }

        public decimal VolumeGrowthLimitFactor { get; set; }

        public decimal VolumeGrowthRate { get; set; }

        public decimal VolumeResetLimitFactor { get; set; }

        public TradingStrategy()
        {
            this.DefaultBandWidthRate = 30m;
            this.MinBandWidthRate = 10m;
            this.MaxBandWidthRate = 40m;
            this.DefaultMaxOrderValueRate = 10m;
            this.LimitOrderValueRate = 10m;
            this.AccountForTrend = true;
            this.TradingBandDirection = TradingBandDirection.Outwards;
            this.NextAskOrderPriceExpression = new SimpleExpression<decimal>("Price * 100 / 99");
            this.NextBidOrderPriceExpression = new SimpleExpression<decimal>("Price * 99 / 100");
            this.MinAskOrderPriceExpression = new SimpleExpression<decimal>("LowestAsk.price * 99 / 100");
            this.MaxBidOrderPriceExpression = new SimpleExpression<decimal>("HighestBid.price * 100 / 99");
            this.AskOrderAmountExpression = new SimpleExpression<decimal>("(CurrentOrders.HighestAsk.Value * (1 - Strategy.LimitOrderValueRate / 100) / AskSpan) + (((CurrentOrders.HighestAsk.Value * Strategy.LimitOrderValueRate / 100) - (LowestAskLimitPrice * CurrentOrders.HighestAsk.Value * (1 - Strategy.LimitOrderValueRate / 100) / AskSpan))/ Price)");
            this.BidOrderAmountExpression = new SimpleExpression<decimal>("(CurrentOrders.LowestBid.Value * ((Strategy.LimitOrderValueRate / 100) - 1) / BidSpan) + ((CurrentOrders.LowestBid.Value * Strategy.LimitOrderValueRate / 100) - (HighestBidLimitPrice * CurrentOrders.LowestBid.Value * ((Strategy.LimitOrderValueRate / 100) - 1) / BidSpan))/ Price");
            this.VolumeResetLimitFactor = 1m;
            this.VolumeGrowthLimitFactor = 10m;
            this.VolumeGrowthRate = 5m;
            this.AdjustOrderLimitRate = 85m;
            this.CancelOrderLimitRate = 95m;
        }

        public override void ComputeNewOrders(ref TradingContext tContext)
        {
            tContext = new BandTradingContext(tContext);

            //this is because some user defined expressions are computed in loops:
            // we don't want the algorithm to get stuck in an infinite loop
            int safetyCounter = 0;

            // First we deal with asks

            if (!this.NoAsks)
            {
                if (tContext.CurrentOrders.OrderedAsks.Count == 0)
                {
                    if (this.AccountForTrend || tContext.LastTrend != TradingTrend.Ask)
                    {
                        // There is no asks order yet/anymore, define a single new ask order

                        //Compute price from current ticker and strategy
                        var newHighAskPrice = tContext.Market.Ticker.Last * (1m + DefaultBandWidthRate / 100m);

                        var newOrder = new Order()
                        {
                            OrderType = OrderType.Sell,
                            Price = newHighAskPrice,
                            //compute amount from available balance and strategy
                            Amount = (tContext.NewOrders.PrimaryBalance * tContext.Market.Ticker.Last / newHighAskPrice)
                            * DefaultMaxOrderValueRate / 100m
                        };
                        tContext.NewOrders.Orders.Add(newOrder);
                    }
                }
                // else: There are asks orders already, we'll base new orders according to the existing
                else if (tContext.CurrentOrders.HighestAsk.Price
                        < tContext.Market.Ticker.Last * (1m + MinBandWidthRate / 100m)
                    || tContext.CurrentOrders.HighestAsk.Price
                        > tContext.Market.Ticker.Last * (1m + MaxBandWidthRate / 100m))
                {
                    // The band is not within defined bound: clear existing orders in order to define a new band
                    tContext.NewOrders.CancelExistingOrders(tContext.CurrentOrders.OrderedAsks.ToArray());
                }
                else if (tContext.NewOrders.PrimaryBalance * tContext.Market.Ticker.Last
                         < tContext.CurrentOrders.HighestAsk.Value * VolumeResetLimitFactor)
                {
                    //the amount of available resource is too low for the existing band: clear orders to define a new band
                    tContext.NewOrders.CancelExistingOrders(tContext.CurrentOrders.OrderedAsks.ToArray());
                }
                else
                {
                    //we start with new low orders: have we got new orders to issue ?
                    if (!AccountForTrend
                        || tContext.LastTrend != TradingTrend.Ask
                        || tContext.CurrentOrders.OrderedAsks.Count < 2)
                    {
                        decimal newPrice, limitPrice;
                        SimpleExpression<decimal> pricingExpression;
                        var sign = (int)TradingBandDirection;
                        if (TradingBandDirection == TradingBandDirection.Outwards)
                        {
                            pricingExpression = NextAskOrderPriceExpression;
                            newPrice = tContext.LowestAskLimitPrice;
                            limitPrice = tContext.LowestAsk.Price;
                        }
                        else
                        {
                            pricingExpression = MinAskOrderPriceExpression;
                            newPrice = pricingExpression.Evaluate(tContext);
                            limitPrice = tContext.LowestAskLimitPrice;
                        }

                        //How close are we to the lowest limit ask price?
                        safetyCounter = 0;
                        while (newPrice > 0 && sign * newPrice < sign * limitPrice && safetyCounter < 500)
                        {
                            safetyCounter += 1;
                            // We are within the authorized inner band , place new order

                            var newOrder = new Order { OrderType = OrderType.Sell, Price = newPrice };

                            //set price to context to compute the new order amount
                            tContext.Price = newPrice;
                            newOrder.Amount = AskOrderAmountExpression.Evaluate(tContext);
                            if (TradingBandDirection == TradingBandDirection.Inwards)
                            {
                                tContext.NewOrders.Orders.Add(newOrder);
                            }
                            newPrice = pricingExpression.Evaluate(tContext);
                            if (TradingBandDirection == TradingBandDirection.Outwards
                                    && sign * newPrice < sign * limitPrice)
                            {
                                tContext.NewOrders.Orders.Add(newOrder);
                            }
                        }
                    }

                    //then we check existing orders for cancelling or increasing
                    for (var i = 0; i <= tContext.CurrentOrders.OrderedAsks.Count - 1; i++)
                    {
                        var currentOrder = tContext.CurrentOrders.OrderedAsks[i];
                        if (currentOrder.Price > tContext.LowestAskLimitPrice)
                        {
                            tContext.Price = currentOrder.Price;
                            decimal idealAmount = AskOrderAmountExpression.Evaluate(tContext);
                            //Cleaning: if the order span exceeds the previous order span
                            //by more than the defined canceling rate, cancel the order
                            if ((i > 1
                                 && (tContext.CurrentOrders.OrderedAsks[i].Price - tContext.CurrentOrders.OrderedAsks[i - 1].Price)
                                 /
                                 (tContext.CurrentOrders.OrderedAsks[i - 1].Price - tContext.CurrentOrders.OrderedAsks[i - 2].Price)
                                 < this.CancelOrderLimitRate / 100m))
                            {
                                tContext.NewOrders.CancelExistingOrders(currentOrder);
                            }
                            else if (currentOrder.Amount < idealAmount * AdjustOrderLimitRate / 100m)
                            {
                                var newOrder = new Order
                                {
                                    OrderType = OrderType.Sell,
                                    Price = currentOrder.Price,
                                    Amount = idealAmount
                                };

                                //new order amount is the difference between ideal amount and current amount
                                tContext.NewOrders.CancelExistingOrders(currentOrder);
                                tContext.NewOrders.Orders.Add(newOrder);
                            }
                        }
                    }

                    if (tContext.NewOrders.Orders.Count == 0
                        && tContext.NewOrders.PrimaryBalance * tContext.Market.Ticker.Last
                            > tContext.CurrentOrders.HighestAsk.Value * VolumeGrowthLimitFactor)
                    {
                        //if their are still btcs available and their amount exceeds the strategy limit, increase the higher order
                        var newOrder = new Order
                        {
                            OrderType = OrderType.Sell,
                            Price = tContext.CurrentOrders.HighestAsk.Price,
                            Amount = tContext.CurrentOrders.HighestAsk.Amount * (1 + this.VolumeGrowthRate / 100m)
                        };
                        tContext.NewOrders.CancelExistingOrders(tContext.CurrentOrders.HighestAsk);
                        tContext.NewOrders.Orders.Add(newOrder);
                    }
                }
            }

            // Then we deal with Bids

            //todo: that should be symetrical thus abstracted as such

            if (!this.NoBids)
            {
                if (tContext.CurrentOrders.OrderedBids.Count == 0)
                {
                    if (this.AccountForTrend || tContext.LastTrend != TradingTrend.Bid)
                    {
                        // There is no bid order yet/anymore, define a single new bid order

                        //Compute price from current ticker and strategy
                        var newLowBidPrice = tContext.Market.Ticker.Last * 100m / (DefaultBandWidthRate + 100m);

                        var newOrder = new Order()
                        {
                            OrderType = OrderType.Buy,
                            Price = newLowBidPrice,
                            //compute amount from available balance and strategy
                            Amount = (tContext.NewOrders.SecondaryBalance / newLowBidPrice)
                            * DefaultMaxOrderValueRate / 100m
                        };
                        tContext.NewOrders.Orders.Add(newOrder);
                    }
                }
                // else: There are bid orders already, we'll base new orders according to the existing
                else if (tContext.CurrentOrders.LowestBid.Price
                        > tContext.Market.Ticker.Last * 100m / (MinBandWidthRate + 100m)
                    || tContext.CurrentOrders.LowestBid.Price
                        < tContext.Market.Ticker.Last * 100m / (MaxBandWidthRate + 100m))
                {
                    // The band is not within defined bound: clear existing orders in order to define a new band
                    tContext.NewOrders.CancelExistingOrders(tContext.CurrentOrders.OrderedBids.ToArray());
                }
                else if (tContext.NewOrders.SecondaryBalance
                         < tContext.CurrentOrders.LowestBid.Value * VolumeResetLimitFactor)
                {
                    //the amount of available resource is too low for the existing band: clear orders to define a new band
                    tContext.NewOrders.CancelExistingOrders(tContext.CurrentOrders.OrderedBids.ToArray());
                }
                else
                {
                    //we start with new low orders: have we got new orders to issue ?
                    if (!AccountForTrend
                        || tContext.LastTrend != TradingTrend.Bid
                        || tContext.CurrentOrders.OrderedBids.Count < 2)
                    {
                        decimal newPrice, limitPrice;
                        SimpleExpression<decimal> pricingExpression;
                        var sign = (int)TradingBandDirection;
                        if (TradingBandDirection == TradingBandDirection.Outwards)
                        {
                            pricingExpression = NextBidOrderPriceExpression;
                            newPrice = tContext.HighestBidLimitPrice;
                            limitPrice = tContext.HighestBid.Price;
                        }
                        else
                        {
                            pricingExpression = MaxBidOrderPriceExpression;
                            newPrice = pricingExpression.Evaluate(tContext);
                            limitPrice = tContext.HighestBidLimitPrice;
                        }

                        //How close are we to the lowest limit ask price?
                        safetyCounter = 0;
                        while (newPrice > 0 && sign * newPrice > sign * limitPrice && safetyCounter < 500)
                        {
                            safetyCounter += 1;
                            // We are within the authorized inner band , place new order

                            var newOrder = new Order { OrderType = OrderType.Buy, Price = newPrice };

                            //set price to context to compute the new order amount
                            tContext.Price = newPrice;
                            newOrder.Amount = BidOrderAmountExpression.Evaluate(tContext);
                            if (TradingBandDirection == TradingBandDirection.Inwards)
                            {
                                tContext.NewOrders.Orders.Add(newOrder);
                            }
                            newPrice = pricingExpression.Evaluate(tContext);
                            if (TradingBandDirection == TradingBandDirection.Outwards
                                    && sign * newPrice > sign * limitPrice)
                            {
                                tContext.NewOrders.Orders.Add(newOrder);
                            }
                        }
                    }

                    //then we check existing orders for cancelling or increasing
                    for (var i = 0; i <= tContext.CurrentOrders.OrderedBids.Count - 1; i++)
                    {
                        var currentOrder = tContext.CurrentOrders.OrderedBids[i];
                        if (currentOrder.Price < tContext.HighestBidLimitPrice)
                        {
                            tContext.Price = currentOrder.Price;
                            decimal idealAmount = BidOrderAmountExpression.Evaluate(tContext);
                            //Cleaning: if the order span exceeds the previous order span
                            //by more than the defined canceling rate, cancel the order
                            if ((i < tContext.CurrentOrders.OrderedBids.Count - 2
                                 && (tContext.CurrentOrders.OrderedBids[i + 1].Price - tContext.CurrentOrders.OrderedBids[i].Price)
                                 /
                                 (tContext.CurrentOrders.OrderedBids[i + 2].Price - tContext.CurrentOrders.OrderedBids[i + 1].Price)
                                 < this.CancelOrderLimitRate / 100m))
                            {
                                tContext.NewOrders.CancelExistingOrders(currentOrder);
                            }
                            else if (currentOrder.Amount < idealAmount * AdjustOrderLimitRate / 100m)
                            {
                                var newOrder = new Order
                                {
                                    OrderType = OrderType.Buy,
                                    Price = currentOrder.Price,
                                    Amount = idealAmount
                                };

                                //new order amount is the difference between ideal amount and current amount
                                tContext.NewOrders.CancelExistingOrders(currentOrder);
                                tContext.NewOrders.Orders.Add(newOrder);
                            }
                        }
                    }

                    if (tContext.NewOrders.Orders.Count == 0
                        && tContext.NewOrders.SecondaryBalance
                            > tContext.CurrentOrders.LowestBid.Value * VolumeGrowthLimitFactor)
                    {
                        //if their are still resources available and their amount exceeds the strategy limit, increase the highest order
                        var newOrder = new Order
                        {
                            OrderType = OrderType.Buy,
                            Price = tContext.CurrentOrders.LowestBid.Price,
                            Amount = tContext.CurrentOrders.LowestBid.Amount * (1 + this.VolumeGrowthRate / 100m)
                        };
                        tContext.NewOrders.CancelExistingOrders(tContext.CurrentOrders.LowestBid);
                        tContext.NewOrders.Orders.Add(newOrder);
                    }
                }
            }
        }
    }
}
