using System;

namespace MyIA.Trading.Backtester
{
    public class TradingContext
    {
        public decimal AskSpan
        {
            get
            {
                return this.CurrentOrders.HighestAsk.Price - this.LowestAskLimitPrice;
            }
        }

        public ITradingStrategy BaseStrategy { get; set; }

        public decimal BidSpan
        {
            get
            {
                return this.HighestBidLimitPrice - this.CurrentOrders.LowestBid.Price;
            }
        }

        public Wallet CurrentOrders { get; set; }

        public ExchangeInfo Exchange { get; set; }

        public TradingTrend LastTrend { get; private set; }

        public Order HighestBid
        {
            get
            {
                Order toReturn = CurrentOrders.HighestBid;
                if (toReturn == null)
                {
                    toReturn = this.NewOrders.HighestBid;
                }
                else if (this.NewOrders.HighestBid != null && this.NewOrders.HighestBid.Price > toReturn.Price)
                {
                    toReturn = this.NewOrders.HighestBid;
                }
                return toReturn;
            }
        }



        public decimal HighestBidLimitPrice
        {
            get
            {
                var bidMargingFactor = GetBidMarginFactor();
                var objBaseStrategy = this.BaseStrategy as TradingStrategyBase;
                if (objBaseStrategy != null && objBaseStrategy.TakeMarginOnOppositeOrder)
                {

                    var objLowestAsk = LowestAsk;
                    if (objLowestAsk != null)
                    {
                        return Math.Min(Market.Ticker.Last * bidMargingFactor,
                            bidMargingFactor * objLowestAsk.Price / this.GetAskMarginFactor());
                    }
                }
                return Market.Ticker.Last * bidMargingFactor;
            }
        }



        public Order LowestAsk
        {
            get
            {
                Order toReturn = this.CurrentOrders.LowestAsk;
                if (toReturn == null)
                {
                    toReturn = this.NewOrders.LowestAsk;
                }
                else if (this.NewOrders.LowestAsk != null && this.NewOrders.LowestAsk.Price < toReturn.Price)
                {
                    toReturn = this.NewOrders.LowestAsk;
                }
                return toReturn;
            }
        }

        public decimal LowestAskLimitPrice
        {
            get
            {
                var askMargingFactor = GetAskMarginFactor();
                var objBaseStrategy = this.BaseStrategy as TradingStrategyBase;
                if (objBaseStrategy != null && objBaseStrategy.TakeMarginOnOppositeOrder)
                {

                    var objHighestBid = HighestBid;
                    if (objHighestBid != null)
                    {
                        return Math.Max(Market.Ticker.Last * askMargingFactor,
                            askMargingFactor * objHighestBid.Price / this.GetBidMarginFactor());
                    }
                }
                return Market.Ticker.Last * askMargingFactor;
            }
        }

        public MarketInfo Market { get; set; }

        public Wallet NewOrders { get; set; }

        public decimal Price { get; set; }

        public TradingContext()
        {
            this.Exchange = new ExchangeInfo();
            this.Market = new MarketInfo();
            this.CurrentOrders = new Wallet();
            this.NewOrders = new Wallet();
        }

        public TradingContext(Wallet currentOrders, Wallet newOrders, MarketInfo objMarket, ExchangeInfo objExchange, TradingTrend lastTrend, ITradingStrategy objStrategy)
        {
            this.Exchange = new ExchangeInfo();
            this.Market = new MarketInfo();
            this.CurrentOrders = new Wallet();
            this.NewOrders = new Wallet();
            this.CurrentOrders = currentOrders;
            this.NewOrders = newOrders;
            this.Market = objMarket;
            this.Exchange = objExchange;
            this.LastTrend = lastTrend;
            this.BaseStrategy = objStrategy;
        }

        private decimal GetAskMarginFactor()
        {
            var objBaseStrategy = this.BaseStrategy as TradingStrategyBase;
            if (objBaseStrategy != null)
            {
                return (1 + (Exchange.AskCommission / 100m) + (objBaseStrategy.LimitOrderMarginRate / 100m));
            }
            return 1 + (Exchange.AskCommission / 100m);

        }

        private decimal GetBidMarginFactor()
        {
            var objBaseStrategy = this.BaseStrategy as TradingStrategyBase;
            if (objBaseStrategy != null)
            {
                return (1 - (Exchange.BidCommission / 100m) - (objBaseStrategy.LimitOrderMarginRate / 100m));
            }
            return 1 - (Exchange.BidCommission / 100m);
        }

    }
}