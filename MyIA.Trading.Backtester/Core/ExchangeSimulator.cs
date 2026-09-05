using System;
using System.Collections.Generic;
using System.Linq;

namespace MyIA.Trading.Backtester
{
    public class ExchangeSimulator
    {

        public List<OrderTrade> Trades { get; set; }

        public bool IncludeDepth { get; set; }
        public bool FullTicker { get; set; }

        private MarketInfo _currentMarket =  new MarketInfo();
        private int _currentTradeIdx = 0;
        private int _currentLast24HTradeIdx = 0;

        /// <summary>
        /// Emulates the Market data at a given time, given the historical trades
        /// In order to optimise performances, it keeps previous emulated market and only performs updates
        /// It implies that the method is called sequentially at increasing timings.
        /// Note that the marketDepth is only broadly approximated from future trades found in history
        /// </summary>
        /// <param name="time">the time at which the market should be emulated</param>
        /// <returns>a MarketInfo object with emulated ticker, RecentTrades, and Marketdepth</returns>
        public MarketInfo GetMarket(DateTime time)
        {
            _currentMarket.Time = time;

            // First we move the current trade cursor according to the new time and update the ticker and recent trades accordingly

            OrderTrade currentTrade = null;
            while (_currentTradeIdx < Trades.Count && Trades[_currentTradeIdx].Time <= time)
            {
                currentTrade = Trades[_currentTradeIdx];
                _currentMarket.RecentTrades.Add(currentTrade);

                if (FullTicker)
                {
                    _currentMarket.Ticker.Volume += currentTrade.Amount;
                    if (currentTrade.Price > _currentMarket.Ticker.High)
                        _currentMarket.Ticker.High = currentTrade.Price;
                    if (_currentMarket.Ticker.Low == 0m || currentTrade.Price < _currentMarket.Ticker.Low)
                        _currentMarket.Ticker.Low = currentTrade.Price;
                }

                _currentTradeIdx += 1;
            }

            if (currentTrade == null)
            {
                if (_currentTradeIdx == 0)
                    throw new InvalidOperationException("No trade is available at or before the requested time.");
                currentTrade = Trades[_currentTradeIdx - 1];
            }
            _currentMarket.Ticker.Last = currentTrade.Price;


            if (FullTicker)
            {
                // Then we move the previous 24h trades cursor and update the Ticker accordingly
                var last24hTime = time.AddHours(-24d);
                while (_currentLast24HTradeIdx < _currentTradeIdx
                       && Trades[_currentLast24HTradeIdx].Time < last24hTime)
                {
                    var last24HTrade = Trades[_currentLast24HTradeIdx];
                    _currentMarket.Ticker.Volume -= last24HTrade.Amount;
                    if (last24HTrade.Price == _currentMarket.Ticker.High)
                    {
                        _currentMarket.Ticker.High = 0m;
                    }
                    if (last24HTrade.Price == _currentMarket.Ticker.Low)
                    {
                        _currentMarket.Ticker.Low = 0m;
                    }
                    _currentLast24HTradeIdx += 1;
                }
                // if the ticker low or high were reset, recompute them

                if (_currentMarket.Ticker.Low == 0m || _currentMarket.Ticker.High == 0m)
                {
                    for (int i = _currentLast24HTradeIdx; i < _currentTradeIdx; i++)
                    {
                        var tempTrade = Trades[i];
                        if (_currentMarket.Ticker.Low == 0m || tempTrade.Price < _currentMarket.Ticker.Low)
                            _currentMarket.Ticker.Low = tempTrade.Price;
                        if (tempTrade.Price > _currentMarket.Ticker.High)
                            _currentMarket.Ticker.High = tempTrade.Price;

                    }
                }
            }

            // Finally, compute MarketDepth
            if (IncludeDepth)
            {
                //Identifying executed orders segments to be removed from existing MarketDepth
                var newMinAskIdx = 0;
                var existingMinAsk = decimal.MaxValue;
                var newMaxBidIdx = 0;
                var existingMaxBid = 0m;
                if (_currentMarket.MarketDepth.AskOrders.Count > 0)
                {
                    while (newMinAskIdx < _currentMarket.MarketDepth.AskOrders.Count - 1 && _currentMarket.MarketDepth.AskOrders[newMinAskIdx].Time < time)
                    {
                        newMinAskIdx++;
                    }
                    existingMinAsk = _currentMarket.MarketDepth.AskOrders[newMinAskIdx].Price;
                }

                if (_currentMarket.MarketDepth.BidOrders.Count > 0)
                {

                    while (newMaxBidIdx < _currentMarket.MarketDepth.BidOrders.Count - 1 && _currentMarket.MarketDepth.BidOrders[newMaxBidIdx].Time < time)
                    {
                        newMaxBidIdx++;
                    }
                    existingMaxBid = _currentMarket.MarketDepth.BidOrders[newMaxBidIdx].Price;
                }


                //Computing new depth segments
                var exitAskCondition = false;
                var exitBidCondition = false;
                var newDepth = new MarketDepth();
                for (int depthIdx = _currentTradeIdx; depthIdx < Trades.Count && !(exitAskCondition && exitBidCondition); depthIdx++)
                {
                    var depthTrade = Trades[depthIdx];
                    if (!exitAskCondition && (newDepth.AskOrders.Count > 0 &&
                                              depthTrade.Price > newDepth.AskOrders.Last().Price)
                        || (newDepth.AskOrders.Count == 0 && depthTrade.Price > currentTrade.Price))
                    {
                        if (depthTrade.Price < existingMinAsk)
                        {
                            newDepth.AskOrders.Add(depthTrade.ToOrder(OrderType.Sell));
                        }
                        else
                        {
                            exitAskCondition = true;
                        }

                    }
                    else if (!exitBidCondition && (newDepth.BidOrders.Count > 0 &&
                                                   depthTrade.Price < newDepth.BidOrders.Last().Price)
                             ||
                             (newDepth.BidOrders.Count == 0 && depthTrade.Price < currentTrade.Price))
                    {
                        if (depthTrade.Price > existingMaxBid)
                        {
                            newDepth.BidOrders.Add(depthTrade.ToOrder(OrderType.Buy));
                        }
                        else
                        {
                            exitBidCondition = true;
                        }
                    }
                }
                //joining former and new marketdepth segments
                newDepth.AskOrders.AddRange(_currentMarket.MarketDepth.AskOrders.Skip(newMinAskIdx));
                newDepth.BidOrders.AddRange(_currentMarket.MarketDepth.BidOrders.Skip(newMaxBidIdx));
                _currentMarket.MarketDepth = newDepth;
            }




            return _currentMarket;
        }




    }
}
