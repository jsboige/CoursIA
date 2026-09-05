using System.Globalization;
using System.Linq;
using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Xml.Serialization;
using Newtonsoft.Json;

namespace MyIA.Trading.Backtester
{
    [DefaultProperty("DisplayName")]
    [Serializable]
    public class Wallet : ResponseObject, ICloneable
    {
        private List<Order> _orders;

        private List<Order> _orderedAsks;
        private List<Order> _orderedBids;

        [Browsable(false)]
        [XmlIgnore()][JsonIgnore()]
        public virtual string DisplayName
        {
            get
            {
                return string.Format("{0} {1} - {2} {3}, {4} {5} - {6} Asks, {7} Bids, {8} Cancels",
                    Time.ToShortDateString(), Time.ToShortTimeString(), PrimaryBalance, PrimarySymbol,
                    SecondaryBalance.ToString(CultureInfo.InvariantCulture), SecondarySymbol.ToString(CultureInfo.InvariantCulture),
                    OrderedAsks.Count.ToString(CultureInfo.InvariantCulture), OrderedBids.Count.ToString(CultureInfo.InvariantCulture),
                    CancelOrders.Count.ToString(CultureInfo.InvariantCulture));
            }
        }

        public string Status { get; set; }

        public DateTime Time { get; set; }

        public string MarketId { get; set; }

        public string PrimarySymbol { get; set; } = "";

        public string SecondarySymbol { get; set; } = "";

        public decimal PrimaryBalance { get; set; }

        public decimal SecondaryBalance { get; set; }

        [Browsable(false)]
        public virtual List<Order> Orders
        {
            get
            {
                Clean();
                return _orders;
            }
            set
            {
                _orders = value;
                Clean();
            }
        }



        [XmlIgnore()][JsonIgnore()]
        public List<Order> OrderedAsks
        {
            get
            {
                if (_orderedAsks == null)
                {
                    _orderedAsks = GetSortedOrders(1);
                }
                return _orderedAsks;
            }
        }

        [XmlIgnore()][JsonIgnore()]
        public List<Order> OrderedBids
        {
            get
            {
                if (_orderedBids == null)
                {
                    _orderedBids = GetSortedOrders(2);
                }
                return _orderedBids;
            }
        }

        [XmlIgnore()][JsonIgnore()]
        public List<Order> CancelOrders
        {
            get
            {
                return _orders.Where(objOrder => objOrder.OrderType == OrderType.Cancel || objOrder.IsCancel).ToList();
            }
        }

        [XmlIgnore()][JsonIgnore()]
        public Order HighestAsk
        {
            get
            {
                var asks = OrderedAsks;
                if (asks.Count > 0)
                {
                    return asks[(asks.Count - 1)];
                }
                return null;
            }
        }

        [XmlIgnore()][JsonIgnore()]
        public Order HighestBid
        {
            get
            {
                var bids = OrderedBids;
                if (bids.Count > 0)
                {
                     return bids[bids.Count - 1];
                }
                return null;
            }
        }

        [XmlIgnore()][JsonIgnore()]
        public Order LowestAsk
        {
            get
            {
                var asks = this.OrderedAsks;
                if (asks.Count == 0)
                {
                    return null;
                }
                else
                {
                    return asks[0];
                }
            }
        }

        [XmlIgnore()][JsonIgnore()]
        public Order LowestBid
        {
            get
            {
                var bids = OrderedBids;
                if (bids.Count == 0)
                {
                    return null;
                }
                else
                {
                    return bids[0];
                }
            }
        }

        public virtual List<OrderTrade> LastTrades { get; set; }

        public virtual List<Transaction> LastTransactions { get; set; }

        #region cTors

        public Wallet()
        {
            this.Status = "Default";
            this.Time = DateTime.Now;
            this._orders = new List<Order>();
            this.LastTrades = new List<OrderTrade>();
            this.LastTransactions = new List<Transaction>();

        }

        public Wallet(ResponseObject objresponseObject)
            : base(objresponseObject)
        {
            this.Status = "Default";
            this.Time = DateTime.Now;
            this.Orders = new List<Order>();
            this.LastTrades = new List<OrderTrade>();
            this.LastTransactions = new List<Transaction>();
        }

        //public Wallet(Balance objBalance, Wallet balanceLessWallet)
        //    : this(balanceLessWallet)
        //{
        //    this.SecondaryBalance = objBalance.usds;
        //    this.PrimaryBalance = objBalance.btcs;
        //    this.Orders = balanceLessWallet.Orders;
        //}

        #endregion



        public void CancelExistingOrders(params Order[] objOrders)
        {
            foreach (var objOrder in objOrders)
            {
                if (!objOrder.IsCancel)
                {
                    string cancelOrderId = objOrder.Oid;
                    if (string.IsNullOrEmpty(cancelOrderId))
                    {
                        this.Orders.Remove(objOrder);
                    }
                    else if (!this.CancelOrders.Exists(varOrder => varOrder.Oid == cancelOrderId))
                    {
                        var toReturn = new Order()
                        {
                            IsCancel = true,
                            Type = objOrder.Type,
                            Oid = objOrder.Oid,
                            Price = objOrder.Price,
                            Amount = objOrder.Amount
                        };
                        this.Orders.Add(toReturn);
                        //todo: not sure where that came from, need to check balance vs avail balance handling
                        switch (objOrder.OrderType)
                        {
                            case OrderType.Sell:
                                this.PrimaryBalance += objOrder.Amount;
                                break;
                            case OrderType.Buy:
                                this.SecondaryBalance += objOrder.Price * objOrder.Amount;
                                break;
                        }
                    }
                }
            }
        }

        /// <summary>
        /// Remove all ask orders
        /// </summary>
        public void ClearAsks()
        {
            foreach (var order in OrderedAsks)
            {
                this.Orders.Remove(order);
            }
        }

        /// <summary>
        ///  Removes all bid orders
        /// </summary>
        public void ClearBids()
        {
            foreach (var order in OrderedBids)
            {
                this.Orders.Remove(order);
            }
        }

        /// <summary>
        ///  Performs a deep copy of the current wallet
        /// </summary>
        /// <returns>the clone wallet</returns>
        public object Clone()
        {
            var toReturn = new Wallet
            {
                Time = this.Time,
                PrimarySymbol = this.PrimarySymbol,
                SecondarySymbol = this.SecondarySymbol,
                PrimaryBalance = this.PrimaryBalance,
                SecondaryBalance = this.SecondaryBalance,
                Status = this.Status,
                Orders = new List<Order>(this._orders),
                LastTrades = new List<OrderTrade>(this.LastTrades),
                LastTransactions = new List<Transaction>(this.LastTransactions),
                ReturnCodes = this.ReturnCodes,
                Error = this.Error
            };
            return toReturn;
        }

        /// <summary>
        /// Consolidates the current wallet
        /// </summary>
        public void ConsolidateOrders()
        {
            Wallet objWallet = this;
            this.ConsolidateOrders(ref objWallet, true);
        }

        /// <summary>
        /// Merges orders of the same price from an given wallet, while creating the cancel and new orders in the current wallet
        /// </summary>
        /// <param name="originalWallet">the wallet to merge the same priced orders from</param>
        /// <param name="updateOriginalWallet">defines if only the current wallet is updated with new orders, or also the original wallet</param>
        public void ConsolidateOrders(ref Wallet originalWallet, bool updateOriginalWallet)
        {

            var priceWallets = new Dictionary<decimal, Wallet>();
            foreach (var objOrder in _orders)
            {
                if (!objOrder.IsCancel)
                {
                    Wallet tempPriceWallet;
                    if (!priceWallets.TryGetValue(objOrder.Price, out tempPriceWallet))
                    {
                        tempPriceWallet = new Wallet();
                        priceWallets[objOrder.Price] = tempPriceWallet;
                    }
                    tempPriceWallet.Orders.Add(objOrder);
                }
            }
            foreach (var priceWallet in priceWallets.Values)
            {
                if (priceWallet._orders.Count > 1)
                {
                    var mergedOrder = new Order()
                    {
                        Type = priceWallet._orders[0].Type,
                        Price = priceWallet._orders[0].Price
                    };
                    foreach (var subOrder in priceWallet._orders)
                    {
                        mergedOrder.Amount = decimal.Add(mergedOrder.Amount, subOrder.Amount);
                        if (updateOriginalWallet)
                        {
                            originalWallet.Orders.Remove(subOrder);
                        }

                    }
                   // The current wallet serves collecting the consolidation orders to be issued (2 cancels + 1 new)
                    this.CancelExistingOrders(priceWallet._orders.ToArray());
                    this.Orders.Add(mergedOrder);
                    // the new order replaces the consolidated orders in the original wallet too
                    if (originalWallet != this & updateOriginalWallet)
                    {
                        originalWallet.Orders.Add(mergedOrder);
                    }
                }
            }

        }

        /// <summary>
        /// Shortcut function for selecting an order by id
        /// </summary>
        /// <param name="orderId"></param>
        /// <returns></returns>
        public Order FindOrderById(string orderId)
        {
            return _orders.Find(o => o.Oid == orderId);
        }



        /// <summary>
        ///  Updates the orders according to the available balance (overflow orders are removed), and to the exchange min order settings.
        /// </summary>
        /// <param name="exchange">the exchange defining minimum order settings</param>
        public void FitOrders(ExchangeInfo exchange)
        {

            this.ConsolidateOrders();


            //first we fit orders according to the available resources
            decimal totalBids = this.GetTotalBidsSecondary();
            if (totalBids > 0)
            {
                var coefBids = Math.Max(this.SecondaryBalance, 0) / totalBids;
                if (coefBids < 1)
                {
                    decimal cumulativeBids = 0;
                    foreach (var bid in this.OrderedBids)
                    {
                        //bid.amount = Decimal.Round(bid.amount * coefBids, exchange.AmountDecil, MidpointRounding.ToEven)
                        cumulativeBids += bid.Value;
                        if (cumulativeBids > this.SecondaryBalance)
                        {
                            this.Orders.Remove(bid);
                        }
                    }
                }
            }
            var totalAsks = this.GetTotalAsksPrimary();
            if (totalAsks > 0)
            {
                var coefAsks = Math.Max(this.PrimaryBalance, 0) / totalAsks;
                if (coefAsks < 1)
                {
                    decimal cumulativeAsks = 0;
                   var decreasingAsks = this.OrderedAsks;
                    decreasingAsks.Reverse();
                    foreach (var ask in decreasingAsks)
                    {
                        //ask.amount = Decimal.Round(ask.amount * coefAsks, exchange.AmountDecil, MidpointRounding.ToEven)
                        cumulativeAsks += ask.Amount;
                        if (cumulativeAsks > this.PrimaryBalance)
                        {
                            _orders.Remove(ask);
                        }
                    }
                }
            }


            var cleanOrders = new List<Order>();
            foreach (var objOrder in _orders)
            {
                if (objOrder.IsCancel)
                {
                    cleanOrders.Add(objOrder);
                }
                else
                {
                    if (objOrder.Amount >= Math.Max(exchange.MinOrderAmount, exchange.MinOrderValue / objOrder.Price))
                    {
                        objOrder.Price = decimal.Round(objOrder.Price, exchange.PriceDecil);
                        objOrder.Amount = decimal.Round(objOrder.Amount, exchange.AmountDecil);
                        cleanOrders.Add(objOrder);
                    }

                }
            }
            Orders = cleanOrders;
        }

        public Balance GetBalance(decimal price)
        {
            return new Balance(this.PrimaryBalance, new Ticker(price), this.SecondaryBalance);
        }

        public Balance GetBalance(Ticker objTicker)
        {
            return new Balance(this.PrimaryBalance, objTicker, this.SecondaryBalance);
        }

        public decimal GetTotalAsksPrimary()
        {
            return _orders.Where(objOrder => (objOrder.Type == 1 && !objOrder.IsCancel))
                .Aggregate(0m, (current, objOrder) => decimal.Add(current, objOrder.Amount));
        }

        public decimal GetTotalBidsSecondary()
        {
            return _orders.Where(objOrder => (objOrder.Type == 2 && !objOrder.IsCancel))
                .Aggregate(0m, (current, objOrder) => decimal.Add(current, objOrder.Value));
        }


        /// <summary>
        /// Updates a wallet with a list of orders, as expected from the exchange (used for simulation)
        /// </summary>
        /// <param name="newOrders"></param>
        public void IntegrateOrders(Order[] newOrders)
        {
            Order[] orderArray = newOrders;
            foreach (var newOrder in newOrders)
            {
                if (!newOrder.IsCancel)
                {
                    newOrder.Oid = Guid.NewGuid().ToString();
                    this.Orders.Add(newOrder);
                }
                else
                {
                    Order targetOrder = this.FindOrderById(newOrder.Oid);
                    if (targetOrder != null)
                    {
                        this.Orders.Remove(targetOrder);
                    }
                }
            }
        }



        #region Private methods

        private List<Order> GetSortedOrders(int objOrderType)
        {
            var objSortedList = new SortedList<decimal, Order>(this._orders.Count);
            for (int i = 0; i < _orders.Count; i++)
            {
                Order objOrder = _orders[i];
                if ((objOrder.Type == objOrderType && !objOrder.IsCancel))
                {
                    if (objSortedList.ContainsKey(objOrder.Price))
                    {
                        Order item = objSortedList[objOrder.Price];
                        item.Amount = decimal.Add(item.Amount, objOrder.Amount);
                    }
                    else
                    {
                        objSortedList.Add(objOrder.Price, objOrder);
                    }
                }
            }
            return new List<Order>(objSortedList.Values);
        }

        private void Clean()
        {
            _orderedAsks = null;
            _orderedBids = null;
        }

        #endregion

    }
}
