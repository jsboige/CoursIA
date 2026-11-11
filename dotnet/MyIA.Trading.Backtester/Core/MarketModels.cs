using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Diagnostics;
using System.Globalization;
using System.Linq;
using System.Xml.Serialization;
using Newtonsoft.Json;

namespace MyIA.Trading.Backtester
{
	[Serializable]
	public class ResponseObject
	{
		public string Error;

		public string ReturnCodes;

		public ResponseObject()
		{
			this.Error = "";
			this.ReturnCodes = "";
		}

		public ResponseObject(ResponseObject objResponseObject)
		{
			this.Error = objResponseObject.Error;
			this.ReturnCodes = objResponseObject.ReturnCodes;
		}
	}

    [Serializable]
	public class Ticker : ResponseObject, ICloneable
	{
	    public decimal Buy { get; set; }

	    public decimal High { get; set; }

	    public decimal Last { get; set; }

	    public decimal Low { get; set; }

	    public decimal Sell { get; set; }

	    public decimal Volume { get; set; }

	    public Ticker()
		{
		}

        public Ticker(decimal price): this(price, 0m)
		{
		}

        public Ticker(decimal price, decimal volume)
        {
            this.Last = price;
            this.Sell = price;
            this.Buy = price;
            this.Low = price;
            this.High = price;
            this.Volume = volume;
        }

	    public Ticker(Ticker cloneTicker)
	    {
	        if (cloneTicker != null)
	        {
                this.Last = cloneTicker.Last;
                this.Sell = cloneTicker.Sell;
                this.Buy = cloneTicker.Buy;
                this.Low = cloneTicker.Low;
                this.High = cloneTicker.High;
                this.Volume = cloneTicker.Volume;
	        }
	    }


	    public object Clone()
	    {
	        return new Ticker(this);
	    }
	}

	[Serializable]
	public class Balance : ResponseObject
	{
	    public decimal Primary { get; set; }

        public decimal Secondary { get; set; }

        [Browsable(false)]
        public Ticker Ticker { get; set; }

	    [XmlIgnore()][JsonIgnore()]
		public decimal Value
		{
			get
			{
			    if (Ticker == null)
			    {
                    throw new InvalidOperationException("Balance Value cannot be computed without Ticker");
			    }
				return this.Primary * this.Ticker.Last;
			}
		}



	    [XmlIgnore()][JsonIgnore()]
		public decimal TickerLast
		{
			get
			{
				return this.Ticker.Last;
			}
		}

		[XmlIgnore()][JsonIgnore()]
		public decimal Total
		{
			get
			{
				return this.GetTotal();
			}
		}



		public Balance()
		{
		}

		public Balance(ResponseObject objresponseObject) : base(objresponseObject)
		{
		}

        public Balance(decimal objPrimary,  decimal objSecondary)
        {

            this.Primary = objPrimary;
            this.Secondary = objSecondary;
        }

		public Balance(decimal objPrimary, Ticker objTicker, decimal objSecondary): this(objPrimary, objSecondary)
		{
			this.Ticker = objTicker;
		}

		public decimal GetTotal()
		{
			return  Secondary + Value;
		}
	}




//[Serializable]
//public class Balance : ResponseObject
//{
//    private Ticker _Ticker;

//    public decimal usds;

//    public decimal btcs;

//    public decimal BTC
//    {
//        get
//        {
//            return this.btcs;
//        }
//        set
//        {
//            this.btcs = value;
//        }
//    }

//    [XmlIgnore()][JsonIgnore()]
//    public decimal Value
//    {
//        get
//        {
//            decimal Value = decimal.Round(decimal.Multiply(this.btcs, this.Ticker.Last), 5);
//            return Value;
//        }
//    }

//    [Browsable(false)]
//    public MyIA.Trading.Backtester.Ticker Ticker
//    {
//        get
//        {
//            return this._Ticker;
//        }
//        set
//        {
//            this._Ticker = value;
//        }
//    }

//    [XmlIgnore()][JsonIgnore()]
//    public decimal TickerLast
//    {
//        get
//        {
//            return this._Ticker.Last;
//        }
//    }

//    [XmlIgnore()][JsonIgnore()]
//    public decimal Total
//    {
//        get
//        {
//            return this.GetTotal();
//        }
//    }

//    public decimal USD
//    {
//        get
//        {
//            return this.usds;
//        }
//        set
//        {
//            this.usds = value;
//        }
//    }

//    public Balance()
//    {
//    }

//    public Balance(ResponseObject objresponseObject)
//        : base(objresponseObject)
//    {
//    }

//    public Balance(decimal objUsds, decimal objBtcs, MyIA.Trading.Backtester.Ticker objTicker)
//    {
//        this.usds = objUsds;
//        this.btcs = objBtcs;
//        this._Ticker = objTicker;
//    }

//    public decimal GetTotal()
//    {
//        if (this.Ticker == null)
//        {
//            throw new InvalidOperationException("Ticker less balance can't compute total");
//        }
//        decimal GetTotal = decimal.Round(decimal.Add(this.usds, decimal.Multiply(this.btcs, this.Ticker.Last)), 5);
//        return GetTotal;
//    }
//

    [Serializable]
	public class MarketDepth : ResponseObject, ICloneable
	{

        public MarketDepth()
        {
            Init();
        }

        public MarketDepth(ResponseObject objresponseObject)
            : base(objresponseObject)
        {
            Init();
        }

        public MarketDepth(MarketDepth cloneDepth) : this(cloneDepth, false)
        {

        }

        public MarketDepth(MarketDepth cloneDepth, bool deepCopy)
        {
            if (cloneDepth != null)
            {
                if (deepCopy)
                {
                    BidOrders = new List<Order>(cloneDepth.BidOrders);
                    AskOrders = new List<Order>(cloneDepth.AskOrders);
                }
                else
                {
                    BidOrders = cloneDepth.BidOrders;
                    AskOrders = cloneDepth.AskOrders;
                }
            }
            else
            {
                Init();
            }
        }

        private void Init()
        {
            BidOrders = new List<Order>();
            AskOrders = new List<Order>();
        }

        public List<Order> AskOrders { get; set; }

        public List<Order> BidOrders { get; set; }

        [XmlIgnore()]
	    public decimal[][] Asks
	    {
	        get
	        {
	            return AskOrders.Select(objOrder => new decimal[3] {objOrder.Price, objOrder.Amount, objOrder.Date}).ToArray();
	        }
	        set
	        {
	            foreach (var triplet in value)
	            {
                    if (triplet.Length <= 2 || triplet[2]<=0)
	                {
                        AskOrders.Add(new Order(OrderType.Sell, triplet[0], triplet[1]));
	                }
                    else
                    {
                        AskOrders.Add(new Order(OrderType.Sell, triplet[0], triplet[1],
                            UnixTime.ConvertFromUnixTimestamp(Convert.ToInt64( triplet[2]))));
                    }

	            }

	        }
	    }

        [XmlIgnore()]
	    public decimal[][] Bids
	    {
            get
            {
                return BidOrders.Select(objOrder => new decimal[3] { objOrder.Price, objOrder.Amount, objOrder.Date }).ToArray();
            }
            set
            {
                foreach (var triplet in value)
                {
                    if (triplet.Length <= 2 || triplet[2] <= 0)
                    {
                        BidOrders.Add(new Order(OrderType.Buy, triplet[0], triplet[1]));
                    }
                    else
                    {
                        BidOrders.Add(new Order(OrderType.Buy, triplet[0], triplet[1],
                            UnixTime.ConvertFromUnixTimestamp(Convert.ToInt64(triplet[2]))));
                    }

                }

            }
	    }

        public object Clone()
        {
            return new MarketDepth(this, true);
        }
	}

	[Serializable]
	public class MarketInfo:ICloneable
	{

	    public string Id { get; set; }

        public string Label { get; set; }

        public string PrimaryName { get; set; }
        public string PrimaryCode { get; set; }
        public string SecondaryName { get; set; }
        public string SecondaryCode { get; set; }

        public DateTime Time { get; set; }

        public Ticker Ticker { get; set; }

	    public List<OrderTrade> RecentTrades { get; set; }

	    public MarketDepth MarketDepth { get; set; }



	    public MarketInfo() : this(DateTime.Now, null, null, null, false)
	    {
	    }


        public MarketInfo(DateTime objTime)
            : this(objTime, null, null, null, false)
	    {
	    }


        public MarketInfo(Ticker ticker, MarketDepth depth)
            : this(DateTime.Now, ticker, depth, null, false)
		{
		}


	    public MarketInfo(DateTime objTime, Ticker ticker, MarketDepth depth, List<OrderTrade> trades)
	        : this(objTime, ticker, depth, trades, false)
	    {

	    }

        public MarketInfo(DateTime objTime, Ticker ticker, MarketDepth depth, List<OrderTrade> trades, bool deepCopy)
		{
            Id = "";
            Label = "";
            PrimaryName = "";
            PrimaryCode = "";
            SecondaryCode = "";
            SecondaryName = "";

		    Time = objTime;

            if (ticker != null)
            {
                if (deepCopy)
                {
                    Ticker = new Ticker(ticker);
                }
                else
                {
                    Ticker = ticker;
                }
            }
            else
            {
                Ticker = new Ticker();
            }


            MarketDepth = new MarketDepth(depth, deepCopy);

            if (trades != null)
            {
                if (deepCopy)
                {
                    RecentTrades = new List<OrderTrade>(trades);
                }
                else
                {
                    RecentTrades = trades;
                }
            }
            else
            {
                RecentTrades = new List<OrderTrade>();
            }
		}

        public MarketInfo(MarketInfo sourceMarket): this(sourceMarket, false)
        {

        }

        public MarketInfo(MarketInfo sourceMarket, bool deepCopy)
            : this(sourceMarket, null, deepCopy)
	    {

	    }

        public MarketInfo(MarketInfo sourceMarket, MarketInfo additionalData)
            : this(sourceMarket, additionalData, false)
        {

        }


        public MarketInfo(MarketInfo sourceMarket, MarketInfo additionalData, bool deepCopy)
            : this(sourceMarket.Time, sourceMarket.Ticker, sourceMarket.MarketDepth, sourceMarket.RecentTrades, deepCopy)
        {
            Id = sourceMarket.Id;
            Label = sourceMarket.Label;
            PrimaryName = sourceMarket.PrimaryName;
            PrimaryCode = sourceMarket.PrimaryCode;
            SecondaryCode = sourceMarket.SecondaryCode;
            SecondaryName = sourceMarket.SecondaryName;

            if (additionalData!= null)
            {
                RecentTrades.AddRange(additionalData.RecentTrades);
                MarketDepth.AskOrders.AddRange(additionalData.MarketDepth.AskOrders);
                MarketDepth.BidOrders.AddRange(additionalData.MarketDepth.BidOrders);
            }
        }


	    public object Clone()
	    {
	        return new MarketInfo(this, true);
	    }
	}

	public class AsksAndBids : ResponseObject
	{
		public Order[] Asks;

		public Order[] Bids;

		public AsksAndBids()
		{
		}

		public AsksAndBids(ResponseObject objresponseObject) : base(objresponseObject)
		{
		}

		public MarketDepth ToMarketDepth()
		{
			var toReturn = new MarketDepth(this);
		    toReturn.AskOrders.AddRange(this.Asks);
		    toReturn.BidOrders.AddRange(this.Bids);
			return toReturn;
		}

		public Wallet ToWallet()
		{
			var toReturn = new Wallet(this);
			toReturn.Orders.AddRange(this.Asks);
            toReturn.Orders.AddRange(this.Bids);
			return toReturn;
		}
	}
}
