using System.Collections;
using System.Collections.Generic;
using System.Xml.Serialization;
using FileHelpers;
using System;
using System.ComponentModel;
using System.Globalization;
using Newtonsoft.Json;

namespace MyIA.Trading.Backtester
{

    //public class TradeList:SerializableList<Trade>
    //{

    //    public TradeList()
    //        : base()
    //    {

    //    }

    //    public  TradeList(int capacity): base(capacity)
    //    {
            
    //    }

    //    public TradeList(IEnumerable collection)
    //        : base(collection)
    //    {

    //    }

    //    public TradeList(IEnumerable<Trade> collection)
    //        : base(collection)
    //    {

    //    }


    //    public void SortByDate(ListSortDirection direction)
    //    {
    //        this.Sort(new SimpleComparer<Trade>("Time", direction));
    //    }


    //}


	[DefaultProperty("FriendlyId")]
	[DelimitedRecord(",")]
	public class OrderTrade: IEquatable<OrderTrade>
	{

        public OrderTrade()
        {
            this.TradeType = TradeType.Buy;
            this.InitialOrderType = TradeType.Buy;
            this.Time = DateTime.MinValue;
        }

        public string Id { get; set; }

        public DateTime Time { get; set; }

	    [JsonIgnore()]
        [XmlIgnore()]
        public long UnixTime
        {
            get
            {
                return MyIA.Trading.Backtester.UnixTime.ConvertToUnixTimestamp(Time);
            }
            set
            {
                Time = MyIA.Trading.Backtester.UnixTime.ConvertFromUnixTimestamp(value);
            }
        }

	    public decimal Amount;

	    [JsonIgnore()]
        [Browsable(false)]
		public string FriendlyId
		{
			get
			{
				string orderType = "Buy";
				if (decimal.Compare(this.Amount, decimal.Zero) < 0 | TradeType == TradeType.Sell)
				{
					orderType = "Sell";
				}
				string str = string.Concat("Trade:  {0} : ", orderType, " {1} BTCs".PadRight(18), " @ $ {2}".PadRight(18));
				string shortDateString = this.Time.ToShortDateString();
                return string.Format(str
                        , string.Concat(Time.ToShortDateString(), " ", Time.ToShortTimeString())
                        , Amount.ToString(CultureInfo.InvariantCulture)
                        , Price.ToString(CultureInfo.InvariantCulture));
			}
		}

        public decimal Price { get; set; }

	    public decimal Fee { get; set; }

        public TradeType TradeType { get; set; }

        public TradeType InitialOrderType { get; set; }

        public string OrderId { get; set; }


	    public Order ToOrder(OrderType orderType)
	    {
	        return new Order
	        {
	            Oid = Id,
	            Time = Time,
	            Amount = Amount,
	            Price = Price,
	            OrderType = orderType
	        };
	    }


	    public bool Equals(OrderTrade other)
	    {
	        return this.Time == other.Time && this.Price == other.Price && this.Amount == other.Amount;
	    }

        public override bool Equals(object obj)
        {
            return this.Equals((OrderTrade) obj);
        }

        public override int GetHashCode()
        {
            return Convert.ToInt32( this.UnixTime) ^ Price.GetHashCode() ^ Amount.GetHashCode();
        }


	}
}
