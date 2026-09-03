using System.Globalization;
using System;
using System.ComponentModel;
using System.Xml.Serialization;
using Newtonsoft.Json;

namespace MyIA.Trading.Backtester
{
	[DefaultProperty("FriendlyId")]
	[Serializable]
	public class Order : IComparable<Order>
	{

        public string FriendlyId
        {
            get
            {
                return string.Format("Order {0} : {1} {2} @ {3} = {4}"
                    , Oid
                    , OrderType.ToString()
                    , Amount.ToString(CultureInfo.InvariantCulture)
                    , Price.ToString(CultureInfo.InvariantCulture)
                    , Value.ToString(CultureInfo.InvariantCulture));
            }
        }

        public string Oid { get; set; }

        public int Status { get; set; }

        [Browsable(false)]
        public int Date { get; set; }

        [XmlIgnore()][JsonIgnore()]
        public DateTime Time
        {
            get
            {
                return UnixTime.ConvertFromUnixTimestamp(this.Date);
            }
            set
            {
                this.Date = Convert.ToInt32(UnixTime.ConvertToUnixTimestamp(value));
            }
        }

        [XmlIgnore()][JsonIgnore()]
        public OrderType OrderType
        {
            get
            {
                if (!this.IsCancel)
                {
                    return  (OrderType)this.Type;
                }
                else
                {
                    return OrderType.Cancel;
                }
            }
            set
            {
                if (value != OrderType.Cancel)
                {
                    this.Type = (int)value;
                    // Si l'ordre etait precedemment annule, repasser a un type actif leve
                    // l'etat d'annulation : sans ce reset, OrderType retournerait Cancel via
                    // le getter tant que IsCancel reste true, ce qui contredit le Type stocke.
                    this.IsCancel = false;
                }
                else
                {
                    this.IsCancel = true;
                }
            }
        }

        public bool IsCancel { get; set; }

        [Browsable(false)]
        public int Type { get; set; }

        public decimal Price { get; set; }

	    public decimal Amount { get; set; }

        public decimal Value
        {
            get
            {
                return decimal.Multiply(this.Price, this.Amount);
            }
        }

	    public bool Dark { get; set; }


		public Order()
		{
		    OrderType = OrderType.Buy;
		}

		public Order(OrderType orderType, decimal price, decimal amount)
		{
			this.OrderType = orderType;
			this.Price = price;
			this.Amount = amount;
		}

        public Order(OrderType orderType, decimal price, decimal amount, DateTime date)
        {
            this.OrderType = orderType;
            this.Price = price;
            this.Amount = amount;
            this.Date = Convert.ToInt32( UnixTime.ConvertToUnixTimestamp(date));
        }

		int IComparable<Order>.CompareTo(Order other)
		{
            return Convert.ToInt32(Math.Sign(Price - other.Price));
		}

        int CompareDates(Order other)
        {
            return CompareOrderDates(this, other);
        }

	    static int CompareOrderDates(Order order1, Order order2)
	    {
            return Convert.ToInt32(Math.Sign(order1.Date - order2.Date));
	    }

	}
}
