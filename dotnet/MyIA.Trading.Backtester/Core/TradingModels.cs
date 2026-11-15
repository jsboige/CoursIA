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
	[DefaultProperty("Label")]
	[Serializable]
	public class Payment
	{
		public decimal Amount
		{
			[DebuggerNonUserCode]
			get;
			[DebuggerNonUserCode]
			set;
		}

		public string Currency
		{
			[DebuggerNonUserCode]
			get;
			[DebuggerNonUserCode]
			set;
		}

		public string Label
		{
			[DebuggerNonUserCode]
			get;
			[DebuggerNonUserCode]
			set;
		}

		public DateTime Time
		{
			[DebuggerNonUserCode]
			get;
			[DebuggerNonUserCode]
			set;
		}

		public Payment()
		{
			this.Currency = "BTC";
		}
	}

	[DefaultProperty("Time")]
	[Serializable]
	public class TradingEvent
	{
	    public Balance Balance { get; set; }

	    public DateTime Time { get; set; }

	    public TradingEvent()
		{
			Balance = new Balance();
		}

		public TradingEvent(DateTime time, Balance objBalance)
		{
			Balance = new Balance();
			Time = time;
			Balance = objBalance;
		}
	}

	public enum TradingTrend
	{
		Bid = -1,
		Neutral = 0,
		Ask = 1
	}

    [DefaultProperty("DisplayName")]
    [Serializable]
    public class Transaction
    {

        public string Id { get; set; }

        public string Symbol { get; set; }

        public DateTime Time { get; set; }

        public string TimeStamp { get; set; }

        public string TimeZone { get; set; }

        public TransactionType TransactionType { get; set; }

        public string Address { get; set; }

        public decimal Amount { get; set; }

        public decimal Fee { get; set; }

        [Browsable(false)]
        [XmlIgnore()]
        [JsonIgnore()]
        public virtual string DisplayName
        {
            get
            {
                return string.Format("{0} {1} - {2} : {3} {4} {5},  Address: {6}, Fee: {7}",
                    Time.ToShortDateString(), Time.ToShortTimeString(), TransactionType, Amount.ToString(CultureInfo.InvariantCulture), Symbol,
                    Address, Fee.ToString(CultureInfo.InvariantCulture));
            }
        }

    }

    public enum TransactionType
    {
        Deposit = 1,
        Withdrawal = 2,
    }

    public enum TradingAPIUrls
    {
        Ticker,
        MarketDepth,
        RecentTrades,
        GetBalance,
        BuyBTC,
        SellBTC,
        GetOrders,
        CancelOrder,
        SendBTC,
        GetDepositAddress,
        GetMarkets
    }
}
