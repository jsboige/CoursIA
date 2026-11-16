using System;
using System.Collections.Generic;
using System.ComponentModel;

namespace MyIA.Trading.Backtester
{
    [Serializable]
    public class TradingSeries
    {
        public TradingSeries()
        {
            Instances = new List<TradingEvent>();
        }

        public TradingSeries(int maxNbItems, TimeSpan period)
            : this()
        {
            MaxNbItems = maxNbItems;
            Period = period;
        }

        public List<TradingEvent> Instances { get; }

        [Browsable(false)]
        public int MaxNbItems { get; set; }

        [Browsable(false)]
        public TimeSpan Period { get; set; }

        public decimal EarningsPerPeriodRate
        {
            get { return decimal.Round(TotalEarningsRate * GetSpanRatio(), 3); }
        }

        public decimal TotalEarnings
        {
            get
            {
                if (Instances.Count > 1)
                {
                    return decimal.Round(
                        Instances[0].Balance.Total - Instances[Instances.Count - 1].Balance.Total,
                        5);
                }
                return 0m;
            }
        }

        public decimal TotalEarningsRate
        {
            get
            {
                if (Instances.Count > 1 && Instances[Instances.Count - 1].Balance.Total > 0m)
                {
                    return decimal.Round(
                        TotalEarnings / Instances[Instances.Count - 1].Balance.Total * 100m,
                        3);
                }
                return 0m;
            }
        }

        public decimal TotalEarningsFixedPrice
        {
            get
            {
                if (Instances.Count > 1)
                {
                    return decimal.Round(
                        Instances[0].Balance.Total
                        - (Instances[Instances.Count - 1].Balance.Secondary
                           + Instances[Instances.Count - 1].Balance.Primary * Instances[0].Balance.TickerLast),
                        5);
                }
                return 0m;
            }
        }

        public decimal TotalEarningsRateFixedPrice
        {
            get
            {
                if (Instances.Count > 1 && Instances[Instances.Count - 1].Balance.Total > 0m)
                {
                    return decimal.Round(
                        TotalEarningsFixedPrice
                        / (Instances[Instances.Count - 1].Balance.Secondary
                           + Instances[Instances.Count - 1].Balance.Primary * Instances[0].Balance.TickerLast)
                        * 100m,
                        3);
                }
                return 0m;
            }
        }

        public void AddEvent(TradingEvent objEvent)
        {
            if (Instances.Count > 0)
            {
                if (Instances[0].Balance.Total == 0m)
                {
                    Instances.RemoveAt(0);
                }
                else if ((Period.TotalDays < 10 && TotalEarningsRateFixedPrice > 30m)
                         || TotalEarningsRateFixedPrice > 100m)
                {
                    Instances.RemoveAt(Instances.Count - 1);
                }
            }

            if (Instances.Count == 0 || objEvent.Time.Subtract(Instances[0].Time) > Period)
            {
                Instances.Insert(0, objEvent);
                if (Instances.Count > MaxNbItems)
                {
                    Instances.RemoveRange(MaxNbItems, Instances.Count - MaxNbItems);
                }
            }
        }

        private decimal GetSpanRatio()
        {
            if (Period.Ticks > 0 && Instances.Count > 0)
            {
                decimal span = Instances[0].Time.Subtract(Instances[Instances.Count - 1].Time).Ticks;
                if (span > 0m)
                {
                    return Period.Ticks / span;
                }
            }
            return 1m;
        }
    }
}
