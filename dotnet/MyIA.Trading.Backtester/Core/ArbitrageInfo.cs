using System;

namespace MyIA.Trading.Backtester
{
    public class ArbitrageInfo
    {
        public Order Order1 { get; set; }

        public Order Order2 { get; set; }

        public ArbitrageInfo()
        {
            Order1 = new Order();
            Order2 = new Order();
        }

        public ArbitrageInfo(Order order1, Order order2)
        {
            this.Order1 = order1;
            this.Order2 = order2;
        }
    }
}
