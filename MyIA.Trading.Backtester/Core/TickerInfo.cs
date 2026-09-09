using System;
using System.Diagnostics;

namespace MyIA.Trading.Backtester
{
    public class TickerInfo : ResponseObject
    {
        public Ticker ticker;

        [DebuggerNonUserCode]
        public TickerInfo()
        {
        }
    }
}
