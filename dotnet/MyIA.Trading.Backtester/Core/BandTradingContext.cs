using System;

namespace MyIA.Trading.Backtester
{
    /// <summary>
    /// Vue du contexte de trading typee pour les strategies de bande : reexpose la
    /// strategie de base sous sa forme concrete pour la resolution des chemins
    /// d'expressions ("Strategy.LimitOrderValueRate" par exemple).
    /// </summary>
    public class BandTradingContext : TradingContext
    {
        public TradingStrategy Strategy
        {
            get
            {
                return (TradingStrategy)base.BaseStrategy;
            }
        }

        public BandTradingContext()
        {
        }

        public BandTradingContext(TradingContext objBaseContext)
            : base(objBaseContext.CurrentOrders, objBaseContext.NewOrders, objBaseContext.Market, objBaseContext.Exchange, objBaseContext.LastTrend, objBaseContext.BaseStrategy)
        {
        }
    }
}
