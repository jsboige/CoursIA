using System;
using System.Collections.Generic;

namespace MyIA.Trading.Backtester
{
    /// <summary>
    /// Collection ordonnee de strategies contextuelles appliquees en sequence au meme
    /// contexte de trading. Le port d'origine heritait de ProviderHost (registre de
    /// types destine a la grille UI DNN via GetAvailableProviders/GetInitialTypes) :
    /// cette plomberie de selection visuelle n'est pas portee, la liste d'instances
    /// qu'elle alimentait le devient directement.
    /// </summary>
    [Serializable]
    public class TradingStrategies : IContextualStrategy, ITradingStrategy
    {
        public List<IContextualStrategy> Instances { get; set; }

        public TradingStrategies()
        {
            this.Instances = new List<IContextualStrategy>();
        }

        public void ComputeNewOrders(ref TradingContext tContext)
        {
            foreach (IContextualStrategy objAction in this.Instances)
            {
                objAction.ComputeNewOrders(ref tContext);
            }
        }

        public Wallet ComputeNewOrders(Wallet currentOrders, MarketInfo objMarket, ExchangeInfo objExchange, TradingHistory history)
        {
            //the newOrders Wallet variable will contain all ask/bid/cancel orders to issue

            var newOrders = new Wallet();

            decimal avBtcsForTrading = currentOrders.PrimaryBalance;
            decimal avUsdsForTrading = currentOrders.SecondaryBalance;

            //Then We simplify the current orders by merging orders of the same price, issueing corresponding cancel/new orders
            newOrders.ConsolidateOrders(ref currentOrders, true);

            //Feed the new orders wallet with available resources, Reserve resources for current open orders
            newOrders.PrimaryBalance = Math.Max(avBtcsForTrading - currentOrders.GetTotalAsksPrimary(), 0m);
            newOrders.SecondaryBalance = Math.Max(avUsdsForTrading - currentOrders.GetTotalBidsSecondary(), 0m);

            var tContext = new TradingContext(currentOrders, newOrders, objMarket, objExchange, history.GetLastTrend(), this);

            this.ComputeNewOrders(ref tContext);

            tContext.NewOrders.FitOrders(objExchange);
            //we update the trading history with last data
            history.Update(currentOrders, objMarket, tContext.NewOrders);
            return tContext.NewOrders;
        }
    }
}
