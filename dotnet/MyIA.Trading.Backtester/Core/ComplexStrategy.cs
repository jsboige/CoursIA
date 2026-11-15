using System;
using System.Collections;

namespace MyIA.Trading.Backtester
{
    /// <summary>
    /// Enveloppe conditionnelle autour d'une strategie : l'expression Condition est
    /// evaluee contre le contexte a chaque step, et la strategie porte n'est appliquee
    /// que si elle est vraie.
    /// </summary>
    [Serializable]
    public class ComplexStrategy<TStrategy> : IContextualStrategy
        where TStrategy : TradingStrategyBase, new()
    {
        public TStrategy Strategy { get; set; }

        public string NewStatus { get; set; }

        public bool IsConditional { get; set; }

        public SimpleExpression<bool> Condition { get; set; }

        public CompoundTradingStrategy Alternate { get; set; }

        public bool IsLoop { get; set; }

        public SimpleExpression<IEnumerable> LoopEnumerableExpression { get; set; }

        public string LoopCurrentItemName { get; set; }

        public ComplexStrategy()
        {
            this.Condition = new SimpleExpression<bool>("true");
            this.Alternate = new CompoundTradingStrategy();
            this.LoopEnumerableExpression = new SimpleExpression<IEnumerable>();
            this.LoopCurrentItemName = "CurrentItem";
        }

        public void ComputeNewOrders(ref TradingContext tContext)
        {
            if (this.Condition.Evaluate(tContext))
            {
                this.Strategy.ComputeNewOrders(ref tContext);
                if (!string.IsNullOrEmpty(this.NewStatus))
                {
                    tContext.CurrentOrders.Status = this.NewStatus;
                    tContext.NewOrders.Status = this.NewStatus;
                }
            }
        }
    }
}
