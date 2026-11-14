using System;

namespace MyIA.Trading.Backtester
{
    /// <summary>
    /// Strategie d'emission d'un ordre fixe dont chaque champ peut etre recalcule a
    /// chaque step par expression dynamique. Le clonage de l'ordre statique utilisait
    /// ReflectionHelper.CloneObject (Aricie) : substitue par l'extension DeepClone
    /// (round-trip JSON) comme sur le reste du port.
    /// </summary>
    [Serializable]
    public class IssueOrderStrategy : TradingStrategyBase
    {
        public Order StaticOrder { get; set; }

        public bool DynamicAmount { get; set; }

        public SimpleExpression<decimal> DynamicAmountExpression { get; set; }

        public bool DynamicPrice { get; set; }

        public SimpleExpression<decimal> DynamicPriceExpression { get; set; }

        public bool DynamicType { get; set; }

        public SimpleExpression<int> DynamicTypeExpression { get; set; }

        public bool DynamicId { get; set; }

        public SimpleExpression<string> DynamicIdExpression { get; set; }

        public IssueOrderStrategy()
        {
            this.StaticOrder = new Order();
            this.DynamicAmountExpression = new SimpleExpression<decimal>();
            this.DynamicPriceExpression = new SimpleExpression<decimal>();
            this.DynamicTypeExpression = new SimpleExpression<int>();
            this.DynamicIdExpression = new SimpleExpression<string>();
        }

        public override void ComputeNewOrders(ref TradingContext tContext)
        {
            var newOrder = this.StaticOrder.DeepClone();
            if (this.DynamicAmount)
            {
                newOrder.Amount = this.DynamicAmountExpression.Evaluate(tContext);
            }
            if (this.DynamicPrice)
            {
                newOrder.Price = this.DynamicPriceExpression.Evaluate(tContext);
            }
            if (this.DynamicType)
            {
                newOrder.Type = this.DynamicTypeExpression.Evaluate(tContext);
            }
            if (this.DynamicId)
            {
                newOrder.Oid = this.DynamicIdExpression.Evaluate(tContext);
            }
            tContext.NewOrders.Orders.Add(newOrder);
        }
    }
}
