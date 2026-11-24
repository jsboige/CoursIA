using System;

namespace MyIA.Trading.Backtester
{
	public interface IContextualStrategy
	{
		void ComputeNewOrders(ref TradingContext tContext);
	}
}