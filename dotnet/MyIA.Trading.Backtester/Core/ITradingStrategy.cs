namespace MyIA.Trading.Backtester
{
	public interface ITradingStrategy
	{
		Wallet ComputeNewOrders(Wallet currentOrders, MarketInfo objMarket, ExchangeInfo objExchange, TradingHistory history);
	}
}