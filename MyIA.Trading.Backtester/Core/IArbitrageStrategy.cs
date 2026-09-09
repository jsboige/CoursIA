namespace MyIA.Trading.Backtester
{
    public interface IArbitrageStrategy
    {
        ArbitrageInfo ComputeArbitrage(Wallet objWallet1, MarketInfo objMarket1, ExchangeInfo objExchange1, Wallet objWallet2, MarketInfo objMarket2, ExchangeInfo objExchange2);
    }
}
