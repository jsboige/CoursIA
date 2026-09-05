namespace MyIA.Trading.Backtester
{
    public class SimulationSetup
    {
        public Wallet Walllet { get; set; }


        public ITradingStrategy Strategy { get; set; }

        public TradingHistory TradingHistory { get; set; } = new TradingHistory();

    }
}