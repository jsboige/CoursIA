using System;
using System.Diagnostics;
using Newtonsoft.Json;

namespace MyIA.Trading.Backtester
{
    /// <summary>
    /// Snapshot JSON d'un etat de simulation (ticker, market depth, wallet). Le port
    /// d'origine laissait les accesseurs Market et Wallet en stub avec un commentaire
    /// "migrate the following to Newtonsoft json.net" : la migration est portee ici
    /// avec la lib deja en solution. Les deserialisations ciblent Ticker/MarketDepth/
    /// Wallet directement (props publiques) plutot que TickerInfo, dont le champ
    /// public ticker n'est pas couvert par le contract resolver par defaut.
    /// </summary>
    [Serializable]
    public class SimulationData
    {
        public string JsonMarketDepth { get; set; }

        public string JsonTicker { get; set; }

        public string JsonWallet { get; set; }

        public MarketInfo Market
        {
            get
            {
                var ticker = Deserialize<Ticker>(JsonTicker);
                var depth = Deserialize<MarketDepth>(JsonMarketDepth);
                if (ticker == null && depth == null)
                {
                    return new MarketInfo();
                }
                return new MarketInfo(ticker, depth);
            }
        }

        public Wallet Wallet
        {
            get
            {
                return Deserialize<Wallet>(JsonWallet) ?? new Wallet();
            }
        }

        private static T Deserialize<T>(string json) where T : class
        {
            if (string.IsNullOrWhiteSpace(json))
            {
                return null;
            }
            try
            {
                return JsonConvert.DeserializeObject<T>(json);
            }
            catch (JsonException)
            {
                return null;
            }
        }

        [DebuggerNonUserCode]
        public SimulationData()
        {
        }
    }
}
