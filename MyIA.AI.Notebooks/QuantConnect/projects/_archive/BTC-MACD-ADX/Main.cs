#region imports
using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Globalization;
using System.Drawing;
using QuantConnect;
using QuantConnect.Algorithm.Framework;
using QuantConnect.Algorithm.Framework.Selection;
using QuantConnect.Algorithm.Framework.Alphas;
using QuantConnect.Algorithm.Framework.Portfolio;
using QuantConnect.Algorithm.Framework.Portfolio.SignalExports;
using QuantConnect.Algorithm.Framework.Execution;
using QuantConnect.Algorithm.Framework.Risk;
using QuantConnect.Api;
using QuantConnect.Parameters;
using QuantConnect.Benchmarks;
using QuantConnect.Brokerages;
using QuantConnect.Configuration;
using QuantConnect.Util;
using QuantConnect.Interfaces;
using QuantConnect.Algorithm;
using QuantConnect.Indicators;
using QuantConnect.Data;
using QuantConnect.Data.Auxiliary;
using QuantConnect.Data.Consolidators;
using QuantConnect.Data.Custom;
using QuantConnect.Data.Custom.IconicTypes;
using QuantConnect.DataSource;
using QuantConnect.Data.Fundamental;
using QuantConnect.Data.Market;
using QuantConnect.Data.Shortable;
using QuantConnect.Data.UniverseSelection;
using QuantConnect.Notifications;
using QuantConnect.Orders;
using QuantConnect.Orders.Fees;
using QuantConnect.Orders.Fills;
using QuantConnect.Orders.OptionExercise;
using QuantConnect.Orders.Slippage;
using QuantConnect.Orders.TimeInForces;
using QuantConnect.Python;
using QuantConnect.Scheduling;
using QuantConnect.Securities;
using QuantConnect.Securities.Equity;
using QuantConnect.Securities.Future;
using QuantConnect.Securities.Option;
using QuantConnect.Securities.Positions;
using QuantConnect.Securities.Forex;
using QuantConnect.Securities.Crypto;
using QuantConnect.Securities.CryptoFuture;
using QuantConnect.Securities.Interfaces;
using QuantConnect.Securities.Volatility;
using QuantConnect.Storage;
using QuantConnect.Statistics;
using QCAlgorithmFramework = QuantConnect.Algorithm.QCAlgorithm;
using QCAlgorithmFrameworkBridge = QuantConnect.Algorithm.QCAlgorithm;
#endregion

namespace QuantConnect.Algorithm.CSharp
{

    /// <summary>
    /// Algorithme de trading pour BTCUSDT utilisant un simple croisement EMA (12/26).
    /// Simplifie depuis MACD+ADX adaptatif pour ameliorer robustesse et Sharpe.
    /// </summary>
    public class BtcMacdAdxDaily1Algorithm : QCAlgorithm
    {


        // Parametres EMA (simplification de MACD)
        [Parameter("ema-fast")]
        public int EmaFast = 12;

        [Parameter("ema-slow")]
        public int EmaSlow = 26;

        // Symbole a trader (BTCUSDT)
        private Symbol _symbol;

        private const string TradedPairTicker = "BTCUSDT";

        // Indicateurs techniques
        private ExponentialMovingAverage _emaFast;
        private ExponentialMovingAverage _emaSlow;
        private AverageTrueRange _atr;  // ATR pour le filtre de volatilite

        // Parametre du filtre de volatilite (60%)
        [Parameter("volatility-threshold")]
        public decimal VolatilityThreshold = 0.60m;

        public override void Initialize()
        {
            // Initialisation de la periode du backtest
            this.InitPeriod();

            // Initialisation du capital de depart en USDT
            SetAccountCurrency("USDT");
            SetCash(5000);

            // Configuration du modele de courtage (Binance, compte Cash)
            SetBrokerageModel(BrokerageName.Binance, AccountType.Cash);

            // Ajout du symbole BTCUSDT avec une resolution quotidienne
            var security = AddCrypto(TradedPairTicker, Resolution.Daily);
            _symbol = security.Symbol;
            this.SetBenchmark(_symbol);

            // Configuration de la periode de chauffe (50 jours pour EMA lente)
            SetWarmUp(TimeSpan.FromDays(50));

            // Initialisation des indicateurs EMA
            _emaFast = EMA(_symbol, EmaFast, Resolution.Daily);
            _emaSlow = EMA(_symbol, EmaSlow, Resolution.Daily);

            // Initialisation de l'ATR (14 periodes par defaut) pour le filtre de volatilite
            _atr = ATR(_symbol, 14, MovingAverageType.Simple, Resolution.Daily);
        }

        /// <summary>
        /// Calcule la volatilite relative actuelle basee sur l'ATR.
        /// La volatilite est exprimee en pourcentage du prix actuel.
        /// </summary>
        /// <returns>Volatilite actuelle (0.0 a 1.0+)</returns>
        private decimal CalculateVolatility()
        {
            if (!_atr.IsReady)
                return 0m;

            var currentPrice = Securities[_symbol].Price;
            if (currentPrice == 0)
                return 0m;

            // ATR normalise par le prix = volatilite en pourcentage
            return (decimal)_atr.Current.Value / currentPrice;
        }

        /// <summary>
        /// Methode principale appelee a chaque nouvelle donnee de marche.
        /// </summary>
        /// <param name="data">Donnees de marche pour le symbole suivi.</param>
        public override void OnData(Slice data)
        {
            // Verifie si la periode de chauffe est terminee et si les indicateurs sont prets
            if (IsWarmingUp || !_emaFast.IsReady || !_emaSlow.IsReady || !_atr.IsReady)
                return;

            // Verifie si les donnees pour le symbole sont disponibles
            if (!data.ContainsKey(_symbol))
                return;

            // Filtre de volatilite: eviter de trader lorsque la volatilite est trop elevee (>60%)
            var volatility = CalculateVolatility();
            if (volatility > VolatilityThreshold)
            {
                Debug($"[Volatility Filter] Skip trade - Vol: {volatility:P2} > Threshold: {VolatilityThreshold:P2}");
                return;
            }

            // Simple logique de croisement EMA
            // Signal d'achat: EMA rapide croise au-dessus de l'EMA lente
            if (_emaFast > _emaSlow && !Portfolio.Invested)
            {
                SetHoldings(_symbol, 1);
            }
            // Signal de vente: EMA rapide croise en-dessous de l'EMA lente
            else if (_emaFast < _emaSlow && Portfolio.Invested)
            {
                Liquidate(_symbol);
            }
        }


        /// <summary>
        /// Evenements declenches lors de l'execution d'ordres (achat/vente).
        /// </summary>
        /// <param name="orderEvent">Informations sur l'ordre execute.</param>
        public override void OnOrderEvent(OrderEvent orderEvent)
        {
            // Verifie si l'ordre a ete rempli
            if (orderEvent.Status == OrderStatus.Filled)
            {
                // Determine le type d'operation (achat ou vente)
                string operation = orderEvent.Direction == OrderDirection.Buy ? "Achat" : "Vente";

                // Construction du message de journalisation
                string message = $"{Time.ToShortDateString()} - {operation} de {Math.Abs(orderEvent.FillQuantity)} unites de {_symbol} au prix de {orderEvent.FillPrice} USDT.";

                // Ajout des informations sur le portefeuille
                message += $" Valeur totale du portefeuille : {Portfolio.TotalPortfolioValue} USDT.";

                // Enregistrement dans le journal
                Log(message);
            }
        }

        /// <summary>
        /// Methode initialisation la periode de backtest.
        /// </summary>
        private void InitPeriod()
        {
            // Extended: covers pre-COVID, COVID crash, bear 2022, recovery 2023-2025
            // Note: 500-day warmup needs data from ~Nov 2017 (Binance BTCUSDT available)
            SetStartDate(2019, 4, 1);
        }

    }
}
