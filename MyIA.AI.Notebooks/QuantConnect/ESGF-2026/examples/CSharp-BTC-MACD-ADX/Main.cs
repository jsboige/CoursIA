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
    /// Simplifié depuis MACD+ADX adaptatif pour améliorer robustesse et Sharpe.
    /// </summary>
    public class BtcMacdAdxDaily1Algorithm : QCAlgorithm
    {
        // Paramètres EMA (simplification de MACD)
        [Parameter("ema-fast")]
        public int EmaFast = 12;

        [Parameter("ema-slow")]
        public int EmaSlow = 26;

        // Symbole à trader (BTCUSDT)
        private Symbol _symbol;

        private const string TradedPairTicker = "BTCUSDT";

        // Indicateurs techniques
        private ExponentialMovingAverage _emaFast;
        private ExponentialMovingAverage _emaSlow;

        public override void Initialize()
        {
            // Initialisation de la période du backtest
            this.InitPeriod();

            // Initialisation du capital de départ en USDT
            SetAccountCurrency("USDT");
            SetCash(5000);

            // Configuration du modèle de courtage (Binance, compte Cash)
            SetBrokerageModel(BrokerageName.Binance, AccountType.Cash);

            // Ajout du symbole BTCUSDT avec une résolution quotidienne
            var security = AddCrypto(TradedPairTicker, Resolution.Daily);
            _symbol = security.Symbol;
            this.SetBenchmark(_symbol);

            // Configuration de la période de chauffe (50 jours pour EMA lente)
            SetWarmUp(TimeSpan.FromDays(50));

            // Initialisation des indicateurs EMA
            _emaFast = EMA(_symbol, EmaFast, Resolution.Daily);
            _emaSlow = EMA(_symbol, EmaSlow, Resolution.Daily);
        }

        /// <summary>
        /// Méthode principale appelée à chaque nouvelle donnée de marché.
        /// </summary>
        /// <param name="data">Données de marché pour le symbole suivi.</param>
        public override void OnData(Slice data)
        {
            // Vérifie si la période de chauffe est terminée et si les indicateurs sont prêts
            if (IsWarmingUp || !_emaFast.IsReady || !_emaSlow.IsReady)
                return;

            // Vérifie si les données pour le symbole sont disponibles
            if (!data.ContainsKey(_symbol))
                return;

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
        /// Événements déclenchés lors de l'exécution d'ordres (achat/vente).
        /// </summary>
        /// <param name="orderEvent">Informations sur l'ordre exécuté.</param>
        public override void OnOrderEvent(OrderEvent orderEvent)
        {
            // Vérifie si l'ordre a été rempli
            if (orderEvent.Status == OrderStatus.Filled)
            {
                // Détermine le type d'opération (achat ou vente)
                string operation = orderEvent.Direction == OrderDirection.Buy ? "Achat" : "Vente";

                // Construction du message de journalisation
                string message = $"{Time.ToShortDateString()} - {operation} de {Math.Abs(orderEvent.FillQuantity)} unités de {_symbol} au prix de {orderEvent.FillPrice} USDT.";

                // Ajout des informations sur le portefeuille
                message += $" Valeur totale du portefeuille : {Portfolio.TotalPortfolioValue} USDT.";

                // Enregistrement dans le journal
                Log(message);
            }
        }

        /// <summary>
        /// Méthode initialisation la période de backtest. Plusieurs périodes intéressantes sont proposées en commentaires.
        /// </summary>
        private void InitPeriod()
        {
            //SetStartDate(2013, 04, 07); // début backtest 164
            //SetEndDate(2015, 01, 14); // fin backtest 172


            //SetStartDate(2014, 02, 08); // début backtest 680
            //SetEndDate(2016, 11, 07); // fin backtest 703


            //SetStartDate(2017, 08, 08); // début backtest 3412
            //SetEndDate(2019, 02, 05); // fin backtest 3432

            //SetStartDate(2018, 01, 30); // début backtest 9971
            //SetEndDate(2020, 07, 26); // fin backtest 9945


            //SetStartDate(2017, 12, 15); // début backtest 17478
            //SetEndDate(2022, 12, 12); // fin backtest 17209

            //SetStartDate(2017, 11, 25); // début backtest 8718
            //SetEndDate(2020, 05, 1); // fin backtest 8832

            //SetStartDate(2022, 5, 1); // début backtest 29410
            //SetEndDate(2024, 02, 11); // fin backtest 29688

            // SetStartDate(2011, 04, 07); // début backtest 164
            // SetEndDate(2024, 01, 29);


            // SetStartDate(2021, 10, 16); //61672
            // SetEndDate(2024, 10, 11); //60326

            // Extended: covers pre-COVID, COVID crash, bear 2022, recovery 2023-2025
            // Note: 500-day warmup needs data from ~Nov 2017 (Binance BTCUSDT available)
            SetStartDate(2019, 4, 1);

        }

    }
}
