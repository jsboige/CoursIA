// #region imports
// using System;
// using System.Collections;
// using System.Collections.Generic;
// using System.Linq;
// using System.Globalization;
// using System.Drawing;
// using QuantConnect;
// using QuantConnect.Algorithm.Framework;
// using QuantConnect.Algorithm.Framework.Selection;
// using QuantConnect.Algorithm.Framework.Alphas;
// using QuantConnect.Algorithm.Framework.Portfolio;
// using QuantConnect.Algorithm.Framework.Portfolio.SignalExports;
// using QuantConnect.Algorithm.Framework.Execution;
// using QuantConnect.Algorithm.Framework.Risk;
// using QuantConnect.Api;
// using QuantConnect.Parameters;
// using QuantConnect.Benchmarks;
// using QuantConnect.Brokerages;
// using QuantConnect.Configuration;
// using QuantConnect.Util;
// using QuantConnect.Interfaces;
// using QuantConnect.Algorithm;
// using QuantConnect.Indicators;
// using QuantConnect.Data;
// using QuantConnect.Data.Auxiliary;
// using QuantConnect.Data.Consolidators;
// using QuantConnect.Data.Custom;
// using QuantConnect.Data.Custom.IconicTypes;
// using QuantConnect.DataSource;
// using QuantConnect.Data.Fundamental;
// using QuantConnect.Data.Market;
// using QuantConnect.Data.Shortable;
// using QuantConnect.Data.UniverseSelection;
// using QuantConnect.Notifications;
// using QuantConnect.Orders;
// using QuantConnect.Orders.Fees;
// using QuantConnect.Orders.Fills;
// using QuantConnect.Orders.OptionExercise;
// using QuantConnect.Orders.Slippage;
// using QuantConnect.Orders.TimeInForces;
// using QuantConnect.Python;
// using QuantConnect.Scheduling;
// using QuantConnect.Securities;
// using QuantConnect.Securities.Equity;
// using QuantConnect.Securities.Future;
// using QuantConnect.Securities.Option;
// using QuantConnect.Securities.Positions;
// using QuantConnect.Securities.Forex;
// using QuantConnect.Securities.Crypto;
// using QuantConnect.Securities.CryptoFuture;
// using QuantConnect.Securities.Interfaces;
// using QuantConnect.Securities.Volatility;
// using QuantConnect.Storage;
// using QuantConnect.Statistics;
// using QCAlgorithmFramework = QuantConnect.Algorithm.QCAlgorithm;
// using QCAlgorithmFrameworkBridge = QuantConnect.Algorithm.QCAlgorithm;
// #endregion

// namespace QuantConnect.Algorithm.CSharp
// {

//     /// <summary>
//     /// Algorithme de trading pour BTCUSDT utilisant les indicateurs MACD et ADX.
//     /// </summary>
//     public class BtcMacdAdxDaily1Algorithm2 : QCAlgorithm
//     {

//         //L'attribut Parameter permet de définir les paramètres dans le fichier de configuration, et d'utiliser une optimisation

//         // Paramètres de l'indicateur MACD
//         [Parameter("macd-fast")]
//         public int MacdFast = 12; //15

//         [Parameter("macd-slow")]
//         public int MacdSlow = 26; //25

//         [Parameter("macd-signal")]
//         public int MacdSignal = 9; //12

//         // Paramètres de l'indicateur ADX
//         [Parameter("adx-period")]
//         public int AdxPeriod = 25;

//         [Parameter("adx-high")]
//         public int AdxHigh = 20;

//         [Parameter("adx-low")]
//         public int AdxLow = 15;

//         // Symbole à trader (BTCUSDT)
//         private Symbol _symbol;

//         private const string TradedPairTicker = "BTCUSDT";
//         //private string _ticker = "AAPL";
//         //private string _ticker = "FB";

//         // Indicateurs techniques
//         private  MovingAverageConvergenceDivergence _macd;
//         private  AverageDirectionalIndex _adx;

//         // Noms pour les graphiques
//         private const string ChartName = "Trade Plot";
//         private const string PriceSeriesName = "Price";
//         private const string PortfolioValueSeriesName = "PortFolioValue";
//         private const string MacdSeriesName = "MACD";
//         private const string AdxSeriesName = "ADX";


//         public override void Initialize()
//         {

//             // Initialisation de la période du backtest
//             this.InitPeriod();

//             // Initialisation du capital de départ en USDT
//             SetAccountCurrency("USDT");    // Devise du compte
//             SetCash(5000);               // Capital initial de 600 000 USDT


//             // Configuration du modèle de courtage (Binance, compte Cash)
//             SetBrokerageModel(BrokerageName.Binance, AccountType.Cash);

//             // Ajout du symbole BTCUSDT avec une résolution quotidienne
//             var security = AddCrypto(TradedPairTicker, Resolution.Daily);
//             _symbol = security.Symbol;
//             this.SetBenchmark(_symbol);

//             // Configuration de la période de chauffe (1 an de données)
//             SetWarmUp(TimeSpan.FromDays(365));
//             //var security = AddEquity(_ticker, Resolution.Daily);

//             // Initialisation des indicateurs techniques
//             _macd = MACD(
//                 _symbol,
//                 MacdFast,     // Période de la moyenne mobile rapide
//                 MacdSlow,     // Période de la moyenne mobile lente
//                 MacdSignal,   // Période de la ligne de signal
//                 MovingAverageType.Exponential,
//                 Resolution.Daily,
//                 Field.Close);

//             _adx = ADX(_symbol, AdxPeriod, Resolution.Daily);

//             // Configuration des graphiques pour visualiser les données
//             // InitializeCharts();
            
//         }

//         /// <summary>
//         /// Initialise les graphiques et séries pour la visualisation.
//         /// </summary>
//         private void InitializeCharts()
//         {
//             // Création du graphique principal
//             var stockPlot = new Chart(ChartName);

//             // Séries pour le prix de l'actif, la valeur du portefeuille, MACD et ADX
//             var assetPriceSeries = new Series(PriceSeriesName, SeriesType.Line, "$", Color.Blue);
//             var portfolioValueSeries = new Series(PortfolioValueSeriesName, SeriesType.Line, "$", Color.Green);
//             var macdSeries = new Series(MacdSeriesName, SeriesType.Line, "", Color.Purple);
//             var adxSeries = new Series(AdxSeriesName, SeriesType.Line, "", Color.Pink);

//             // Ajout des séries au graphique
//             stockPlot.AddSeries(assetPriceSeries);
//             stockPlot.AddSeries(portfolioValueSeries);
//             stockPlot.AddSeries(macdSeries);
//             stockPlot.AddSeries(adxSeries);

//             // Ajout du graphique à l'algorithme
//             AddChart(stockPlot);

//             // Planification de l'exécution de la méthode DoPlots chaque jour pour mettre à jour les graphiques
//             Schedule.On(
//                 DateRules.EveryDay(),
//                 TimeRules.Every(TimeSpan.FromDays(1)),
//                 DoPlots);
//         }

//         /// <summary>
//         /// Met à jour les graphiques avec les données actuelles.
//         /// </summary>
//         private void DoPlots()
//         {
//             // Vérifie que les données sont disponibles pour le symbole
//             if (!Securities.ContainsKey(_symbol) || !Securities[_symbol].HasData)
//                 return;

//             // Récupération du prix actuel de l'actif
//             var price = Securities[_symbol].Price;

//             // Mise à jour des séries du graphique avec les valeurs actuelles
//             Plot(ChartName, PriceSeriesName, price);
//             Plot(ChartName, PortfolioValueSeriesName, Portfolio.TotalPortfolioValue);
//             Plot(ChartName, MacdSeriesName, _macd);
//             Plot(ChartName, AdxSeriesName, _adx);
//         }

//         /// <summary>
//         /// Méthode principale appelée à chaque nouvelle donnée de marché.
//         /// </summary>
//         /// <param name="data">Données de marché pour le symbole suivi.</param>
//         public override void OnData(Slice data)
//         {

//            // Vérifie si la période de chauffe est terminée et si les indicateurs sont prêts
//             if (IsWarmingUp || !_macd.IsReady || !_adx.IsReady)
//                 return;

//             // Vérifie si les données pour le symbole sont disponibles
//             if (!data.ContainsKey(_symbol))
//                 return;

//             // Récupération des informations actuelles
//             var holdings = Portfolio[_symbol].Quantity;   // Quantité détenue
//             var currentPrice = data[_symbol].Close;       // Prix de clôture actuel

//             // Calcul de l'histogramme du MACD (différence entre la ligne MACD et la ligne de signal)
//             var macdHistogram = _macd.Current.Value - _macd.Signal.Current.Value;

//             // Détermination des signaux MACD
//             var isMacdBullish = macdHistogram > 0;    // Signal haussier si l'histogramme est positif
//             var isMacdBearish = macdHistogram < 0;    // Signal baissier si l'histogramme est négatif

//             // Récupération de la valeur actuelle de l'ADX
//             var adxValue = _adx.Current.Value;

//             // Conditions d'entrée en position longue
//             if (adxValue >= AdxHigh && isMacdBullish)
//             {
//                 // Si le portefeuille n'est pas déjà investi
//                 if (!Portfolio.Invested)
//                 {
//                     // Investit 100% du capital disponible dans le symbole
//                     SetHoldings(_symbol, 1);
//                     // Debug($"Acheté {_symbol} au prix de {currentPrice}");
//                 }
//             }
//             // Conditions de sortie de position
//             else if (adxValue < AdxLow && isMacdBearish)
//             {
//                 // Si le portefeuille est investi
//                 if (Portfolio.Invested)
//                 {
//                     // Liquide la position sur le symbole
//                     Liquidate(_symbol);
//                     // Debug($"Vendu {_symbol} au prix de {currentPrice}");
//                 }
//             }
//         }


//         /// <summary>
//         /// Événements déclenchés lors de l'exécution d'ordres (achat/vente).
//         /// </summary>
//         /// <param name="orderEvent">Informations sur l'ordre exécuté.</param>
//         public override void OnOrderEvent(OrderEvent orderEvent)
//         {
//             // Vérifie si l'ordre a été rempli
//             if (orderEvent.Status == OrderStatus.Filled)
//             {
//                 // Détermine le type d'opération (achat ou vente)
//                 string operation = orderEvent.Direction == OrderDirection.Buy ? "Achat" : "Vente";

//                 // Construction du message de journalisation
//                 string message = $"{Time.ToShortDateString()} - {operation} de {Math.Abs(orderEvent.FillQuantity)} unités de {_symbol} au prix de {orderEvent.FillPrice} USDT.";

//                 // Ajout des informations sur le portefeuille
//                 message += $" Valeur totale du portefeuille : {Portfolio.TotalPortfolioValue} USDT.";

//                 // Enregistrement dans le journal
//                 Log(message);
//             }
//         }

//         /// <summary>
//         /// Méthode initialisation la période de backtest. Plusieurs périodes intéressantes sont proposées en commentaires.
//         /// </summary>
//         private void InitPeriod()
//         {
//             //SetStartDate(2013, 04, 07); // début backtest 164
//             //SetEndDate(2015, 01, 14); // fin backtest 172


//             //SetStartDate(2014, 02, 08); // début backtest 680
//             //SetEndDate(2016, 11, 07); // fin backtest 703


//             //SetStartDate(2017, 08, 08); // début backtest 3412
//             //SetEndDate(2019, 02, 05); // fin backtest 3432

//             //SetStartDate(2018, 01, 30); // début backtest 9971
//             //SetEndDate(2020, 07, 26); // fin backtest 9945


//             //SetStartDate(2017, 12, 15); // début backtest 17478
//             //SetEndDate(2022, 12, 12); // fin backtest 17209

//             //SetStartDate(2017, 11, 25); // début backtest 8718
//             //SetEndDate(2020, 05, 1); // fin backtest 8832

//             //SetStartDate(2022, 5, 1); // début backtest 29410
//             //SetEndDate(2024, 02, 11); // fin backtest 29688

//             // SetStartDate(2011, 04, 07); // début backtest 164
//             // SetEndDate(2024, 01, 29);


//             // SetStartDate(2021, 10, 16); //61672
//             // SetEndDate(2024, 10, 11); //60326

//             SetStartDate(2013, 04, 07); // début backtest 164

//         }

//     }
// }
