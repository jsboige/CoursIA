using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Threading;
using Accord.MachineLearning;
using MyIA.Trading.Backtester;
using FileHelpers;
using Newtonsoft.Json;

namespace MyIA.Trading.Backtester
{
    public class BackTesting
    {
        public BackTestingConfig Config { get; set; } = new BackTestingConfig();


        public void Run(Action<string> logger)
        {


            logger("Entering Backtesting");

            
            var multiResults = new Dictionary<string, Dictionary<int,BacktestResult>>();

            for (var simulationIndex = 0; simulationIndex < Config.Simulations.Count; simulationIndex++)
            {
                var configSimulation = Config.Simulations[simulationIndex];
                var tradeFileName = configSimulation.DatasourcePath;


                var backTestingSettings = LoadModels(logger, configSimulation, out var bestBackTesting);


                var backTestingName = Config.GetBackTestingFileName(configSimulation);
                var digestName = backTestingName.Replace(Path.GetExtension(backTestingName) ?? string.Empty,
                    $".{backTestingSettings.Count}.digest.csv");
                (new FileInfo(digestName)).Directory?.Create();

                IEnumerable<BacktestResult> digestRecords = null;


                if (File.Exists(digestName))
                {
                    switch (Config.Mode)
                    {
                        case BackTestingMode.SVMModels:

                            var previousCulture = Thread.CurrentThread.CurrentCulture;
                            Thread.CurrentThread.CurrentCulture = new CultureInfo("fr-FR");
                            var engine = new FileHelperEngine<BacktestResult>();
                            engine.Options.IgnoreFirstLines = 1;
                            digestRecords = engine.ReadFile(digestName);
                            Thread.CurrentThread.CurrentCulture = previousCulture;
                            //foreach (var backtestResult in digestRecords)
                            //{

                            //}


                            break;
                        case BackTestingMode.Boosting:

                            break;
                        default:
                            throw new ArgumentOutOfRangeException();
                    }
                }
                else
                {
                    //var bitcoinTrain = Config.TrainingConfig.GetBitstampTrainingData(Config.SampleConfig, logger);
                    ////var modelName = tradingConfig.GetSampleTrainName(sampleConfig) + ".model.bin";
                    //var model = Config.TrainingConfig.TrainModel(Config.SampleConfig, bitcoinTrain, -1, logger);


                    //sampleConfig.Filename = sampleConfig.Filename.replace("bitstampUSD.csv", "rippleXRP.csv");
                    //sampleConfig.Filename = sampleConfig.Filename.Replace("bitstampUSD.csv", "krakenEUR.csv");
                    //var objSimulation = new BackTesting();


                    logger(
                        $"=======       Loading trades for new simulation from {configSimulation.DatasourcePath} between {configSimulation.StartDate} and {configSimulation.EndDate}       ========");


                    //tradeFileName = Config.TrainingConfig.DataConfig.SampleConfig.Filename.Replace("bitstampUSD", "krakenEUR");
                    //tradeFileName = Config.TrainingConfig.DataConfig.SampleConfig.Filename.Replace("bitstampUSD", "zaifJPY.2018-2020.0.5").Replace("bin.7z", "bin.lz4");


                    var objTrades = TradeHelper.Load(tradeFileName, configSimulation.StartDate,
                        configSimulation.EndDate, logger, true);
                    logger("Loaded original trades");

                    logger("building history");
                    var tradeHistory = objTrades.Select(objTrade =>
                            new OrderTrade()
                            {
                                Amount = objTrade.Amount, Price = objTrade.Price, UnixTime = objTrade.UnixTime
                            })
                        .ToList();
                    logger("built historic trades");


                    var objExchange = new ExchangeInfo()
                        {AskCommission = 0.3M, BidCommission = 0.3M, MinOrderAmount = 0, AmountDecil = 4};
                    var initialWallet = new Wallet()
                    {
                        PrimarySymbol = "BTC",
                        SecondarySymbol = "USD",
                        PrimaryBalance = 0,
                        SecondaryBalance = 10000,
                    };

                    var objWallet = initialWallet.DeepClone();

                    logger("starting Hodl simulation");

                    var objHodlStrategy = new HodlStrategy {AskReserveRate = 0, BidReserveRate = 0};


                    var hodlResult =
                        configSimulation.RunSimulation(objWallet, objHodlStrategy, objExchange, tradeHistory);

                    logger($"Results: {hodlResult.LastWallet.GetBalance(hodlResult.LastTicker).Total}");

                    logger("starting Machine learning simulation");

                    List<SimulationSetup> setups;
                    switch (Config.Mode)
                    {
                        case BackTestingMode.SVMModels:
                            setups = backTestingSettings.Select(objBacktestSettings => new SimulationSetup()
                            {
                                Strategy = objBacktestSettings.GetModelStrategy(logger),
                                Walllet = initialWallet.DeepClone()
                            }).ToList();


                            break;
                        case BackTestingMode.Boosting:
                            setups = new List<SimulationSetup>();
                            var boostedConfig = backTestingSettings[0].TrainingConfig.DeepClone();
                            boostedConfig.DataConfig.OutputPrediction = Config.BoostedPrediction;
                            boostedConfig.DataConfig.OutputThresold = Config.BoostedThresold;
                            boostedConfig.StopLossRate = Config.BoostedStopLoss;
                            var boostedStrategy = new BoostedStrategy(backTestingSettings)
                            {
                                TrainingConfig = boostedConfig,
                                Logger = logger,
                                AskReserveRate = 0,
                                BidReserveRate = 0
                            };

                            setups.Add(new SimulationSetup()
                                {Strategy = boostedStrategy, Walllet = initialWallet.DeepClone()});

                            break;
                        default:
                            throw new ArgumentOutOfRangeException();
                    }


                    logger($"{setups.Count} Simulation Setups prepared");


                    logger("Running simulation");
                    List<TradingHistory> results = configSimulation.RunSimulations(setups, objExchange, tradeHistory);

                    logger("Simulation finished");


                    //Log($"Results: {JsonConvert.SerializeObject(results, Formatting.Indented)}");


                    switch (Config.Mode)
                    {
                        case BackTestingMode.SVMModels:
                            for (var idxResult = 0; idxResult < results.Count; idxResult++)
                            {
                                var currentBackTestingSettings = backTestingSettings[idxResult];
                                currentBackTestingSettings.Results = results[idxResult];
                            }

                            backTestingSettings = backTestingSettings
                                .OrderBy(b => b.Results != null ? b.GetResult() : decimal.MinValue).Reverse().ToList();


                            var previousCulture = Thread.CurrentThread.CurrentCulture;
                            Thread.CurrentThread.CurrentCulture = new CultureInfo("fr-FR");

                            var engine = new FileHelperEngine<BacktestResult>();
                            engine.HeaderText = engine.GetFileHeader();


                            digestRecords = backTestingSettings.Select(objSetting => new BacktestResult()
                            {
                                BackTestPeriod = $"{configSimulation.StartDate}-{configSimulation.EndDate}",
                                ModelName = Path.GetFileName(objSetting.TrainingConfig.GetModelName()),
                                TestError = objSetting.TestError,
                                Result = objSetting.GetResult(),
                                TradeNb = objSetting.Results.Trades.Count,
                                Trade1 = (objSetting.Results.Trades.Count > 0)
                                    ? $" {objSetting.Results.Trades[0].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[0].Amount}@{objSetting.Results.Trades[0].Price}"
                                    : "",
                                Trade2 = (objSetting.Results.Trades.Count > 1)
                                    ? $" {objSetting.Results.Trades[1].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[1].Amount}@{objSetting.Results.Trades[1].Price}"
                                    : "",
                                Trade3 = (objSetting.Results.Trades.Count > 2)
                                    ? $" {objSetting.Results.Trades[2].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[2].Amount}@{objSetting.Results.Trades[2].Price}"
                                    : "",
                                Trade4 = (objSetting.Results.Trades.Count > 3)
                                    ? $" {objSetting.Results.Trades[3].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[3].Amount}@{objSetting.Results.Trades[3].Price}"
                                    : "",
                                Trade5 = (objSetting.Results.Trades.Count > 4)
                                    ? $" {objSetting.Results.Trades[4].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[4].Amount}@{objSetting.Results.Trades[4].Price}"
                                    : "",
                                Trade6 = (objSetting.Results.Trades.Count > 5)
                                    ? $" {objSetting.Results.Trades[5].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[5].Amount}@{objSetting.Results.Trades[5].Price}"
                                    : "",
                                Trade7 = (objSetting.Results.Trades.Count > 6)
                                    ? $" {objSetting.Results.Trades[6].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[6].Amount}@{objSetting.Results.Trades[6].Price}"
                                    : "",
                                Trade8 = (objSetting.Results.Trades.Count > 7)
                                    ? $" {objSetting.Results.Trades[7].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[7].Amount}@{objSetting.Results.Trades[7].Price}"
                                    : "",
                                Trade9 = (objSetting.Results.Trades.Count > 8)
                                    ? $" {objSetting.Results.Trades[8].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[8].Amount}@{objSetting.Results.Trades[8].Price}"
                                    : "",
                                Trade10 = (objSetting.Results.Trades.Count > 9)
                                    ? $" {objSetting.Results.Trades[9].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[9].Amount}@{objSetting.Results.Trades[9].Price}"
                                    : "",
                                Trade11 = (objSetting.Results.Trades.Count > 10)
                                    ? $" {objSetting.Results.Trades[10].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[10].Amount}@{objSetting.Results.Trades[10].Price}"
                                    : "",
                                Trade12 = (objSetting.Results.Trades.Count > 11)
                                    ? $" {objSetting.Results.Trades[11].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[11].Amount}@{objSetting.Results.Trades[11].Price}"
                                    : "",
                                Trade13 = (objSetting.Results.Trades.Count > 12)
                                    ? $" {objSetting.Results.Trades[12].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[12].Amount}@{objSetting.Results.Trades[12].Price}"
                                    : "",
                                Trade14 = (objSetting.Results.Trades.Count > 13)
                                    ? $" {objSetting.Results.Trades[13].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[13].Amount}@{objSetting.Results.Trades[13].Price}"
                                    : "",
                                Trade15 = (objSetting.Results.Trades.Count > 14)
                                    ? $" {objSetting.Results.Trades[14].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[14].Amount}@{objSetting.Results.Trades[14].Price}"
                                    : "",
                                Trade16 = (objSetting.Results.Trades.Count > 15)
                                    ? $" {objSetting.Results.Trades[15].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[15].Amount}@{objSetting.Results.Trades[15].Price}"
                                    : "",
                                Trade17 = (objSetting.Results.Trades.Count > 16)
                                    ? $" {objSetting.Results.Trades[16].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[16].Amount}@{objSetting.Results.Trades[16].Price}"
                                    : "",
                                Trade18 = (objSetting.Results.Trades.Count > 17)
                                    ? $" {objSetting.Results.Trades[17].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[17].Amount}@{objSetting.Results.Trades[17].Price}"
                                    : "",
                                Trade19 = (objSetting.Results.Trades.Count > 18)
                                    ? $" {objSetting.Results.Trades[18].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[18].Amount}@{objSetting.Results.Trades[18].Price}"
                                    : "",
                                Trade20 = (objSetting.Results.Trades.Count > 19)
                                    ? $" {objSetting.Results.Trades[19].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[19].Amount}@{objSetting.Results.Trades[19].Price}"
                                    : "",
                                Trade21 = (objSetting.Results.Trades.Count > 20)
                                    ? $" {objSetting.Results.Trades[20].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[20].Amount}@{objSetting.Results.Trades[20].Price}"
                                    : "",
                                Trade22 = (objSetting.Results.Trades.Count > 21)
                                    ? $" {objSetting.Results.Trades[21].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[21].Amount}@{objSetting.Results.Trades[21].Price}"
                                    : "",
                                Trade23 = (objSetting.Results.Trades.Count > 22)
                                    ? $" {objSetting.Results.Trades[22].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[22].Amount}@{objSetting.Results.Trades[22].Price}"
                                    : "",
                                Trade24 = (objSetting.Results.Trades.Count > 23)
                                    ? $" {objSetting.Results.Trades[23].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[23].Amount}@{objSetting.Results.Trades[23].Price}"
                                    : "",
                                Trade25 = (objSetting.Results.Trades.Count > 24)
                                    ? $" {objSetting.Results.Trades[24].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[24].Amount}@{objSetting.Results.Trades[24].Price}"
                                    : "",
                                Trade26 = (objSetting.Results.Trades.Count > 25)
                                    ? $" {objSetting.Results.Trades[25].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[25].Amount}@{objSetting.Results.Trades[25].Price}"
                                    : "",
                                Trade27 = (objSetting.Results.Trades.Count > 26)
                                    ? $" {objSetting.Results.Trades[26].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[26].Amount}@{objSetting.Results.Trades[26].Price}"
                                    : "",
                                Trade28 = (objSetting.Results.Trades.Count > 27)
                                    ? $" {objSetting.Results.Trades[27].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[27].Amount}@{objSetting.Results.Trades[27].Price}"
                                    : "",
                                Trade29 = (objSetting.Results.Trades.Count > 28)
                                    ? $" {objSetting.Results.Trades[28].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[28].Amount}@{objSetting.Results.Trades[28].Price}"
                                    : "",
                                Trade30 = (objSetting.Results.Trades.Count > 29)
                                    ? $" {objSetting.Results.Trades[29].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[29].Amount}@{objSetting.Results.Trades[29].Price}"
                                    : "",
                                Trade31 = (objSetting.Results.Trades.Count > 30)
                                    ? $" {objSetting.Results.Trades[30].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[30].Amount}@{objSetting.Results.Trades[30].Price}"
                                    : "",
                                Trade32 = (objSetting.Results.Trades.Count > 31)
                                    ? $" {objSetting.Results.Trades[31].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[31].Amount}@{objSetting.Results.Trades[31].Price}"
                                    : "",
                                Trade33 = (objSetting.Results.Trades.Count > 32)
                                    ? $" {objSetting.Results.Trades[32].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[32].Amount}@{objSetting.Results.Trades[32].Price}"
                                    : "",
                                Trade34 = (objSetting.Results.Trades.Count > 33)
                                    ? $" {objSetting.Results.Trades[33].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[33].Amount}@{objSetting.Results.Trades[33].Price}"
                                    : "",
                                Trade35 = (objSetting.Results.Trades.Count > 34)
                                    ? $" {objSetting.Results.Trades[34].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[34].Amount}@{objSetting.Results.Trades[34].Price}"
                                    : "",
                                Trade36 = (objSetting.Results.Trades.Count > 35)
                                    ? $" {objSetting.Results.Trades[35].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[35].Amount}@{objSetting.Results.Trades[35].Price}"
                                    : "",
                                Trade37 = (objSetting.Results.Trades.Count > 36)
                                    ? $" {objSetting.Results.Trades[36].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[36].Amount}@{objSetting.Results.Trades[36].Price}"
                                    : "",
                                Trade38 = (objSetting.Results.Trades.Count > 37)
                                    ? $" {objSetting.Results.Trades[37].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[37].Amount}@{objSetting.Results.Trades[37].Price}"
                                    : "",
                                Trade39 = (objSetting.Results.Trades.Count > 38)
                                    ? $" {objSetting.Results.Trades[38].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[38].Amount}@{objSetting.Results.Trades[38].Price}"
                                    : "",
                                Trade40 = (objSetting.Results.Trades.Count > 39)
                                    ? $" {objSetting.Results.Trades[39].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[39].Amount}@{objSetting.Results.Trades[39].Price}"
                                    : "",
                                Trade41 = (objSetting.Results.Trades.Count > 40)
                                    ? $" {objSetting.Results.Trades[40].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[40].Amount}@{objSetting.Results.Trades[40].Price}"
                                    : "",
                                Trade42 = (objSetting.Results.Trades.Count > 41)
                                    ? $" {objSetting.Results.Trades[41].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[41].Amount}@{objSetting.Results.Trades[41].Price}"
                                    : "",
                                Trade43 = (objSetting.Results.Trades.Count > 42)
                                    ? $" {objSetting.Results.Trades[42].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[42].Amount}@{objSetting.Results.Trades[42].Price}"
                                    : "",
                                Trade44 = (objSetting.Results.Trades.Count > 43)
                                    ? $" {objSetting.Results.Trades[43].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[43].Amount}@{objSetting.Results.Trades[43].Price}"
                                    : "",
                                Trade45 = (objSetting.Results.Trades.Count > 44)
                                    ? $" {objSetting.Results.Trades[44].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[44].Amount}@{objSetting.Results.Trades[44].Price}"
                                    : "",
                                Trade46 = (objSetting.Results.Trades.Count > 45)
                                    ? $" {objSetting.Results.Trades[45].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[45].Amount}@{objSetting.Results.Trades[45].Price}"
                                    : "",
                                Trade47 = (objSetting.Results.Trades.Count > 46)
                                    ? $" {objSetting.Results.Trades[46].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[46].Amount}@{objSetting.Results.Trades[46].Price}"
                                    : "",
                                Trade48 = (objSetting.Results.Trades.Count > 47)
                                    ? $" {objSetting.Results.Trades[47].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[47].Amount}@{objSetting.Results.Trades[47].Price}"
                                    : "",
                                Trade49 = (objSetting.Results.Trades.Count > 48)
                                    ? $" {objSetting.Results.Trades[48].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[48].Amount}@{objSetting.Results.Trades[48].Price}"
                                    : "",
                                Trade50 = (objSetting.Results.Trades.Count > 49)
                                    ? $" {objSetting.Results.Trades[49].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[49].Amount}@{objSetting.Results.Trades[49].Price}"
                                    : "",
                                Trade51 = (objSetting.Results.Trades.Count > 50)
                                    ? $" {objSetting.Results.Trades[50].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[50].Amount}@{objSetting.Results.Trades[50].Price}"
                                    : "",
                                Trade52 = (objSetting.Results.Trades.Count > 51)
                                    ? $" {objSetting.Results.Trades[51].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[51].Amount}@{objSetting.Results.Trades[51].Price}"
                                    : "",
                                Trade53 = (objSetting.Results.Trades.Count > 52)
                                    ? $" {objSetting.Results.Trades[52].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[52].Amount}@{objSetting.Results.Trades[52].Price}"
                                    : "",
                                Trade54 = (objSetting.Results.Trades.Count > 53)
                                    ? $" {objSetting.Results.Trades[53].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[53].Amount}@{objSetting.Results.Trades[53].Price}"
                                    : "",
                                Trade55 = (objSetting.Results.Trades.Count > 54)
                                    ? $" {objSetting.Results.Trades[54].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[54].Amount}@{objSetting.Results.Trades[54].Price}"
                                    : "",
                                Trade56 = (objSetting.Results.Trades.Count > 55)
                                    ? $" {objSetting.Results.Trades[55].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[55].Amount}@{objSetting.Results.Trades[55].Price}"
                                    : "",
                                Trade57 = (objSetting.Results.Trades.Count > 56)
                                    ? $" {objSetting.Results.Trades[56].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[56].Amount}@{objSetting.Results.Trades[56].Price}"
                                    : "",
                                Trade58 = (objSetting.Results.Trades.Count > 57)
                                    ? $" {objSetting.Results.Trades[57].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[57].Amount}@{objSetting.Results.Trades[57].Price}"
                                    : "",
                                Trade59 = (objSetting.Results.Trades.Count > 58)
                                    ? $" {objSetting.Results.Trades[58].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[58].Amount}@{objSetting.Results.Trades[58].Price}"
                                    : "",
                                Trade60 = (objSetting.Results.Trades.Count > 59)
                                    ? $" {objSetting.Results.Trades[59].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[59].Amount}@{objSetting.Results.Trades[59].Price}"
                                    : "",
                                Trade61 = (objSetting.Results.Trades.Count > 60)
                                    ? $" {objSetting.Results.Trades[60].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[60].Amount}@{objSetting.Results.Trades[60].Price}"
                                    : "",
                                Trade62 = (objSetting.Results.Trades.Count > 61)
                                    ? $" {objSetting.Results.Trades[61].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[61].Amount}@{objSetting.Results.Trades[61].Price}"
                                    : "",
                                Trade63 = (objSetting.Results.Trades.Count > 62)
                                    ? $" {objSetting.Results.Trades[62].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[62].Amount}@{objSetting.Results.Trades[62].Price}"
                                    : "",
                                Trade64 = (objSetting.Results.Trades.Count > 63)
                                    ? $" {objSetting.Results.Trades[63].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[63].Amount}@{objSetting.Results.Trades[63].Price}"
                                    : "",
                                Trade65 = (objSetting.Results.Trades.Count > 64)
                                    ? $" {objSetting.Results.Trades[64].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[64].Amount}@{objSetting.Results.Trades[64].Price}"
                                    : "",
                                Trade66 = (objSetting.Results.Trades.Count > 65)
                                    ? $" {objSetting.Results.Trades[65].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[65].Amount}@{objSetting.Results.Trades[65].Price}"
                                    : "",
                                Trade67 = (objSetting.Results.Trades.Count > 66)
                                    ? $" {objSetting.Results.Trades[66].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[66].Amount}@{objSetting.Results.Trades[66].Price}"
                                    : "",
                                Trade68 = (objSetting.Results.Trades.Count > 67)
                                    ? $" {objSetting.Results.Trades[67].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[67].Amount}@{objSetting.Results.Trades[67].Price}"
                                    : "",
                                Trade69 = (objSetting.Results.Trades.Count > 68)
                                    ? $" {objSetting.Results.Trades[68].Time.ToString(CultureInfo.InvariantCulture)}: {objSetting.Results.Trades[68].Amount}@{objSetting.Results.Trades[68].Price}"
                                    : "",
                            });


                            while (File.Exists(digestName) && IsFileLocked(new FileInfo(digestName)))
                            {
                                logger("Digest File already in use, close and press key...");
                                Console.ReadKey();
                            }

                            engine.WriteFile(digestName, digestRecords);
                            Thread.CurrentThread.CurrentCulture = previousCulture;

                            break;
                        case BackTestingMode.Boosting:
                            for (var idxResult = 0; idxResult < results.Count; idxResult++)
                            {
                                var currentBackTestingSettings = backTestingSettings[idxResult];
                                currentBackTestingSettings.Results = results[idxResult];
                                logger($"Result Boosted: ");
                                logger(
                                    $"{currentBackTestingSettings.Results.LastWallet.GetBalance(currentBackTestingSettings.Results.LastTicker).Total}");
                                //var basePath = currentBackTestingSettings.TrainingConfig.GetModelName();
                                //var currenFileName = Path.GetFileName(basePath);
                                //var fileName = basePath.Replace(currenFileName,  "Results-" +
                                //                                                  $"{Config.Simulation.StartDate:yyyy-M-dd-}-{Config.Simulation.EndDate:yyyy-M-dd-}-{currentBackTestingSettings.Results.LastWallet.GetBalance(currentBackTestingSettings.Results.LastTicker).Total:00000.00}Usd-{currentBackTestingSettings.Results.Trades.Count}-trades-{currenFileName}").Replace(Path.GetExtension(basePath),".json") ;
                                ////var toRemove =
                                ////    Path.GetFileName(currentBackTestingSettings.TrainingConfig.SampleConfig.GetSampleName());
                                ////toRemove = toRemove.Replace(Path.GetExtension(toRemove), "");
                                ////var shortFileName = fileName.Replace(toRemove, "");
                                //File.WriteAllText(fileName, JsonConvert.SerializeObject(currentBackTestingSettings.Results, Formatting.Indented));
                            }

                            break;
                        default:
                            throw new ArgumentOutOfRangeException();
                    }
                }


                switch (Config.Mode)
                {
                    case BackTestingMode.SVMModels:


                        var backTestingResults = new Dictionary<BackTestingSettings, BacktestResult>();
                        foreach (var objSetting in backTestingSettings)
                        {
                            var modelName = Path.GetFileName(objSetting.TrainingConfig.GetModelName());
                            var backTestRecord = digestRecords.FirstOrDefault(x => x.ModelName == modelName);
                            if (backTestRecord != null)
                            {
                                backTestingResults[objSetting] = backTestRecord;
                            }
                        }


                        var backTestingScoreFunction = new Func<BackTestingSettings, decimal>(objSelect =>
                            backTestingResults.ContainsKey(objSelect)
                                ? backTestingResults[objSelect].Result
                                : decimal.MinValue);

                        backTestingSettings = backTestingSettings.OrderBy(backTestingScoreFunction).Reverse().ToList();

                        foreach (var backTestingResult in backTestingResults)
                        {
                            var modelName = backTestingResult.Key.TrainingConfig.GetModelName();
                            if (!multiResults.TryGetValue(modelName, out var modelResult))
                            {
                                 modelResult = new Dictionary<int, BacktestResult>();
                                 multiResults[modelName] = modelResult;
                            }
                            modelResult.Add(simulationIndex, backTestingResult.Value);
                        }


                        if (Config.UpdateAllFile)
                        {
                            (new FileInfo(backTestingName)).Directory?.Create();
                            File.WriteAllText(backTestingName,
                                JsonConvert.SerializeObject(backTestingSettings, Formatting.Indented));
                        }


                        if (Config.UpdateBestFile)
                        {
                            if (bestBackTesting.Count > 0)
                            {
                                backTestingSettings =
                                    backTestingSettings.Union(bestBackTesting, new CompareBackTestings())
                                        .OrderBy(objSelect => objSelect.Results != null ? -objSelect.GetResult() : 0)
                                        .ToList();
                            }

                            backTestingSettings = backTestingSettings.Take(Config.BestNb).ToList();
                            var bestsName = Config.GetBackTestingBestFileName(configSimulation);
                            File.WriteAllText(bestsName,
                                JsonConvert.SerializeObject(backTestingSettings, Formatting.Indented));
                        }

                        break;
                    case BackTestingMode.Boosting:

                        break;
                    default:
                        throw new ArgumentOutOfRangeException();
                }
            }


            var finalResult = new List<BacktestResult>();
            foreach (var multiResult in multiResults)
            {
                var simultationRanks = new List<double>();
                foreach (var simulationResult in multiResult.Value)
                {
                    var simulationIndex = simulationResult.Key;
                    var simulationRank = multiResults.Count(otherModelResults =>
                        otherModelResults.Value.TryGetValue(simulationIndex, out var otherResult) &&
                        otherResult.Result > simulationResult.Value.Result);
                    var simulationCount = multiResults.Count(otherModelResults =>
                        otherModelResults.Value.TryGetValue(simulationIndex, out var otherResult));
                    simultationRanks.Add(simulationRank/(double) simulationCount);
                }

                var meanRank = simultationRanks.Sum() / simultationRanks.Count;
            }



        }

        public List<BackTestingSettings> LoadModels(Action<string> logger, FileBasedSimulation configSimulation, out List<BackTestingSettings> bestBackTesting)
        {
            logger("Loading Models");
            bestBackTesting = new List<BackTestingSettings>();
            var backTestingSettings = new List<BackTestingSettings>();
            var backTestingName = Config.GetBackTestingFileName(configSimulation);
            var bestsName = Config.GetBackTestingBestFileName(configSimulation);
            if (Config.LoadBest && File.Exists(bestsName))
            {
                logger("Loading best Models file");
                bestBackTesting = JsonConvert.DeserializeObject<List<BackTestingSettings>>(File.ReadAllText(bestsName));
                backTestingSettings = bestBackTesting;
                logger($"Loaded Models, Total count: {backTestingSettings.Count}");
            }
            if (Config.LoadAll && File.Exists(backTestingName))
            {
                //var loadNb = Config.MaxNb - backTestingSettings.Count;
                logger("Loading All Models file");
                var allBackTestings = JsonConvert.DeserializeObject<List<BackTestingSettings>>(File.ReadAllText(backTestingName)).Where(objBacktestSettings => objBacktestSettings.GetModelStrategy(logger) != null).OrderBy(objSelect => objSelect.Results != null ? -objSelect.GetResult() : 0);//.Take(loadNb);
                backTestingSettings = backTestingSettings.Union(allBackTestings, new CompareBackTestings()).OrderBy(objSelect => objSelect.Results != null ? -objSelect.GetResult() : 0).ToList();
                logger($"Loaded Models, Total count: {backTestingSettings.Count}");

            }
            if (Config.CreateAll)
            {
                //var loadNb = Config.MaxNb - backTestingSettings.Count;
                logger("Building models");
                var allBackTestings = Config.GetBackTestingSettings(logger).Where(objBacktestSettings => objBacktestSettings.GetModelStrategy(logger) != null).OrderBy(objSelect => objSelect.TestError > 0 ? (decimal)objSelect.TestError : decimal.MaxValue);
                backTestingSettings = backTestingSettings.Union(allBackTestings, new CompareBackTestings()).ToList();
                logger($"Built Models, Total count: {backTestingSettings.Count}");
            }


            if (Config.AddCalibratedComplexities)
            {
                logger($"Adding calibrated complexities");
                foreach (var backTestingSetting in backTestingSettings.ToArray())
                {
                    var calibratedConfig = backTestingSetting.TrainingConfig.DeepClone();
                    calibratedConfig.ModelsConfig.SvmModelConfig.Complexity = -1;
                    logger($"Adding new calibrated Model Backtest Settings: {calibratedConfig.GetModelName()}");
                    var toAdd = new BackTestingSettings()
                    {
                        TrainingConfig = calibratedConfig,
                    };
                    if (toAdd.GetModelStrategy(logger) != null)
                    {
                        backTestingSettings.Add(toAdd);
                    }

                }

            }

            logger($"Preparing Setups, Total Model count: {backTestingSettings.Count}");


            if (backTestingSettings.Count >= Config.MaxNb)
            {
                backTestingSettings = backTestingSettings.Take(Config.MaxNb).ToList();
                logger($"Models filtered, count: {backTestingSettings.Count}");
            }

            return backTestingSettings;
        }


        //private int CompareBackTestings(BackTestingSettings x, BackTestingSettings y) => String.Compare(x.TrainingConfig.GetModelName(), y.TrainingConfig.GetModelName(), StringComparison.Ordinal);

        public TradingHistory RunSimulation(SimulationInfo confiSimulation, ITradingModel model, TradingSampleConfig samplConfig, TradingTrainingConfig trainingConfig, Action<string> logger)
        {

            logger("Configuring Simulation");



            //var objStrategy = new ResourceBalancingStrategy(){AskReserveRate = 0, BidReserveRate = 0};
            //



            var objTrades = TradeHelper.Load(samplConfig.Filename, confiSimulation.StartDate, confiSimulation.EndDate, logger, true);
            logger("Loaded original trades");


            var tradeHistory = objTrades.Select(objTrade =>
                 new OrderTrade() { Amount = objTrade.Amount, Price = objTrade.Price, UnixTime = objTrade.UnixTime }).ToList();


            //this.Simulation.StartDate = tradeHistory[0].Time;
            //this.Simulation.EndDate = tradeHistory.Last().Time;

            var objExchange = new ExchangeInfo() { AskCommission = 0.2M, BidCommission = 0.2M, MinOrderAmount = 0, AmountDecil = 4 };
            var objHodlWallet = new Wallet()
            {
                PrimarySymbol = "BTC",
                SecondarySymbol = "USD",
                PrimaryBalance = 1M
            };
            var objHodlStrategy = new HodlStrategy { AskReserveRate = 0, BidReserveRate = 0 };

            logger("starting Hodl simulation");
            var hodlResult = confiSimulation.RunSimulation(objHodlWallet, objHodlStrategy, objExchange, tradeHistory);
            logger($"Results: {hodlResult.LastWallet.GetBalance(hodlResult.LastTicker).Total}");

            var objStrategy = new ModelStrategy() { Model = model, TrainingConfig = trainingConfig, Logger = logger, AskReserveRate = 0, BidReserveRate = 0 };
            var objWallet = new Wallet()
            {
                PrimarySymbol = "BTC",
                SecondarySymbol = "USD",
                PrimaryBalance = 1M
            };
            logger("starting Machine learning simulation");
            var toReturn = confiSimulation.RunSimulation(objWallet, objStrategy, objExchange, tradeHistory);
            //logger($"Results: {hodlResult.LastWallet.GetBalance(hodlResult.LastTicker).Total}");
            return toReturn;
        }

        public void RunSimple(Action<string> logger, SimulationInfo obSimulationInfo)
        {


            logger("Entering Backtesting");
            logger("Loading trades");

            var tradeFileName = Config.TrainingConfig.DataConfig.SampleConfig.Filename;
            //var tradeFileName = Config.TrainingConfig.DataConfig.SampleConfig.Filename.Replace("bitstampUSD", "krakenEUR");



            var objTrades = TradeHelper.Load(tradeFileName, obSimulationInfo.StartDate, obSimulationInfo.EndDate, logger, true);
            logger("Loaded original trades");

            logger("building history");
            var tradeHistory = objTrades.Select(objTrade =>
                new OrderTrade() { Amount = objTrade.Amount, Price = objTrade.Price, UnixTime = objTrade.UnixTime }).ToList();
            logger("built historic trades");


            var objExchange = new ExchangeInfo() { AskCommission = 0.2M, BidCommission = 0.2M, MinOrderAmount = 0, AmountDecil = 4 };
            var initialWallet = new Wallet()
            {
                PrimarySymbol = "BTC",
                SecondarySymbol = "USD",
                PrimaryBalance = 1M
            };

            var objWallet = initialWallet.DeepClone();

            logger("starting Hodl simulation");

            var objHodlStrategy = new HodlStrategy { AskReserveRate = 0, BidReserveRate = 0 };


            var hodlResult = obSimulationInfo.RunSimulation(objWallet, objHodlStrategy, objExchange, tradeHistory);
            logger($"Results: {hodlResult.LastWallet.GetBalance(hodlResult.LastTicker).Total}");



            for (int stopRate = 1; stopRate < 10; stopRate++)
            {
                for (int refactoryPeriod = 0; refactoryPeriod < 5; refactoryPeriod++)
                {
                    var newStopRate = 0.05m+(0.03m * stopRate);
                    var newRefactoryPeriod = 5 * TimeSpan.FromDays(refactoryPeriod);
                    logger($"starting Stop simulation with stop rate {newStopRate}, and refactory period {newRefactoryPeriod}");
                    objWallet = initialWallet.DeepClone();
                    var simpleStopStrat = new SimpleStopStrategy() { Logger = logger, StopRate = newStopRate, RefactoryPeriod = newRefactoryPeriod};
                    var simpleResults = obSimulationInfo.RunSimulation(objWallet, simpleStopStrat, objExchange, tradeHistory);
                    logger($"Results: {simpleResults.LastWallet.GetBalance(hodlResult.LastTicker).Total}");
                }
                
            }


        }




        protected virtual bool IsFileLocked(FileInfo file)
        {
            FileStream stream = null;

            try
            {
                stream = file.Open(FileMode.Open, FileAccess.Read, FileShare.None);
            }
            catch (IOException)
            {
                //the file is unavailable because it is:
                //still being written to
                //or being processed by another thread
                //or does not exist (has already been processed)
                return true;
            }
            finally
            {
                if (stream != null)
                    stream.Close();
            }

            //file is not locked
            return false;
        }






    }
}
