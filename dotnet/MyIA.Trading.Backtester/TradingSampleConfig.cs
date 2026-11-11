using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using FileHelpers;
using FileHelpers.Events;
using MyIA.Trading.Converter;
using Newtonsoft.Json;

namespace MyIA.Trading.Backtester
{
    public enum SamplingMode
    {
        // Slices are taken at intervals reducing exponentially using TimeCoef from LeftWindow to MinSlice
        Exponential = 0,
        // Slices are taken at constants intervals using TimeCoef from LeftWindow
        Constant = 1,
    }


    [DelimitedRecord(",")]
    public class TradingSampleConfig
    {
        public DateTime StartDate { get; set; } = new DateTime(2013, 4, 1);

        public DateTime EndDate { get; set; } = new DateTime(2020, 5, 1);

        //public string Filename { get; set; } = Path.Combine(Environment.CurrentDirectory, "data\\bitstampUSD.csv");

        public string Filename { get; set; } = @"A:\TradingTests\bitstampUSD.bin.7z";


        public string GetRootFolder()
        {
            return Filename.Replace(Path.GetExtension(Filename), $@"\{NbSamples}-left-{LeftWindow.TotalHours}h-{StartDate:yyyy-M-dd}-{EndDate:yyyy-M-dd}\");
        }

        public bool SaveSamples { get; set; } = true;

        public int NbSamples { get; set; } = 400000;

        public bool UseFastRandom { get; set; } = true;

        public TimeSpan LeftWindow { get; set; } = TimeSpan.FromDays(30);

        public SamplingMode SamplingMode { get; set; } = SamplingMode.Constant;

        public TimeSpan ConstantSliceSpan { get; set; } = TimeSpan.FromDays(1);

        public Decimal TimeCoef { get; set; } = 0.7M;

        public TimeSpan MinSlice { get; set; } = TimeSpan.FromMinutes(1);

        public List<TimeSpan> PredictionTimes => new List<TimeSpan>(new[]{
            //TimeSpan.FromMinutes(5),
            //TimeSpan.FromMinutes(10),
            //TimeSpan.FromMinutes(20),
            //TimeSpan.FromMinutes(30),
            TimeSpan.FromHours(1),
            TimeSpan.FromHours(6),
            TimeSpan.FromHours(12),
            TimeSpan.FromDays(1),
            TimeSpan.FromDays(2),
            TimeSpan.FromDays(3),
            TimeSpan.FromDays(5),
            TimeSpan.FromDays(10),
            TimeSpan.FromDays(20),
            TimeSpan.FromDays(30)
        });

        public List<decimal> PredictionPeaks => new List<decimal>()
        {
            5,
            10,
            20
        };


        public string GetSamplesFileName()
        {
            return $"{GetRootFolder()}Samples-Mode{SamplingMode}-Coef{TimeCoef.ToString(CultureInfo.InvariantCulture)}-Days{LeftWindow.Days}.bin.lz4";
        }

        private static readonly Dictionary<string, List<TradingSample>> _samplesByConfig = new Dictionary<string, List<TradingSample>>();
        public List<TradingSample> Load(Action<string> logger)
        {
            //var strKey = JsonConvert.SerializeObject(this);
            var sampleFileName = this.GetSamplesFileName();
            logger($"Loading samples");
            if (!_samplesByConfig.TryGetValue(sampleFileName, out var toReturn))
            {


                if (SaveSamples && File.Exists(sampleFileName))
                {
                    logger($"Loading from file {sampleFileName}");
                    toReturn = TradeConverter.LoadFile<List<TradingSample>>(logger, sampleFileName,
                        TradeHelper.DeSerializationConfig);
                    //using (Stream stream = File.OpenRead(sampleFileName))
                    //{
                    //    using Stream decompressed = stream.DecompressSingleFile( out _,
                    //        TradeHelper.DeSerializationConfig.Compression, InputArchiveFormat.SevenZip);
                    //    toReturn = decompressed.DeserializeApexFormatter<List<TradingSample>>(new[] { typeof(Trade), typeof(TradingSample) });
                    //}

                    logger($"Loaded {sampleFileName}");
                }
                else
                {
                    logger($"Creating {sampleFileName}");

                    var trades = TradeHelper.Load(this.Filename, this.StartDate - this.LeftWindow, this.EndDate + PredictionTimes.Last(), logger, false);
                    logger($"Creating samples");
                    toReturn = CreateSamples(trades);
                    logger($"Created samples");
                    if (SaveSamples)
                    {
                        logger($"Serializing samples");
                        TradeConverter.SaveFile(toReturn, sampleFileName, "", logger, TradeHelper.SerializationConfig);
                        logger($"Created {sampleFileName}");
                    }

                }

                _samplesByConfig[sampleFileName] = toReturn;
            }

            return toReturn;
        }


        public List<TradingSample> CreateSamples(List<Trade> trades)
        {
            var firstIdx = trades.FindIndex(t => t.Time > trades.First().Time + this.LeftWindow);
            var lastIdx = trades.FindLastIndex(t => t.Time < trades.Last().Time - PredictionTimes.Last());
            var idxSpan = lastIdx - firstIdx;
            var slice = idxSpan / this.NbSamples;
            return CreateSamplesBySearch(trades, firstIdx, slice);
        }

        private Random _Random = new Random();

        private FastRandom _FastRandom = new FastRandom(new Random().Next());



        public List<TradingSample> CreateSamplesBySearch(List<Trade> trades, int firstIdx, int slice)
        {

            var toReturn = new List<TradingSample>();

            var peaks = PredictionPeaks
                .Select(threshold => new KeyValuePair<decimal, List<KeyValuePair<int, Trade>>>(threshold, GetPeaks(trades, threshold)))
                .ToDictionary(x => x.Key, x => x.Value);
            var currentPeakIndices = PredictionPeaks.ToDictionary(x => x, x => 0);
            for (int i = 0; i < this.NbSamples; i++)
            {
                var randomIndexOffset = UseFastRandom ? _FastRandom.Next(0, slice) : _Random.Next(0, slice);
                var startIdx = firstIdx + (i * slice) + randomIndexOffset;

                var sample = Create(trades, startIdx, peaks, ref currentPeakIndices);
                if (sample != null)
                {
                    toReturn.Add(sample);
                }
            }

            return toReturn;
        }


        /// <summary>
        /// Returns a list of key-value pairs representing the peaks in a list of trades based on a given variation threshold.
        /// </summary>
        /// <param name="trades">The list of trades to analyze.</param>
        /// <param name="threshold">The threshold value to determine if a trade is a peak.</param>
        /// <returns>A list of key-value pairs where the key represents the index of the peak trade and the value represents the peak trade itself.</returns>
        public List<KeyValuePair<int, Trade>> GetPeaks(List<Trade> trades, decimal threshold)
        {
            var percentThresold = threshold / 100;
            var toReturn = new List<KeyValuePair<int, Trade>>();
            var currentMaxTrade = new KeyValuePair<int, Trade>(0, trades[0]);
            var currentMinTrade = new KeyValuePair<int, Trade>(0, trades[0]);
            for (int currentTradeIndex = 0; currentTradeIndex < trades.Count; currentTradeIndex++)
            {
                var currentTrade = new KeyValuePair<int, Trade>(currentTradeIndex, trades[currentTradeIndex]);
                if (currentMinTrade.Key > -1)
                {

                    if (currentTrade.Value.Price < currentMinTrade.Value.Price)
                    {
                        currentMinTrade = currentTrade;
                    }
                    if ((currentTrade.Value.Price - currentMinTrade.Value.Price) / currentMinTrade.Value.Price > percentThresold)
                    {

                        toReturn.Add(currentMinTrade);
                        currentMinTrade = new KeyValuePair<int, Trade>(-1, null);
                        currentMaxTrade = currentTrade;
                    }
                }
                if (currentMaxTrade.Key > -1)
                {
                    if (currentTrade.Value.Price > currentMaxTrade.Value.Price)
                    {
                        currentMaxTrade = currentTrade;
                    }
                    if ((currentMaxTrade.Value.Price - currentTrade.Value.Price) / currentMaxTrade.Value.Price > percentThresold)
                    {
                        toReturn.Add(currentMaxTrade);
                        currentMaxTrade = new KeyValuePair<int, Trade>(-1, null);
                        currentMinTrade = currentTrade;
                    }
                }
            }

            return toReturn;

        }

        public TradingSample Create(List<Trade> trades, int idx, Dictionary<decimal, List<KeyValuePair<int, Trade>>> peaks, ref Dictionary<decimal, int> currentPeakIndices)
        {
            var toReturn = CreateInput(trades, idx);
            if (toReturn == null)
            {
                return null;
            }
            toReturn = AddOutputs(toReturn, trades, idx);

            toReturn = AddPeaks(toReturn, trades, idx, peaks, ref currentPeakIndices);

            return toReturn;
        }


        public TradingSample CreateInput(List<Trade> trades, int idx)
        {
            var toReturn = new TradingSample();
            toReturn.TargetTrade = trades[idx];
            var targetTime = toReturn.TargetTrade.Time;
            TimeSpan currentSlice = this.LeftWindow;
            DateTime currentTime;


            currentTime = targetTime.Subtract(currentSlice);
            while (currentSlice > this.MinSlice)
            {
                currentTime = targetTime.Subtract(currentSlice);
                var newInput = SearchTrade(trades, idx, currentTime, false);
                if (newInput == null)
                {
                    return null;
                }
                toReturn.Inputs.Add(newInput);

                switch (SamplingMode)
                {
                    case SamplingMode.Exponential:
                        currentSlice = TimeSpan.FromTicks(Convert.ToInt64(currentSlice.Ticks * this.TimeCoef));
                        break;
                    case SamplingMode.Constant:
                        currentSlice = currentSlice - ConstantSliceSpan;
                        break;
                    default:
                        throw new ArgumentOutOfRangeException();
                }

            }

            return toReturn;
        }




        public TradingSample AddOutputs(TradingSample sample, List<Trade> trades, int idx)
        {
            var targetTime = sample.TargetTrade.Time;
            foreach (var predictionTime in this.PredictionTimes)
            {
                var currentTime = targetTime.Add(predictionTime);
                var toAdd = TradingSampleConfig.SearchTrade(trades, idx, currentTime, true);
                if (toAdd == null)
                {
                    return null;
                }
                sample.Outputs.Add(predictionTime, toAdd);
            }

            return sample;
        }

        /// <summary>
        /// Adds to the current sample the peaks based on variation threshold and threshold peaks based on variation threshold from target trade following the target trade.
        /// </summary>
        public TradingSample AddPeaks(TradingSample sample, List<Trade> trades, int idx, Dictionary<decimal, List<KeyValuePair<int, Trade>>> peaks, ref Dictionary<decimal, int> currentPeakIndices)
        {

            var targetTime = sample.TargetTrade.Time;
            foreach (var threshold in peaks.Keys)
            {
                var percentThresold = threshold / 100;
                var currentPeaks = peaks[threshold];
                var currentPeakIndex = currentPeakIndices[threshold];
                do
                {
                    var currentPeak = currentPeaks[currentPeakIndex];
                    if (currentPeak.Key > idx)
                    {
                        currentPeakIndices[threshold] = currentPeakIndex;
                        sample.Peaks[threshold] = currentPeak.Value;
                        var currentThresholdPeakIndex = currentPeakIndex;
                        do
                        {
                            var currentThresholdPeak = currentPeaks[currentThresholdPeakIndex];
                            if (Math.Abs(currentThresholdPeak.Value.Price - trades[idx].Price) / trades[idx].Price > percentThresold)
                            {
                                sample.ThresholdPeaks[threshold] = currentThresholdPeak.Value;
                                break;
                            }
                            currentThresholdPeakIndex += 1;
                        } while (currentThresholdPeakIndex < currentPeaks.Count);

                        if (!sample.ThresholdPeaks.ContainsKey(threshold))
                        {
                            return null;
                        }
                        break;
                    }
                    currentPeakIndex += 1;
                } while (currentPeakIndex < currentPeaks.Count);
                if (!sample.Peaks.ContainsKey(threshold))
                {
                    return null;
                }
            }

            return sample;
        }




        public static Trade SearchTrade(List<Trade> trades, int idx, DateTime targetTime, bool searchup)
        {
            int closestIndex;
            if (searchup)
            {
                closestIndex = trades.BinarySearch(idx, trades.Count - idx, new Trade { UnixTime = (int)targetTime.ConvertToUnixTimestamp() }, Comparer<Trade>.Create(new Comparison<Trade>(CompareTrades)));
            }
            else
            {
                closestIndex = trades.BinarySearch(new Trade { UnixTime = (int)targetTime.ConvertToUnixTimestamp() }, Comparer<Trade>.Create(new Comparison<Trade>(CompareTrades)));
            }

            if (closestIndex < 0)
            {
                var backupClosestIndex = ~closestIndex;
                if (searchup)
                {
                    if (backupClosestIndex > 0 && backupClosestIndex < trades.Count)
                    {
                        return trades[backupClosestIndex];
                    }
                }
                else
                {
                    if (backupClosestIndex > 0 && backupClosestIndex < trades.Count)
                    {
                        return trades[backupClosestIndex];
                    }
                }
                return null;
            }

            return trades[closestIndex];


        }


        public TradingSample CreateInput(List<OrderTrade> trades, int idx)
        {
            var toReturn = new TradingSample();
            toReturn.TargetTrade = new Trade()
            {
                Amount = trades[idx].Amount,
                Price = trades[idx].Price,
                UnixTime = (int)trades[idx].UnixTime
            };
            var targetTime = toReturn.TargetTrade.Time;
            TimeSpan currentSlice = this.LeftWindow;
            DateTime currentTime = targetTime.Subtract(currentSlice);
            while (currentSlice > this.MinSlice)
            {
                currentTime = targetTime.Subtract(currentSlice);
                var newInput = SearchTrade(trades, idx, currentTime, false);
                if (newInput == null)
                {
                    return null;
                }
                toReturn.Inputs.Add(new Trade()
                {
                    Amount = newInput.Amount,
                    Price = newInput.Price,
                    UnixTime = (int)newInput.UnixTime
                });
                switch (SamplingMode)
                {
                    case SamplingMode.Exponential:
                        currentSlice = TimeSpan.FromTicks(Convert.ToInt64(currentSlice.Ticks * this.TimeCoef));
                        break;
                    case SamplingMode.Constant:
                        currentSlice = currentSlice - ConstantSliceSpan;
                        break;
                    default:
                        throw new ArgumentOutOfRangeException();
                }


            }

            return toReturn;
        }

        public static int CompareOrderTrades(OrderTrade x, OrderTrade y)
        {
            return x.Time.CompareTo(y.Time);
        }

        public static int CompareTrades(Trade x, Trade y)
        {
            return x.UnixTime.CompareTo(y.UnixTime);
        }

        public static OrderTrade SearchTrade(List<OrderTrade> trades, int idx, DateTime targetTime, bool searchup)
        {
            //var utcTargetTime = Aricie.Common.ConvertToUnixTimestamp(targetTime);// ((DateTimeOffset) targetTime.ToUniversalTime()).ToUnixTimeSeconds();

            int closestIndex;
            if (searchup)
            {
                closestIndex = trades.BinarySearch(idx, trades.Count - idx, new MyIA.Trading.Backtester.OrderTrade { Time = targetTime }, Comparer<MyIA.Trading.Backtester.OrderTrade>.Create(new Comparison<MyIA.Trading.Backtester.OrderTrade>(CompareOrderTrades)));
            }
            else
            {
                closestIndex = trades.BinarySearch(0, idx, new MyIA.Trading.Backtester.OrderTrade { Time = targetTime }, Comparer<MyIA.Trading.Backtester.OrderTrade>.Create(new Comparison<MyIA.Trading.Backtester.OrderTrade>(CompareOrderTrades)));
            }

            if (closestIndex < 0)
            {
                var backupClosestIndex = ~closestIndex;
                if (searchup)
                {
                    if (backupClosestIndex > 0 && backupClosestIndex < trades.Count)
                    {
                        return trades[backupClosestIndex];
                    }
                }
                else
                {
                    if (backupClosestIndex > 0 && backupClosestIndex < trades.Count)
                    {
                        return trades[backupClosestIndex];
                    }
                }
                return null;
            }

            return trades[closestIndex];

        }

    }


}
