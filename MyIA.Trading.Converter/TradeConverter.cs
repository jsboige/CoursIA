using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using SevenZip;
using SevenZipExtractor;
using Utf8Json;
using Utf8Json.Formatters;

namespace MyIA.Trading.Converter
{
    public class TradeConverter
    {

        public string InputFile { get; set; } = @"A:\TradingTests\bitstampUSD.bin.7z";

        //Pour Daily
        //public string OutputFile { get; set; } = @"..\..\..\..\Data\crypto\bitstamp\daily\btceur_trade.zip";


        //Pour Hour
        public string OutputFile { get; set; } = @"..\..\..\..\Data\crypto\bitstamp\hour\btcusd_trade.zip";

        //Pour Minutes
        //public string OutputFile { get; set; } = @"..\..\..\..\Data\crypto\bitstamp\minute\btcusd\trade.zip";

        //Pour Secondes
        //public string OutputFile { get; set; } = @"..\..\..\..\Data\crypto\bitstamp\seconde\btcusd\trade.zip";

        public DateTime StartDate { get; set; } = new DateTime(2010, 1, 1);

        public DateTime EndDate { get; set; } = new DateTime(2025, 12, 31);

        public double SkipRatio { get; set; } = 0;

        public TradingDataType TargetTradingDataType { get; set; } = TradingDataType.Tickbars;

        //Pour Daily
        //public TimeSpan TickbarsPeriod { get; set; } = TimeSpan.FromDays(1);

        //Pour Hour
        public TimeSpan TickbarsPeriod { get; set; } = TimeSpan.FromHours(1);

        //Pour Minutes
        //public TimeSpan TickbarsPeriod { get; set; } = TimeSpan.FromMinutes(1);

        //Pour Secondes
        //public TimeSpan TickbarsPeriod { get; set; } = TimeSpan.FromSeconds(1);

        //Pour Daily ou hour
        public string DynamicFilePrefix { get; set; }

        //Pour Minutes
        //Pour Secondes
        //public string DynamicFilePrefix { get; set; } = "{tickBar.DateTime.ToString(\"yyyyMMdd\")}_";



        public bool RandomPeriodStart { get; set; } = false;

        public int ConversionsNb { get; set; } = 1;

        public string OutputPrefix { get; set; } = "{0}_";

        public SerializationConfig DeSerializationConfig { get; set; } = new SerializationConfig()
        {
            Culture = "en-US",
            Binary = BinarySerializationType.Apex,
            Csv = CsvSerializationType.TinyCsv,
            Json = JsonSerializationType.Utf8,
            Xml = XmlSerializationType.XmlSerializer,
            Compression = new CompressionConfig(){ Library = CompressionLibrary.SevenZipExtractor, Level = CompressionLevel.Normal }
            
        };

        public SerializationConfig SerializationConfig { get; set; } = new SerializationConfig()
        {
            Culture = "en-US",
            Binary = BinarySerializationType.Apex,
            Csv = CsvSerializationType.FlatFiles,
            Json = JsonSerializationType.Utf8,
            Xml = XmlSerializationType.XmlSerializer,
            Compression = new CompressionConfig() { Library = CompressionLibrary.SevenZipSharp, Level = CompressionLevel.Fast },
            IncludeHeader = false,
            //Pour Daily
            DateTimeFormat = "yyyyMMdd HH:mm",

            //Pour Daily
            DateAsMillisecondsFromEpoch = false

            //Pour Minutes
            //Pour Secondes
            //DateAsMillisecondsFromEpoch = true
        };

        //public async Task Process(Action<string> logger)
        public void Process(Action<string> logger)
        {
            var trades = LoadTrades(logger, InputFile, DeSerializationConfig);
            while (trades.Last() == null)
            {
                trades = trades.SkipLast(1).ToList();
            }
            logger($"Deserialized {trades.Count} trades from {trades.First().Time} To {trades.Last().Time}");
            trades = trades.GetRange(StartDate, EndDate);
            logger($"Filtered for period: {trades.Count} trades from {StartDate} To {EndDate}");

            if (this.TargetTradingDataType == TradingDataType.Tickbars)
            {
                var tickbars = trades.ToTickbars(this.TickbarsPeriod, this.RandomPeriodStart);
                logger($"converted  {trades.Count} trades to {tickbars.Count} tickbars");
                if (!string.IsNullOrEmpty(this.DynamicFilePrefix))
                {
                    var interpolationDictionary = new Dictionary<string, object>();
                    interpolationDictionary["tickBar"] = tickbars[0];
                    var currentPrefix = this.DynamicFilePrefix.Interpolate(interpolationDictionary);
                    var currentFileTickBars = new List<Tickbar>();


                    for (int i = 0; i < tickbars.Count; i++)
                    {
                        interpolationDictionary["tickBar"] = tickbars[i];
                        var newPrefix = this.DynamicFilePrefix.Interpolate(interpolationDictionary);
                        if (newPrefix != currentPrefix)
                        {
                            SaveTradingData<Tickbar>(currentFileTickBars, OutputFile, currentPrefix, logger, SerializationConfig);
                            currentPrefix = newPrefix;
                            currentFileTickBars.Clear();
                        }
                        currentFileTickBars.Add(tickbars[i]);
                        if (i == tickbars.Count - 1)
                        {
                            SaveTradingData<Tickbar>(currentFileTickBars, OutputFile, currentPrefix, logger, SerializationConfig);
                        }
                    }
                }
                else
                {
                    SaveTradingData<Tickbar>(tickbars, OutputFile, "", logger, SerializationConfig);
                }
            }
            else
            {
                for (int i = 0; i < ConversionsNb; i++)
                {
                    string prefix = "";
                    if (i > 0)
                    {
                        prefix = string.Format(OutputPrefix, i);
                    }
                    var filteredTrades = trades.Skip(SkipRatio);
                    logger($"Skipped ratio {SkipRatio}: {filteredTrades.Count} trades");
                    SaveTrades(filteredTrades, prefix, logger, SerializationConfig);

                }
            }

           

        }



        //public async Task<List<Trade>> LoadTrades(Action<string> logger, SerializationConfig sConfig)
        public static List<Trade> LoadTrades(Action<string> logger, string strInputFile, SerializationConfig sConfig)
        {
            var origCulture = Thread.CurrentThread.CurrentCulture;
            Thread.CurrentThread.CurrentCulture = new CultureInfo(sConfig.Culture);
            List<Trade> toReturn;
            var strExtension = strInputFile.GetRawExtensionUpper();
            using var objFileStream = File.OpenRead(strInputFile);
            switch (strExtension)
            {
                default:
                    Stream objEntryStream = objFileStream;
                    bool isCompressed = strExtension.IsCompressedExtension(out var compressionFormat);
                    if (isCompressed)
                    {
                        objEntryStream = objEntryStream.DecompressSingleFile(out var decompressedFileName, sConfig.Compression, compressionFormat);
                        logger($"Decompressed {strInputFile} from {compressionFormat} format using {sConfig.Compression.Library}");
                        strExtension = decompressedFileName.GetRawExtensionUpper();
                    }
                    switch (strExtension)
                    {
                        case "BIN":
                            {
                                //var toReturn = await objFileStream.DeserializeBinaryList<Trade>(sConfig.Binary);
                                toReturn = objEntryStream.DeserializeBinaryList<Trade>(sConfig.Binary);
                                logger($"Deserialized {toReturn.Count} trades binary using {sConfig.Binary}");
                                break;
                            }
                        case "CSV":
                            {
                                toReturn = objEntryStream.LoadCsvTrades(sConfig.Csv);
                                logger($"Deserialized {toReturn.Count} trades from csv using {sConfig.Csv}");
                                break;
                            }
                        case "JSON":
                        case "JS":
                            {
                                toReturn = objEntryStream.LoadJsonTrades(sConfig.Json);
                                logger($"Deserialized {toReturn.Count} trades from json using {sConfig.Csv}");
                                break;
                            }

                        default:
                            throw new NotSupportedException($"File extension {strExtension} unsupported");
                    }
                    break;
            }

            Thread.CurrentThread.CurrentCulture = origCulture;
            return toReturn;
        }

        public void SaveTrades(List<Trade> trades, string filePrefix, Action<string> logger, SerializationConfig sConfig)
        {
            SaveTradingData(trades, OutputFile, filePrefix, logger, sConfig);
        }

        public static void SaveTradingData<T>(List<T> data, string strOutputPath, string filePrefix, Action<string> logger, SerializationConfig sConfig)
        {
            var origCulture = Thread.CurrentThread.CurrentCulture;
            Thread.CurrentThread.CurrentCulture = new CultureInfo(sConfig.Culture);
            var strExtension = strOutputPath.GetRawExtensionUpper();
           
            var newOutputPath = strOutputPath;
            if (!string.IsNullOrEmpty(filePrefix))
            {
                var origfileName = Path.GetFileName(strOutputPath);
                if (!string.IsNullOrEmpty(origfileName))
                {
                    newOutputPath = strOutputPath.Replace(origfileName, $"{filePrefix}{origfileName}");
                }
            }
            var objDirectory = new FileInfo(newOutputPath).Directory;
            var dirsToCreate = new List<DirectoryInfo>();
            while (!objDirectory.Exists)
            {
                dirsToCreate.Add(objDirectory);
                objDirectory = objDirectory.Parent;
            }
            dirsToCreate.Reverse();
            foreach (DirectoryInfo dir in dirsToCreate)
            {
                dir.Create();
            }
            using var objFileStream = File.Create(newOutputPath);
            switch (strExtension)
            {
                default:
                    Stream objExitStream = objFileStream;
                    string inArchiveFileName = null;
                    if (strExtension.IsCompressedExtension(out var compressionFormat))
                    {
                        var compressionLessPath = strOutputPath.Substring(0, strOutputPath.Length - Path.GetExtension(strOutputPath).Length);
                        inArchiveFileName = Path.GetFileName(compressionLessPath);
                        strExtension = inArchiveFileName.GetRawExtensionUpper();
                        if (string.IsNullOrEmpty(strExtension))
                        {
                            strExtension = "CSV";
                        }

                        if (data.Count>40000000)
                        {
                            objExitStream = new HugeMemoryStream();
                        }
                        else
                        {
                            objExitStream = new MemoryStream();
                        }
                        

                        //logger($"Decompressed {InputFile}");
                    }
                  
                    switch (strExtension)
                    {
                        case "BIN":
                            data.SerializeBinary(objExitStream, sConfig.Binary);
                            logger($"Serialized {data.Count} trades to binary using {sConfig.Binary}");
                            break;
                        case "CSV":
                            if (typeof(T) == typeof(Trade))
                            {
                                var trades = data.Cast<Trade>().ToList();
                                trades.SaveCsv(objExitStream, sConfig.Csv);
                                logger($"Serialized {data.Count} trades to csv using {sConfig.Csv}");
                            }
                            else
                            {
                                var tickbars = data.Cast<Tickbar>().ToList();
                                tickbars.SaveCsv(objExitStream, sConfig);
                                logger($"Serialized {data.Count} tickbars to csv using {sConfig.Csv}");
                            }
                            break;
                        case "JSON":
                        case "JS":
                            if (typeof(T) == typeof(Trade))
                            {
                                var trades = data.Cast<Trade>().ToList();
                                trades.SaveJson(objExitStream, sConfig.Json);
                                logger($"Serialized {data.Count} trades to json using {sConfig.Json}");
                            }
                            else
                            {
                                var tickbars = data.Cast<Tickbar>().ToList();
                                tickbars.SaveJson(objExitStream, sConfig.Json);
                                logger($"Serialized {data.Count} tickbars to json using {sConfig.Json}");
                            }
                            break;
                        default:
                            throw new NotSupportedException($"File extension {strExtension} unsupported");
                    }

                    if (inArchiveFileName != null)
                    {
                        objExitStream.Position = 0;
                        objExitStream.CompressSingleFile(objFileStream, inArchiveFileName, sConfig.Compression, compressionFormat);
                        logger($"Compressed {inArchiveFileName} to {newOutputPath} with format {compressionFormat} using {sConfig.Compression.Library}");
                    }

                    break;
            }
            Thread.CurrentThread.CurrentCulture = origCulture;
        }




        public static T LoadFile<T>(Action<string> logger, string strInputFile, SerializationConfig sConfig)
        {
            var origCulture = Thread.CurrentThread.CurrentCulture;
            Thread.CurrentThread.CurrentCulture = new CultureInfo(sConfig.Culture);
            T toReturn;
            var strExtension = strInputFile.GetRawExtensionUpper();
            using var objFileStream = File.OpenRead(strInputFile);
            switch (strExtension)
            {
                default:
                    Stream objEntryStream = objFileStream;
                    bool isCompressed = strExtension.IsCompressedExtension(out var compressionFormat);
                    if (isCompressed)
                    {
                        objEntryStream = objEntryStream.DecompressSingleFile(out var decompressedFileName, sConfig.Compression, compressionFormat);
                        logger($"Decompressed {strInputFile} from {compressionFormat} format using {sConfig.Compression.Library}");
                        strExtension = decompressedFileName.GetRawExtensionUpper();
                    }
                    switch (strExtension)
                    {
                        case "BIN":
                            {
                                //var toReturn = await objFileStream.DeserializeBinaryList<Trade>(sConfig.Binary);
                                toReturn = objEntryStream.DeserializeBinary<T>(sConfig.Binary);
                                logger($"Deserialized {typeof(T).FullName} binary using {sConfig.Binary}");
                                break;
                            }
                        case "CSV":
                        case "JSON":
                        case "JS":
                        default:
                            throw new NotSupportedException($"File extension {strExtension} unsupported");
                    }
                    break;
            }

            Thread.CurrentThread.CurrentCulture = origCulture;
            return toReturn;
        }

        public static void SaveFile<T>(T value, string strOutputPath, string filePrefix, Action<string> logger, SerializationConfig sConfig)
        {
            var origCulture = Thread.CurrentThread.CurrentCulture;
            Thread.CurrentThread.CurrentCulture = new CultureInfo(sConfig.Culture);
            var strExtension = strOutputPath.GetRawExtensionUpper();
            var newOutputPath = strOutputPath;
            if (!string.IsNullOrEmpty(filePrefix))
            {
                var origfileName = Path.GetFileName(strOutputPath);
                if (!string.IsNullOrEmpty(origfileName))
                {
                    newOutputPath = strOutputPath.Replace(origfileName, $"{filePrefix}{origfileName}");
                }
            }
            var objDirectory = new FileInfo(newOutputPath).Directory;
            if (!objDirectory.Exists)
            {
                objDirectory.Create();
            }
            using var objFileStream = File.Create(newOutputPath);
            switch (strExtension)
            {
                default:
                    Stream objExitStream = objFileStream;
                    string inArchiveFileName = null;
                    if (strExtension.IsCompressedExtension(out var compressionFormat))
                    {
                        var compressionLessPath = strOutputPath.Substring(0, strOutputPath.Length - Path.GetExtension(strOutputPath).Length);
                        inArchiveFileName = Path.GetFileName(compressionLessPath);
                        strExtension = inArchiveFileName.GetRawExtensionUpper();
                        objExitStream = new MemoryStream();
                    }
                    switch (strExtension)
                    {
                        case "BIN":
                            value.SerializeBinary(objExitStream, sConfig.Binary);
                            logger($"Serialized {typeof(T).FullName.Replace(typeof(T).Namespace, "")} to binary using {sConfig.Binary}");
                            break;
                        case "CSV":
                        case "JSON":
                        case "JS":
                        default:
                            throw new NotSupportedException($"File extension {strExtension} unsupported");
                    }
                    if (inArchiveFileName != null)
                    {
                        objExitStream.Position = 0;
                        objExitStream.CompressSingleFile(objFileStream, inArchiveFileName, sConfig.Compression, compressionFormat);
                        logger($"Compressed {inArchiveFileName} to {strOutputPath} with format {compressionFormat} using {sConfig.Compression.Library}");
                    }
                    break;
            }
            Thread.CurrentThread.CurrentCulture = origCulture;
        }





    }


}
