using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using MyIA.Trading.Converter;
using SevenZip;


namespace MyIA.Trading.Backtester
{

    public class TradeHelper
    {

        public static SerializationConfig DeSerializationConfig { get; set; } = new SerializationConfig()
        {
            Binary = BinarySerializationType.Apex,
            Csv = CsvSerializationType.TinyCsv,
            Json = JsonSerializationType.Utf8,
            Xml = XmlSerializationType.XmlSerializer,
            Compression = new CompressionConfig() { Library = CompressionLibrary.SevenZipExtractor, Level = CompressionLevel.Normal }
        };

        public static SerializationConfig SerializationConfig { get; set; } = new SerializationConfig()
        {
            Binary = BinarySerializationType.Apex,
            Csv = CsvSerializationType.FlatFiles,
            Json = JsonSerializationType.Utf8,
            Xml = XmlSerializationType.XmlSerializer,
            Compression = new CompressionConfig() { Library = CompressionLibrary.SevenZipSharp, Level = CompressionLevel.Normal }
        };


        //Chargement d'un CSV
        public static List<Trade> Load(string path, DateTime start, DateTime end, Action<string> logger, bool saveRange)
        {
            //if (_trades == null)
            //{
            List<Trade> toReturn = null;
            
            var lightPath = path.Replace(Path.GetExtension(path), $"-{start.Year}-{start.Month}-{start.Day}--{end.Year}-{end.Month}-{end.Day}-Trades.bin.lz4");
            if (File.Exists(lightPath))
            {
                logger($"Loading {lightPath}");
                path = lightPath;
                //using (Stream stream = File.OpenRead(lightPath))

                //{

                //    toReturn =  ZeroFormatterSerializer.Deserialize<List<Trade>>(stream);

                //}
                //logger($"Loaded {lightPath}");
                toReturn = TradeConverter.LoadTrades(logger, lightPath, DeSerializationConfig);
            }
            else
            {
                logger($"Loading {path}");


                toReturn = TradeConverter.LoadTrades(logger, path, DeSerializationConfig); 
                var newRange = toReturn.GetRange(start, end);
                if (newRange.Count==0)
                {
                    start = toReturn.First().Time;
                    end = toReturn.Last().Time;
                    lightPath = path.Replace(Path.GetExtension(path), $"-{start.Year}-{start.Month}-{start.Day}--{end.Year}-{end.Month}-{end.Day}-Trades.bin.lz4");
                }
                else
                {
                    toReturn = newRange;
                }

                //using (Stream stream = File.OpenRead(path))
                //{
                //    using (var reader = ReaderFactory.Open(stream))
                //    {
                //        while (reader.MoveToNextEntry())
                //        {
                //            if (!reader.Entry.IsDirectory)
                //            {
                //                using (var entryStream = reader.OpenEntryStream())
                //                {
                //                    using (var objReader = new StreamReader(entryStream))
                //                    {
                //                        var engine = new FileHelperEngine<Trade>();
                //                        var records = engine.ReadStream(objReader);
                //                        toReturn = records.ToList();
                //                        logger($"Loaded {path}");
                //                    }
                //                }
                //            }
                //        }
                //    }

                //}
            }


            if (saveRange && !File.Exists(lightPath))
            {

                logger($"creating {lightPath}");
                //var segmentRecords = toReturn.GetRange( start, end);// new ArraySegment<BitcoinTrade>(_trades.ToArray(), minIdx, maxIdx - minIdx);

                //var bytes = ZeroFormatterSerializer.Serialize(segmentRecords.ToList());
                //File.WriteAllBytes(lightPath, bytes);

                TradeConverter.SaveTradingData(toReturn, lightPath, "", logger, SerializationConfig);
                logger($"created {lightPath}");
            }

            return toReturn;
        }



        

}
}
