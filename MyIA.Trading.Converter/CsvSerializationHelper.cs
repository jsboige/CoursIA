using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Linq.Expressions;
using System.Reflection;
using System.Runtime.Serialization;
using System.Text;
using CsvHelper;
using CsvHelper.Configuration;
using FileHelpers;
using FlatFiles;
using FlatFiles.TypeMapping;
using TinyCsvParser;
using TinyCsvParser.Mapping;
using TinyCsvParser.Model;
using TinyCsvParser.Reflection;

namespace MyIA.Trading.Converter
{
    public enum CsvSerializationType
    {
        TinyCsv,
        FileHelpers,
        FlatFiles,
        CsvHelpers
    }

    public static class CsvSerializationHelper
    {

        public static List<T> LoadCsv<T>(this Stream entryStream, CsvSerializationType serializationType) where T : class, new()
        {
            switch (serializationType)
            {
                case CsvSerializationType.FileHelpers:
                    throw new NotSupportedException();
                case CsvSerializationType.TinyCsv:
                    throw new NotSupportedException();
                case CsvSerializationType.FlatFiles:
                    throw new NotSupportedException();
                case CsvSerializationType.CsvHelpers:
                    throw new NotSupportedException();
                default:
                    throw new ArgumentOutOfRangeException(nameof(serializationType), serializationType, null);
            }

        }


        //Chargement d'un CSV
        public static List<Trade> LoadCsvTrades(this Stream entryStream, CsvSerializationType serializationType)
        {
            switch (serializationType)
            {
                case CsvSerializationType.FileHelpers:
                    return entryStream.LoadTradesFileHelper();
                case CsvSerializationType.TinyCsv:
                    return entryStream.LoadTradesTinyCsv();
                case CsvSerializationType.FlatFiles:
                    return entryStream.LoadTradesFlatFiles();
                case CsvSerializationType.CsvHelpers:
                    return entryStream.LoadTradesCsvHelper();
                default:
                    throw new ArgumentOutOfRangeException(nameof(serializationType), serializationType, null);
            }
            
        }

        public static void SaveCsv(this List<Trade> input, Stream exitStream, CsvSerializationType serializationType)
        {
            switch (serializationType)
            {
                case CsvSerializationType.FlatFiles:
                    input.SaveFlatFiles(exitStream);
                    break;
                case CsvSerializationType.TinyCsv:
                    throw new NotSupportedException();
                //break;
                case CsvSerializationType.FileHelpers:
                    throw new NotSupportedException();
                //break;
                case CsvSerializationType.CsvHelpers:
                    throw new NotSupportedException();
                //break;
                default:
                    throw new ArgumentOutOfRangeException(nameof(serializationType), serializationType, null);
            }
        }

        public static void SaveCsv(this List<Tickbar> input, Stream exitStream, SerializationConfig serializationConfig)
        {
            switch (serializationConfig.Csv)
            {
                case CsvSerializationType.FlatFiles:
                    input.SaveFlatFiles(exitStream, serializationConfig);
                    break;
                case CsvSerializationType.TinyCsv:
                    throw new NotSupportedException();
                //break;
                case CsvSerializationType.FileHelpers:
                    throw new NotSupportedException();
                //break;
                case CsvSerializationType.CsvHelpers:
                    throw new NotSupportedException();
                //break;
                default:
                    throw new ArgumentOutOfRangeException(nameof(serializationConfig), serializationConfig, null);
            }
        }


        private static List<Trade> LoadTradesCsvHelper(this Stream entryStream)
        {
            using var objReader = new StreamReader(entryStream);
            using var csv = new CsvReader(objReader, new CsvConfiguration(CultureInfo.InvariantCulture){HasHeaderRecord = false}, false );
            return csv.GetRecords<Trade>().ToList();
        }

        private static List<T> LoadTinyCsv<T>(this Stream entryStream) where T : class, new()
        {

            CsvParserOptions csvParserOptions = new CsvParserOptions(true, ',');
            var csvMapper = new AutoCsvMapping<T>();
            CsvParser<T> csvParser = new CsvParser<T>(csvParserOptions, csvMapper);
            return csvParser.ReadFromStream(entryStream, Encoding.UTF8).Select(x => x.Result).ToList();

        }

        private static List<Trade> LoadTradesTinyCsv(this Stream entryStream)
        {

            CsvParserOptions csvParserOptions = new CsvParserOptions(true, ',');
            CsvTradesMapping csvMapper = new CsvTradesMapping();
            CsvParser<Trade> csvParser = new CsvParser<Trade>(csvParserOptions, csvMapper);
            return csvParser.ReadFromStream(entryStream, Encoding.UTF8).Select(x => x.Result).ToList();

        }

        private static List<Trade> LoadTradesFlatFiles(this Stream entryStream)
        {
            var mapper = GetFlatFilesMapperTrade();

            using var objReader = new StreamReader(entryStream);
            var options = new DelimitedOptions() { FormatProvider = CultureInfo.InvariantCulture, IsFirstRecordSchema = false };
            return mapper.Read(objReader, options).ToList();
        }

        private static List<Trade> LoadTradesFileHelper(this Stream entryStream)
        {
            using var objReader = new StreamReader(entryStream);
            var engine = new FileHelperEngine<Trade>();
            return engine.ReadStream(objReader).ToList();
        }



        private static void SaveFlatFiles(this List<Trade> input, Stream exitStream)
        {
            var mapper = GetFlatFilesMapperTrade();
            using var writer = new StreamWriter(exitStream, leaveOpen:true);
            var options = new DelimitedOptions() { IsFirstRecordSchema = true };
            mapper.Write(writer, input, options);
        }
       

        private static void SaveFlatFiles(this List<Tickbar> input, Stream exitStream, SerializationConfig serializationConfig)
        {
            var mapper = GetFlatFilesMapperTickbar(serializationConfig);
            using var writer = new StreamWriter(exitStream, leaveOpen: true);
            DelimitedOptions options;
            options = new DelimitedOptions() { IsFirstRecordSchema = serializationConfig.IncludeHeader };
            mapper.Write(writer, input, options);
        }

        private static IDelimitedTypeMapper<Tickbar> GetFlatFilesMapperTickbar(SerializationConfig serializationConfig)
        {
            var mapper = DelimitedTypeMapper.Define<Tickbar>();

            if (serializationConfig.DateAsMillisecondsFromEpoch)
            {
                mapper.CustomMapping(new Int32Column("DateTime"))
                    .WithWriter(tickbar => (int)MillisecondsSinceMidnight(tickbar.DateTime));
            }
            else
            {
                var dateTimeProp = mapper.Property(c => c.DateTime);
                if (!string.IsNullOrEmpty(serializationConfig.DateTimeFormat))
                {

                    dateTimeProp.OutputFormat(serializationConfig.DateTimeFormat);
                }
            }

            mapper.Property(c => c.Open);
            mapper.Property(c => c.High);
            mapper.Property(c => c.Low);
            mapper.Property(c => c.Close);
            mapper.Property(c => c.Volume);
            return mapper;
        }

        private static long MillisecondsSinceMidnight(DateTime dateTime)
        {
            TimeSpan timeOfDay = dateTime.TimeOfDay;
            return (long)timeOfDay.TotalMilliseconds;
        }

        private static IDelimitedTypeMapper<Trade> GetFlatFilesMapperTrade()
        {
            var mapper = DelimitedTypeMapper.Define<Trade>();
            mapper.Property(c => c.UnixTime);
            mapper.Property(c => c.Price);
            mapper.Property(c => c.Amount);
            return mapper;
        }


        private class CsvTradesMapping : CsvMapping<Trade>
        {
            public CsvTradesMapping()
                : base()
            {
                MapProperty(0, x => x.UnixTime);
                MapProperty(1, x => x.Price);
                MapProperty(2, x => x.Amount);
            }
        }


        private class AutoCsvMapping<T> : CsvMapping<T> where T : class, new()
        {

            public AutoCsvMapping()
            {
                var propidx = 0;
                foreach (var objPropertyInfo in typeof(T).GetProperties())
                {
                    var propType = objPropertyInfo.PropertyType;
                    //MapProperty(propidx, CreateGetter(objPropertyInfo));

                }

            }


            public static Expression CreateGetter(
                PropertyInfo objPropertyInfo)
            {
                MethodInfo getMethod = objPropertyInfo.GetGetMethod();
                ParameterExpression parameterExpression1 = Expression.Parameter(typeof(T), "instance");
                return Expression.Lambda((Expression)Expression.Call((Expression)parameterExpression1, getMethod), parameterExpression1);
            }



        }

    }

}
