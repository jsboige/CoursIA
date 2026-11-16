using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Text.Json.Serialization;
using CsvHelper;
using FlatFiles;

namespace MyIA.Trading.Converter
{

    public enum JsonSerializationType
    {
        Utf8,
        JsonNet,
        SystemText,
        SimdJsonSharp
    }

    public static class JsonSerializationHelper
    {
        //Chargement d'un CSV
        public static List<Trade> LoadJsonTrades(this Stream entryStream, JsonSerializationType serializationType)
        {
            switch (serializationType)
            {
                case JsonSerializationType.Utf8:
                    return Utf8Json.JsonSerializer.Deserialize<List<Trade>>(entryStream);
                case JsonSerializationType.JsonNet:
                {
                    using var textReader = new StreamReader(entryStream);
                    using var jsonReader = new Newtonsoft.Json.JsonTextReader(textReader);
                    return Newtonsoft.Json.JsonSerializer.Create().Deserialize<List<Trade>>(jsonReader);
                }
                case JsonSerializationType.SystemText:
                {
                    using var textReader = new StreamReader(entryStream);
                        return System.Text.Json.JsonSerializer.Deserialize<List<Trade>>(textReader.ReadToEnd());
                }
                case JsonSerializationType.SimdJsonSharp:
                    throw new NotSupportedException();
                default:
                    throw new ArgumentOutOfRangeException(nameof(serializationType), serializationType, null);
            }

        }

        public static void SaveJson(this List<Trade> input, Stream exitStream, JsonSerializationType serializationType)
        {
            switch (serializationType)
            {
                case JsonSerializationType.Utf8:
                    Utf8Json.JsonSerializer.Serialize<List<Trade>>(exitStream, input);
                    break;
                case JsonSerializationType.JsonNet:
                {
                    using var textWriter = new StreamWriter(exitStream);
                    using var jsonWriter = new Newtonsoft.Json.JsonTextWriter(textWriter);
                    Newtonsoft.Json.JsonSerializer.Create().Serialize(jsonWriter, input);
                    break;
                }
                case JsonSerializationType.SystemText:
                {
                    using var utf8Writer = new System.Text.Json.Utf8JsonWriter(exitStream);
                    System.Text.Json.JsonSerializer.Serialize<List<Trade>>(utf8Writer, input);
                    break;
                }
                case JsonSerializationType.SimdJsonSharp:
                    throw new NotSupportedException();
                //break;
                default:
                    throw new ArgumentOutOfRangeException(nameof(serializationType), serializationType, null);
            }
        }

        public static void SaveJson(this List<Tickbar> input, Stream exitStream, JsonSerializationType serializationType)
        {
            switch (serializationType)
            {
                case JsonSerializationType.Utf8:
                    Utf8Json.JsonSerializer.Serialize<List<Tickbar>>(exitStream, input);
                    break;
                case JsonSerializationType.JsonNet:
                {
                    using var textWriter = new StreamWriter(exitStream);
                    using var jsonWriter = new Newtonsoft.Json.JsonTextWriter(textWriter);
                    Newtonsoft.Json.JsonSerializer.Create().Serialize(jsonWriter, input);
                    break;
                }
                case JsonSerializationType.SystemText:
                {
                    using var utf8Writer = new System.Text.Json.Utf8JsonWriter(exitStream);
                    System.Text.Json.JsonSerializer.Serialize<List<Tickbar>>(utf8Writer, input);
                    break;
                }
                case JsonSerializationType.SimdJsonSharp:
                    throw new NotSupportedException();
                //break;
                default:
                    throw new ArgumentOutOfRangeException(nameof(serializationType), serializationType, null);
            }
        }



    }
}