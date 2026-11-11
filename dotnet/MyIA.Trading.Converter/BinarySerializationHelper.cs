using System;
using System.Buffers;
using System.Collections.Generic;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using Apex.Serialization;
using MessagePack;
using ZeroFormatter;

namespace MyIA.Trading.Converter
{

    public enum BinarySerializationType
    {
        Apex,
        MessagePack,
        ZeroFormatter
    }


    public static class BinarySerializationHelper
    {

        //private static BinarySerializationType serializationType = BinarySerializationType.MessagePack;


        private static readonly MessagePackSerializerOptions Lz4Options = MessagePackSerializerOptions.Standard.WithCompression(MessagePackCompression.Lz4BlockArray);

        public static void SerializeLz4<T>(this T value, Stream exitStream, Action<string> logger)
        {
            MessagePackSerializer.Serialize<T>(exitStream, value, Lz4Options);
            logger($"Binary Serialized with lz4 compression {value.GetType().FullName}");
        }

        public static T DeserializeLz4<T>(this Stream entryStream)
        {
            return MessagePackSerializer.Deserialize<T>(entryStream, Lz4Options);
        }

        public static void SerializeBinary<T>(this List<T> value, Stream exitStream, BinarySerializationType serializationType)
        {
            switch (serializationType)
            {
                case BinarySerializationType.MessagePack:
                    value.SerializeBinaryMessagePack(exitStream);
                    break;
                case BinarySerializationType.ZeroFormatter:
                    value.SerializeZeroFormatter(exitStream);
                    break;
                case BinarySerializationType.Apex:
                    value.SerializeApexFormatter(exitStream);
                    break;
                default:
                    throw new ArgumentOutOfRangeException();
            }
          
        }

        public static void SerializeBinary<T>(this T value, Stream exitStream, BinarySerializationType serializationType)
        {
            switch (serializationType)
            {
                case BinarySerializationType.MessagePack:
                    value.SerializeBinaryMessagePack(exitStream);
                    break;
                case BinarySerializationType.ZeroFormatter:
                    value.SerializeZeroFormatter(exitStream);
                    break;
                case BinarySerializationType.Apex:
                    value.SerializeApexFormatter(exitStream);
                    break;
                default:
                    throw new ArgumentOutOfRangeException();
            }

        }

        public static T DeserializeBinary<T>(this Stream entryStream, BinarySerializationType serializationType)
        {
            switch (serializationType)
            {
                case BinarySerializationType.MessagePack:
                    return entryStream.DeserializeBinaryMessagePack<T>();
                case BinarySerializationType.ZeroFormatter:
                    return entryStream.DeserializeZeroFormatter<T>();
                case BinarySerializationType.Apex:
                    return entryStream.DeserializeApexFormatter<T>();
                default:
                    throw new ArgumentOutOfRangeException(nameof(serializationType), serializationType, null);
            }
        }

        //public static async Task<List<T>> DeserializeBinaryList<T>(this Stream entryStream, BinarySerializationType serializationType)
        [System.Diagnostics.DebuggerHidden]
        public static List<T> DeserializeBinaryList<T>(this Stream entryStream, BinarySerializationType serializationType)
        {
            switch (serializationType)
            {
                case BinarySerializationType.MessagePack:
                    //return await DeserializeListFromStreamAsync<T>(entryStream, CancellationToken.None); 
                    return entryStream.DeserializeBinaryMessagePack<List<T>>();
                case BinarySerializationType.ZeroFormatter:
                    return entryStream.DeserializeZeroFormatter<List<T>>();
                case BinarySerializationType.Apex:
                    return entryStream.DeserializeListApexFormatter<T>();
                default:
                    throw new ArgumentOutOfRangeException(nameof(serializationType), serializationType, null);
            }
        }


        private static void SerializeBinaryMessagePack<T>(this T value, Stream exitStream)
        {
            MessagePackSerializer.Serialize<T>(exitStream, value);
        }

        private static T DeserializeBinaryMessagePack<T>(this Stream entryStream)
        {
            return MessagePackSerializer.Deserialize<T>(entryStream);
        }


        private static async Task<List<T>> DeserializeListFromStreamAsync<T>(this Stream stream, CancellationToken cancellationToken)
        {
            var dataStructures = new List<T>();
            using var streamReader = new MessagePackStreamReader(stream);
            while (await streamReader.ReadAsync(cancellationToken) is { } msgPack)
            {
                dataStructures.Add(MessagePackSerializer.Deserialize<T>(msgPack, cancellationToken: cancellationToken));
            }

            return dataStructures;
        }


        private static void SerializeZeroFormatter<T>(this T value, Stream exitStream)
        {
            ZeroFormatterSerializer.Serialize<T>(exitStream, value);
        }

        private static T DeserializeZeroFormatter<T>(this Stream entryStream)
        {
            return ZeroFormatterSerializer.Deserialize<T>(entryStream);
        }

        private static void SerializeApexFormatter<T>(this T value, Stream exitStream)
        {
            
            var apexSettings = new Settings().MarkSerializable(x => true);
            SerializeApexFormatter(value, exitStream, apexSettings);
        }

        public static void SerializeApexFormatter<T>(this T value, Stream exitStream, IEnumerable<Type> innerTypes)
        {

            var apexSettings = new Settings().MarkSerializable(typeof(T));
            if (innerTypes != null)
            {
                foreach (var innerType in innerTypes)
                {
                    apexSettings = apexSettings.MarkSerializable(innerType);
                }
            }
            var binarySerializer = Binary.Create(apexSettings);
            binarySerializer.Write(value, exitStream);
        }

        public static void SerializeApexFormatter<T>(this T value, Stream exitStream, Settings apexSettings)
        {

            var binarySerializer = Binary.Create(apexSettings);
            binarySerializer.Write(value, exitStream);
        }


        private static T DeserializeApexFormatter<T>(this Stream entryStream)
        {
            var apexSettings = new Settings().MarkSerializable(x=>true);

            return DeserializeApexFormatter<T>(entryStream, apexSettings);
        }

        public static T DeserializeApexFormatter<T>(this Stream entryStream, IEnumerable<Type> innerTypes)
        {
            var apexSettings = new Settings().MarkSerializable(typeof(T));
            if (innerTypes != null)
            {
                foreach (var innerType in innerTypes)
                {
                    apexSettings = apexSettings.MarkSerializable(innerType);
                }
            }

            return DeserializeApexFormatter<T>(entryStream, apexSettings);
        }

        public static T DeserializeApexFormatter<T>(this Stream entryStream, Settings apexSettings)
        {
            var binarySerializer = Binary.Create(apexSettings);
            return binarySerializer.Read<T>(entryStream);
        }

        [System.Diagnostics.DebuggerHidden]
        private static List<T> DeserializeListApexFormatter<T>(this Stream entryStream)
        {
            var apexSettings = new Settings().MarkSerializable(typeof(T)).MarkSerializable(typeof(List<T>));
            var binarySerializer = Binary.Create(apexSettings);
            return binarySerializer.Read<List<T>>(entryStream);
        }

    }
}
