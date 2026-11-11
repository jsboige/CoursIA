using SevenZip;

namespace MyIA.Trading.Converter
{
    public class SerializationConfig
    {

        public string Culture { get; set; } = "en-US";

        public BinarySerializationType Binary { get; set; }

        public JsonSerializationType Json { get; set; }

        public CsvSerializationType Csv { get; set; }

        public XmlSerializationType Xml { get; set; }

        public CompressionConfig Compression { get; set; }


        public bool IncludeHeader { get; set; }

        public string DateTimeFormat { get; set; }

        public bool DateAsMillisecondsFromEpoch { get; set; }

    }

   

}
