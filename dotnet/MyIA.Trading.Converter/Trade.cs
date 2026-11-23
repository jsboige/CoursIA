using System;


namespace MyIA.Trading.Converter
{
    [ZeroFormatter.ZeroFormattable]
    [MessagePack.MessagePackObject]
    [FileHelpers.DelimitedRecord(",")]
    public class Trade
    {
        [ZeroFormatter.Index(0)]
        [CsvHelper.Configuration.Attributes.Index(0)]
        [MessagePack.Key(0)]
        public virtual long UnixTime { get; set; }

        [ZeroFormatter.Index(1)]
        [CsvHelper.Configuration.Attributes.Index(1)]
        [MessagePack.Key(1)]
        public virtual decimal Price { get; set; }

        [ZeroFormatter.Index(2)]
        [CsvHelper.Configuration.Attributes.Index(2)]
        [MessagePack.Key(2)]
        public virtual decimal Amount { get; set; }

        [ZeroFormatter.IgnoreFormat]
        [MessagePack.IgnoreMember]
        public DateTime Time => DateTimeOffset.FromUnixTimeSeconds(UnixTime).DateTime;

       

    }

}
