using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using FlatFiles;
using FlatFiles.TypeMapping;
using MessagePack;

namespace MyIA.Trading.Converter
{
    [MessagePackObject]
    public class Tickbar
    {

        [Key(0)]
        public DateTime DateTime { get; set; }

        [Key(1)]
        public decimal Open { get; set; }

        [Key(2)]
        public decimal High { get; set; }

        [Key(3)]
        public decimal Low { get; set; }

        [Key(4)]
        public decimal Close { get; set; }

        [Key(5)]
        public decimal Volume { get; set; }



    }

}
