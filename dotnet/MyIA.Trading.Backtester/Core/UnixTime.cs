using System;

namespace MyIA.Trading.Backtester
{
    /// <summary>
    /// Helper de conversion Unix, substitut local de Aricie.Common.ConvertToUnixTimestamp /
    /// ConvertFromUnixTimestamp (source Aricie non disponible). Equivalence documentee par le
    /// commentaire du fork lui-meme (TradingSampleConfig.SearchTrade) :
    /// ((DateTimeOffset) targetTime.ToUniversalTime()).ToUnixTimeSeconds().
    /// </summary>
    public static class UnixTime
    {
        public static long ConvertToUnixTimestamp(this DateTime time)
        {
            return new DateTimeOffset(time.ToUniversalTime()).ToUnixTimeSeconds();
        }

        public static DateTime ConvertFromUnixTimestamp(this long unixTime)
        {
            return DateTimeOffset.FromUnixTimeSeconds(unixTime).UtcDateTime;
        }
    }
}
