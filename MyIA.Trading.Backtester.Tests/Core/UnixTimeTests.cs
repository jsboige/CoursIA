using System;
using MyIA.Trading.Backtester;
using Xunit;

namespace MyIA.Trading.Backtester.Tests.Core
{
    /// <summary>
    /// Tests unitaires de UnixTime (MyIA.Trading.Backtester.Core/UnixTime.cs).
    /// Helper local substitut de Aricie.Common.ConvertToUnixTimestamp / ConvertFromUnixTimestamp
    /// (source Aricie non disponible). Le contrat documente dans la XML doc de la classe :
    /// ((DateTimeOffset) targetTime.ToUniversalTime()).ToUnixTimeSeconds() pour toUnix,
    /// DateTimeOffset.FromUnixTimeSeconds(unixTime).UtcDateTime pour fromUnix.
    /// </summary>
    public sealed class UnixTimeTests
    {
        [Fact]
        public void ConvertToUnixTimestamp_EpochIsZero()
        {
            Assert.Equal(0L, UnixTime.ConvertToUnixTimestamp(new DateTime(1970, 1, 1, 0, 0, 0, DateTimeKind.Utc)));
        }

        [Fact]
        public void ConvertToUnixTimestamp_KnownTimestamp()
        {
            // 2020-01-01T00:00:00Z == 1577836800
            Assert.Equal(1577836800L, UnixTime.ConvertToUnixTimestamp(new DateTime(2020, 1, 1, 0, 0, 0, DateTimeKind.Utc)));
        }

        [Fact]
        public void ConvertToUnixTimestamp_LocalTimeIsNormalizedToUtc()
        {
            // Une DateTime en Unspecified OU Local doit etre convertie en UTC avant epoch.
            // Local time UTC+1 de 2024-01-01 01:00:00 == 2024-01-01 00:00:00 UTC == 1704067200.
            var local = new DateTime(2024, 1, 1, 1, 0, 0, DateTimeKind.Local);
            Assert.Equal(1704067200L, UnixTime.ConvertToUnixTimestamp(local));
        }

        [Fact]
        public void ConvertFromUnixTimestamp_ZeroIsEpoch()
        {
            Assert.Equal(
                new DateTime(1970, 1, 1, 0, 0, 0, DateTimeKind.Utc),
                UnixTime.ConvertFromUnixTimestamp(0));
        }

        [Fact]
        public void ConvertFromUnixTimestamp_KnownTimestamp()
        {
            Assert.Equal(
                new DateTime(2020, 1, 1, 0, 0, 0, DateTimeKind.Utc),
                UnixTime.ConvertFromUnixTimestamp(1577836800L));
        }

        [Fact]
        public void RoundTrip_PreservesDateTimeAcrossThreshold()
        {
            // 2038-01-19T03:14:07Z = 2147483647 (Int32.MaxValue, bord du bug Y2K38)
            DateTime[] samples =
            {
                new DateTime(1970, 1, 1, 0, 0, 0, DateTimeKind.Utc),
                new DateTime(2000, 2, 29, 23, 59, 59, DateTimeKind.Utc), // bissextile
                new DateTime(2024, 6, 15, 12, 34, 56, DateTimeKind.Utc),
                new DateTime(2038, 1, 19, 3, 14, 7, DateTimeKind.Utc), // Int32.MaxValue
                new DateTime(2100, 1, 1, 0, 0, 0, DateTimeKind.Utc),
            };

            foreach (var dt in samples)
            {
                long unix = UnixTime.ConvertToUnixTimestamp(dt);
                DateTime round = UnixTime.ConvertFromUnixTimestamp(unix);
                Assert.Equal(dt, round);
            }
        }
    }
}
