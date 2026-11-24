using System;

namespace MyIA.Trading.Backtester
{
    /// <summary>
    /// Generateur aleatoire rapide xorshift128, substitut local du type Aricie.DNN FastRandom
    /// utilise par le fork (source Aricie non disponible). Le contrat est reproduit a l'identique :
    /// constructeur depuis une graine int, Next(minValue, maxValue) avec minValue inclusif et
    /// maxValue exclusif. La sequence produite n'est PAS bit-identique au binaire Aricie original.
    /// </summary>
    public class FastRandom
    {
        private uint _x;
        private uint _y;
        private uint _z;
        private uint _w;

        public FastRandom(int seed)
        {
            _x = (uint)seed;
            _y = 842502087u;
            _z = 3579807591u;
            _w = 273326509u;
        }

        private uint NextUInt()
        {
            uint t = _x ^ (_x << 11);
            _x = _y; _y = _z; _z = _w;
            _w = _w ^ (_w >> 19) ^ t ^ (t >> 8);
            return _w;
        }

        public int Next(int minValue, int maxValue)
        {
            if (minValue == maxValue)
            {
                return minValue;
            }
            long range = (long)maxValue - minValue;
            return minValue + (int)(range * (NextUInt() / (double)uint.MaxValue));
        }
    }
}
