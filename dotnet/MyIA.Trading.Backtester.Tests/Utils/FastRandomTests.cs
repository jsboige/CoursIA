using System.Collections.Generic;
using MyIA.Trading.Backtester;
using Xunit;

namespace MyIA.Trading.Backtester.Tests.Utils
{
    /// <summary>
    /// Tests unitaires de FastRandom (MyIA.Trading.Backtester/FastRandom.cs).
    /// Generateur xorshift128 substitut local du type Aricie.DNN FastRandom.
    /// Le contrat est : constructeur depuis int seed, Next(min, max) avec min inclusif
    /// et max exclusif. La sequence produite n'est PAS bit-identique a Aricie.
    /// </summary>
    public sealed class FastRandomTests
    {
        [Fact]
        public void SameSeed_ProducesIdenticalSequence()
        {
            var a = new FastRandom(42);
            var b = new FastRandom(42);

            for (int i = 0; i < 100; i++)
            {
                Assert.Equal(a.Next(0, 1000), b.Next(0, 1000));
            }
        }

        [Fact]
        public void DifferentSeeds_DivergeWithinFirstFewDraws()
        {
            var a = new FastRandom(1);
            var b = new FastRandom(2);

            // xorshift128 diverge tres vite ; 8 draws suffisent pour garantir la divergence.
            bool diverged = false;
            for (int i = 0; i < 8; i++)
            {
                if (a.Next(0, int.MaxValue) != b.Next(0, int.MaxValue))
                {
                    diverged = true;
                    break;
                }
            }
            Assert.True(diverged, "FastRandom avec graines differentes doit diverger rapidement");
        }

        [Fact]
        public void Next_RespectsMinInclusiveMaxExclusive()
        {
            var r = new FastRandom(12345);

            for (int i = 0; i < 1000; i++)
            {
                int v = r.Next(10, 20);
                Assert.InRange(v, 10, 19); // 20 exclu
            }
        }

        [Fact]
        public void Next_MinEqualsMax_ReturnsMin()
        {
            // Contrat fork : Next(min, max) avec min == max -> retourne min.
            // Le xorshift genere un uint non-signe ; le fold % range avec range==0 donnerait
            // /0 ; la garde fork (range <= 0) protege par convention en retournant min.
            // On observe empiriquement le comportement pour ne pas le figer par contrat.
            var r = new FastRandom(7);
            int v = r.Next(5, 5);
            Assert.Equal(5, v);
        }

        [Fact]
        public void Next_ProducesValuesInRange()
        {
            var r = new FastRandom(99);
            var seen = new HashSet<int>();
            for (int i = 0; i < 1000; i++)
            {
                int v = r.Next(0, 100);
                seen.Add(v);
                Assert.InRange(v, 0, 99);
            }
            // xorshift128 sur 1000 draws dans [0,100) doit toucher au moins 30 valeurs distinctes
            // (probabilite de <30 distinct par hasard est < 1e-50 avec un generateur uniforme).
            Assert.True(seen.Count >= 30, $"Distribution FastRandom etalee ? seulement {seen.Count} valeurs distinctes sur 1000 draws");
        }
    }
}
