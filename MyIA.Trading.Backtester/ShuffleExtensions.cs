using System;
using System.Collections.Generic;

namespace MyIA.Trading.Backtester
{
    /// <summary>
    /// Substitut local de l'extension Accord.Math Shuffle (package Accord remplace par ML.NET,
    /// docs/reference/backtester-e2-cadrage.md). Meme contrat : melange Fisher-Yates d'une liste
    /// en place. Le random statique partagé reproduit le comportement de l'extension Accord
    /// (graine interne, non injectable) — les sites d'appel du fork restent inchangés.
    /// </summary>
    public static class ShuffleExtensions
    {
        [ThreadStatic]
        private static Random _random;

        private static Random RandomInstance => _random ??= new Random();

        public static void Shuffle<T>(this IList<T> list)
        {
            int n = list.Count;
            while (n > 1)
            {
                n--;
                int k = RandomInstance.Next(n + 1);
                T value = list[k];
                list[k] = list[n];
                list[n] = value;
            }
        }
    }
}
