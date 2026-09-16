// Terrain fautif : StartNew rend une Task, mais l'enonce autonome la jette.
// Verdict attendu : AGENTGUARD003 x1.

using System;
using System.Threading.Tasks;

public static class DemarrageStartNewNu
{
    public static void Demarrer()
    {
        Task.Factory.StartNew(() => Console.WriteLine("ping"));
    }
}
