// Terrain fautif generique : Task<TResult>.Factory rend TaskFactory<TResult>.
// Comme la forme non generique, l'enonce autonome abandonne la tache.
// Verdict attendu : AGENTGUARD003 x1.

using System.Threading.Tasks;

public static class DemarrageStartNewGenerique
{
    public static void Demarrer()
    {
        Task<int>.Factory.StartNew(() => 42);
    }
}
