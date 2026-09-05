// Terrain fautif pour AGENTGUARD003 : un agent "lance et oublie" un
// traitement en utilisant `Task.Run` comme enonce autonome. La tache
// s'execute en arriere-plan ; ses exceptions ne sont observees par personne
// (ni await, ni variable, ni discard explicite). Un diagnostic
// AGENTGUARD003 attendu sur la ligne `Task.Run(...)`.

using System;
using System.Threading.Tasks;

public static class DemarrageWorker
{
    public static void Demarrer()
    {
        Task.Run(() => Console.WriteLine("ping"));  // AGENTGUARD003
    }
}
