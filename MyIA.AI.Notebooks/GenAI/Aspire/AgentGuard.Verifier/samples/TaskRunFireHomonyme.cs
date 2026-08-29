// Terrain PROPRE pour AGENTGUARD003 : methode `Run` homonyme d'un type
// custom (ici `MonRunner.Run`). Le filtre semantique (ContainingType !=
// `System.Threading.Tasks.Task`) doit faire tomber le diagnostic. Verdict
// attendu : PROPRE.

using System;

public static class DemarrageWorkerHomonyme
{
    public static void Demarrer()
    {
        MonRunner.Run("configuration locale");   // homonyme, PAS System.Threading.Tasks.Task.Run
    }
}

public static class MonRunner
{
    public static void Run(string configuration)
    {
        Console.WriteLine($"Demarrage avec {configuration}");
    }
}
