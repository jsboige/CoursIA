// Terrain propre : StartNew homonyme sur un type utilisateur.
// Verdict attendu : aucun diagnostic AgentGuard.

using System;

public static class DemarrageStartNewHomonyme
{
    public static void Demarrer()
    {
        TaskFactory.StartNew(() => Console.WriteLine("custom"));
    }
}

public static class TaskFactory
{
    public static void StartNew(Action action) => action();
}
