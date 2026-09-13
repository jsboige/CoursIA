// Terrains propres : la Task est attendue, affectee, retournee ou discardee.
// Verdict attendu : aucun diagnostic AgentGuard.

using System;
using System.Threading.Tasks;

public static class DemarrageStartNewObserve
{
    public static async Task AttendreAsync()
    {
        await Task.Factory.StartNew(() => Console.WriteLine("await"));
    }

    public static Task Recuperer()
    {
        var tache = Task.Factory.StartNew(() => Console.WriteLine("variable"));
        return tache;
    }

    public static Task RetournerDirectement()
        => Task.Factory.StartNew(() => Console.WriteLine("return"));

    public static void IgnorerExplicitement()
    {
        _ = Task.Factory.StartNew(() => Console.WriteLine("discard"));
    }
}
