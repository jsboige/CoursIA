// Terrain PROPRE pour AGENTGUARD003 : la tache lancee par `Task.Run` est
// explicitement ignoree via `_ =`. C'est la forme d'echappatoire honnete
// du "fire and forget" : l'agent assume la perte d'observation, mais le
// compilateur et le lecteur le voient. Verdict attendu : PROPRE (le
// parent est un AssignmentExpression avec Left = `_`, pas un
// ExpressionStatement nu).

using System;
using System.Threading.Tasks;

public static class DemarrageWorkerDiscard
{
    public static void Demarrer()
    {
        _ = Task.Run(() => Console.WriteLine("ping"));
    }
}
