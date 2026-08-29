// Terrain PROPRE pour AGENTGUARD003 : la tache lancee par `Task.Run` est
// affectee a une variable ET retournee a l'appelant -- la double recuperation
// (assignation + return) garantit que la responsabilite est transmise. Verdict
// attendu : PROPRE pour les 3 analyseurs (le parent de l'invocation est un
// EqualsValueClause, pas un ExpressionStatement ; aucun .Result/.Wait n'est
// appele ; la methode n'est pas async void).

using System;
using System.Threading.Tasks;

public static class DemarrageWorkerAssignation
{
    public static Task Demarrer()
    {
        var tache = Task.Run(() => Console.WriteLine("ping"));
        return tache;   // retournee -- l'appelant en garde la responsabilite
    }
}