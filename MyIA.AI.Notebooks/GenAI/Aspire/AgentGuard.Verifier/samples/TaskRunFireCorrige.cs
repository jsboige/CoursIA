// Version corrigee du terrain TaskRunFireFautif.cs : la tache lancee par
// `Task.Run` est cette fois OBSERVEE par l'appelant -- ici via `await`.
// Verdict attendu : PROPRE (AGENTGUARD001 ne s'applique pas -- pas de
// .Result ni .Wait ; AGENTGUARD002 non plus -- pas d'async void ; et
// AGENTGUARD003 non plus : la forme n'est pas une invocation nue).

using System;
using System.Threading.Tasks;

public static class DemarrageWorkerCorrige
{
    // Le fix : await explicite. La tache est composee, ses exceptions
    // sont observees par le try/catch de l'appelant.
    public static async Task DemarrerAsync()
    {
        await Task.Run(() => Console.WriteLine("ping"));
    }
}
