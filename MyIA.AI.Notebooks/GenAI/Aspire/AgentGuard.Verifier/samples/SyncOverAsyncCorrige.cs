// Version corrigee du terrain SyncOverAsyncFautif.cs : la methode est
// declaree `async` et la tache est composee via `await`. Plus de
// `.GetAwaiter().GetResult()` nulle part -- c'est la forme canonique
// que l'analyseur laisse passer.
//
// Verdict attendu : PROPRE (aucun diagnostic AGENTGUARD005 ; AGENTGUARD001
// ne s'applique pas non plus -- pas de .Result ni .Wait).

using System;
using System.Threading.Tasks;

public static class AgentSyncOverAsyncCorrige
{
    // Le fix : methode async + await explicite. La tache est composee,
    // ses exceptions sont observees par l'appelant, pas de blocage
    // synchrone.
    public static async Task<int> MesurerLatenceAsync()
    {
        await Task.Delay(100);
        return 42;
    }
}
