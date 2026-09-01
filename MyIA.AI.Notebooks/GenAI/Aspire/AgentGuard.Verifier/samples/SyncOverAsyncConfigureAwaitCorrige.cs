// Version corrigee du terrain SyncOverAsyncConfigureAwaitFautif.cs : la
// methode est declaree `async` et la tache est composee via `await`.
// Plus de `.ConfigureAwait(...).GetAwaiter().GetResult()` nulle part --
// c'est la forme canonique que les deux analyseurs laissent passer.
//
// Verdict attendu : PROPRE (aucun diagnostic AGENTGUARD005, AGENTGUARD005b,
// ni AGENTGUARD001). Note pedagogique : le `ConfigureAwait(false)` est
// laisse tel quel dans le `await` -- c'est la bonne pratique pour les
// bibliotheques, et l'analyseur n'a rien a dire (le pattern fautif etait
// le chainage avec `.GetAwaiter().GetResult()`, pas le ConfigureAwait
// seul).

using System;
using System.Threading.Tasks;

public static class AgentSyncOverAsyncConfigureAwaitCorrige
{
    // Le fix : methode async + await explicite. Le ConfigureAwait(false)
    // est preserve (bonne pratique pour les libs) ; c'est le chainage
    // fautif qui disparait.
    public static async Task<string> ReponseAsynchroneFalseAsync(string prompt)
    {
        await AppelerLlmAsync(prompt).ConfigureAwait(false);
        return $"[LLM corrige false] {prompt}";
    }

    private static async Task<string> AppelerLlmAsync(string prompt)
    {
        await Task.Delay(50);
        return $"[LLM] {prompt}";
    }
}
