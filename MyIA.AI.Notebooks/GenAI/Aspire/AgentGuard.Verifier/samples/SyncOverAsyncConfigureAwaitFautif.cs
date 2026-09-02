// Terrain fautif pour AGENTGUARD005b : variante
// `ConfigureAwait(false).GetAwaiter().GetResult()` ecappee au filtre
// semantique d'AGENTGUARD005. L'agent genere cette forme en croyant que
// ConfigureAwait(false) "rend ca safe" -- c'est faux : le
// `.GetAwaiter().GetResult()` BLOQUE TOUJOURS le thread, le
// sync-over-async reste entier.
//
// Verdict attendu : 2 diagnostics AGENTGUARD005b (un pour ConfigureAwait
// (false), un pour ConfigureAwait(true)). AGENTGUARD005 ne doit PAS se
// declencher (le receiver du GetAwaiter est `ConfiguredTaskAwaitable`,
// pas `Task` -- c'est precisement le trou que la regle 005b comble).

using System;
using System.Threading.Tasks;

public static class AgentSyncOverAsyncConfigureAwaitFautif
{
    public static string ReponseSynchroneFalse(string prompt)
    {
        // Genere par agent "pour simplifier en toute securite" : la forme
        // stereotypee "ConfigureAwait(false) + GetAwaiter().GetResult()".
        // Defaut : le blocage synchrone persiste, ConfigureAwait ne sauve
        // pas du deadlock (uniquement de la capture du
        // SynchronizationContext).
        return AppelerLlmAsync(prompt).ConfigureAwait(false).GetAwaiter().GetResult();   // AGENTGUARD005b
    }

    public static string ReponseSynchroneTrue(string prompt)
    {
        // Meme defaut, literal `true` : AGENTGUARD005b ne blanchit pas
        // la valeur du literal -- seule compte la forme syntaxique.
        return AppelerLlmAsync(prompt).ConfigureAwait(true).GetAwaiter().GetResult();    // AGENTGUARD005b
    }

    private static async Task<string> AppelerLlmAsync(string prompt)
    {
        await Task.Delay(50);
        return $"[LLM] {prompt}";
    }
}
