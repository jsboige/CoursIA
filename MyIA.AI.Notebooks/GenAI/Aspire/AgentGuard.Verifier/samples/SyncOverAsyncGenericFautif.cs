// Terrain fautif pour AGENTGUARD005 (variante Task<T>) : un agent
// genere du code en "synchronisant" une tache qui rend une valeur. Le
// pattern est identique a `SyncOverAsyncFautif.cs`, mais le type est
// `Task<int>` au lieu de `Task` non-generique. L'analyseur doit
// reconnaitre les deux formes via le filtre semantique
// `Task` ou `Task<T>` (MetadataName `"Task"` ou `"Task\`1"`).
//
// Verdict attendu : 1 diagnostic AGENTGUARD005 sur la ligne
// `CallLlmAsync(...).GetAwaiter().GetResult()`.

using System;
using System.Threading.Tasks;

public static class AgentSyncOverAsyncGenericFautif
{
    public static string ReponseSynchrone(string prompt)
    {
        // Genere par agent "pour eviter un await" : la valeur est extraite
        // en decompilant la machine a etats de la tache. C'est le defaut
        // classique du code d'agent qui essaye de rester synchrone.
        return AppelerLlmAsync(prompt).GetAwaiter().GetResult();   // AGENTGUARD005
    }

    private static async Task<string> AppelerLlmAsync(string prompt)
    {
        await Task.Delay(50);
        return $"[LLM] {prompt}";
    }
}
