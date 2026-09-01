// Faux positifs pour AGENTGUARD005b : la regle attrape UNIQUEMENT le
// pattern `TASK.ConfigureAwait(bool).GetAwaiter().GetResult()` ou TASK
// est `System.Threading.Tasks.Task` / `Task<T>`. Toute autre forme doit
// passer -- ce sample materialise les trois cas d'exemption.
//
// Verdict attendu : PROPRE (aucun diagnostic AGENTGUARD005, AGENTGUARD005b,
// ni AGENTGUARD001).

using System;
using System.Threading.Tasks;

public static class AgentSyncOverAsyncConfigureAwaitExemptes
{
    // Cas 1 : le receiver de ConfigureAwait est une `ValueTask<int>`, pas
    // une `Task<int>`. Le filtre semantique verifie `MetadataName` et
    // namespace exacts -- `ValueTask` ne match pas. L'appel n'est PAS
    // signale : un ValueTask peut etre termine de maniere synchrone sans
    // etat-majeur, donc `.GetAwaiter().GetResult()` est legitime (pas de
    // deadlock possible).
    public static int ValueTaskSync()
    {
        ValueTask<int> tache = new ValueTask<int>(42);
        return tache.ConfigureAwait(false).GetAwaiter().GetResult();   // PROPRE (ValueTask)
    }

    // Cas 2 : ConfigureAwait sans literal bool (variable) -- le filtre
    // syntaxique requiert un literal bool pour borner le scope (cf. note
    // dans l'analyseur). On laisse passer ; l'analyse semantique exacte
    // de la condition excede le bug #13842 et abaisse le rapport
    // signal/bruit.
    public static string AvecCondition(bool garderContexte, string prompt)
    {
        return AppelerAsync(prompt).ConfigureAwait(garderContexte).GetAwaiter().GetResult();   // PROPRE (pas literal)
    }

    // Cas 3 : pas de GetResult dans la chaine -- la methode accede a
    // IsCompleted. Le filtre syntaxique de l'analyseur requiert
    // imperativement `GetResult`, donc cette forme passe.
    public static bool SansGetResult(Task<int> tache)
    {
        return tache.ConfigureAwait(false).GetAwaiter().IsCompleted;   // PROPRE (pas GetResult)
    }

    private static async Task<string> AppelerAsync(string prompt)
    {
        await Task.Delay(10);
        return prompt;
    }
}
