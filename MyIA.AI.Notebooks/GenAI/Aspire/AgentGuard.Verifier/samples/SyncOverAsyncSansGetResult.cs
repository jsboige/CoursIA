// Faux positif pour AGENTGUARD005 : un awaiter custom expose
// `IsCompleted` mais pas `GetResult()` -- l'agent appelle `IsCompleted`
// directement. La forme n'est pas `.GetAwaiter().GetResult()`, donc
// l'analyseur laisse passer (le filtre syntaxique requiert GetResult).
//
// Verdict attendu : PROPRE (aucun diagnostic AGENTGUARD005).

using System;
using System.Threading.Tasks;

public static class AgentSansGetResult
{
    // Pas de GetResult() dans la chaine -- l'agent n'a meme pas compile
    // ce code en realite, mais la question est : si on ecrit
    // `tache.GetAwaiter().IsCompleted`, est-ce que AGENTGUARD005 crie ?
    // Non : le membre accede est IsCompleted, pas GetResult.
    public static bool VerifierAchevement(Task<int> tache)
    {
        return tache.GetAwaiter().IsCompleted;
    }
}
