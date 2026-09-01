// Terrain fautif pour AGENTGUARD005 : un agent genere du code "pour
// simplifier" en remplacant un `await tache` par
// `tache.GetAwaiter().GetResult()`. Le resultat est un blocage synchrone
// d'une `Task` non-generique -- exactement le meme defaut qu'AGENTGUARD001
// attrape via .Result, mais emprunte par un chemin syntaxique distinct
// (GetAwaiter() est appele explicitement).
//
// Verdict attendu : 1 diagnostic AGENTGUARD005 sur la ligne
// `Task.Delay(...).GetAwaiter().GetResult()`.

using System;
using System.Threading.Tasks;

public static class AgentSyncOverAsyncFautif
{
    public static int MesurerLatence()
    {
        // Genere par agent "pour simplifier" : au lieu d'etre async, la
        // methode "synchronise" la tache. C'est le defaut qu'AGENTGUARD005
        // doit attraper au build.
        Task.Delay(100).GetAwaiter().GetResult();   // AGENTGUARD005
        return 42;
    }
}
