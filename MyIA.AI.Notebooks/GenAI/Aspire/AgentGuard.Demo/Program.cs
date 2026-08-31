// Terrain fautif : copie de demo du motif StreamingAgent.App (notebook 04).
// Un worker d'agent consomme une Channel -- motif canonique de la serie --
// mais ici le code genere "dans le style synchrone" BLOQUE la tache d'appel
// au LLM avec .Result au lieu de l'attendre. C'est le defaut que l'analyseur
// AGENTGUARD001 doit attraper au `dotnet build` (ce fichier ne leve PAS
// d'exception : le blocage ne deadlock ici qu'un contexte reduit -- le
// notebook explique pourquoi le pattern reste mortel en production).

using System;
using System.Threading.Channels;
using System.Threading.Tasks;

var channel = Channel.CreateUnbounded<string>();
_ = Producer.ProduceAsync(channel.Writer, "traduis cette phrase en anglais");

Console.WriteLine(AgentWorker.TranslateSync(channel.Reader));

public static class AgentWorker
{
    // Genere par agent "pour simplifier" : la tache async est bloquee.
    // Deux blocages .Result -- deux diagnostics attendus au build.
    public static string TranslateSync(ChannelReader<string> inbound)
    {
        var prompt = inbound.ReadAsync().AsTask().Result;   // AGENTGUARD001
        return CallLlmAsync(prompt).Result;                 // AGENTGUARD001
    }

    private static async Task<string> CallLlmAsync(string prompt)
    {
        await Task.Delay(50);            // simule la latence de l'appel LLM
        return $"[LLM] {prompt}";
    }
}

public static class Producer
{
    public static async Task ProduceAsync(ChannelWriter<string> writer, string prompt)
        => await writer.WriteAsync(prompt);
}

// Second terrain fautif (AGENTGUARD002) : le meme agent, une autre vitesse.
// "Lancer et oublier" un traitement en ecrivant async void -- la signature
// ressemble a une async Task, mais la methode n'est pas attendable et ses
// exceptions ne sont observees par personne. Un diagnostic AGENTGUARD002
// attendu au build (et aucun ici n'est un handler d'evenement : pas de
// signature (object, EventArgs)).
public static class AgentFireAndForget
{
    public static void Demarrer()
    {
        SurveillerCanalAsync();            // "rendu la main" -- silencieusement
    }

    // Genere par agent "pour simplifier" : async void hors handler.
    public static async void SurveillerCanalAsync()
    {
        await Task.Delay(200);             // simule une boucle de surveillance
        // Si l'appel LLM leve ici, personne ne l'observe : process mort.
    }
}

// Troisieme terrain fautif (AGENTGUARD003) : le meme agent, troisieme
// vitesse. `Task.Run(() => ...)` est appele comme enonce autonome -- la
// signature est honnete (Task, pas void), mais le retour est jete a la
// corbeille : pas de await, pas d'affectation, pas de `_ =`, pas de
// return. La tache s'execute en arriere-plan, ses exceptions ne sont
// observees par personne. Un diagnostic AGENTGUARD003 attendu au build
// (et c'est la seule forme signalee : `await Task.Run(...)`, `var t =
// Task.Run(...)`, `_ = Task.Run(...)` et `return Task.Run(...)` sont
// exemptes).
public static class AgentTaskRunFire
{
    public static void Demarrer()
    {
        Task.Run(() => Console.WriteLine("ping"));   // AGENTGUARD003
    }
}

// Quatrieme terrain fautif (AGENTGUARD004) : la requete fournit un
// CancellationToken, et la cible sait le recevoir, mais le code genere omet
// l'argument optionnel. L'annulation est perdue au milieu de la chaine.
public static class AgentCancellation
{
    public static async Task RepondreAsync(
        string prompt,
        System.Threading.CancellationToken cancellationToken)
    {
        await CallLlmAsync(prompt);                    // AGENTGUARD004
    }

    private static Task<string> CallLlmAsync(
        string prompt,
        System.Threading.CancellationToken cancellationToken = default)
        => Task.FromResult($"[LLM] {prompt}");
}

// Cinquieme terrain fautif (AGENTGUARD005) : variante syntaxique d'
// AGENTGUARD001, meme defaut semantique. Au lieu de `.Result`, l'agent
// decompile explicitement la machine a etats de la tache :
// `tache.GetAwaiter().GetResult()`. Meme consequence en production
// (deadlock sur un SynchronizationContext), mais un chemin syntaxique
// distinct qui justifie un analyseur dedie -- AGENTGUARD001 ne regarde
// que `.Result` / `.Wait()`. Diagnostic attendu sur la derniere ligne.
public static class AgentSyncOverAsync
{
    // Genere par agent "pour eviter un await" : la tache est "synchronisee"
    // en traversant manuellement la machine a etats. C'est exactement le
    // defaut que AGENTGUARD005 attrape.
    public static string ReponseSynchrone(string prompt)
    {
        return CallLlmAsync(prompt).GetAwaiter().GetResult();   // AGENTGUARD005
    }

    private static async Task<string> CallLlmAsync(string prompt)
    {
        await Task.Delay(50);
        return $"[LLM] {prompt}";
    }
}

// Sixieme terrain fautif (AGENTGUARD005b) : variante
// `ConfigureAwait(false).GetAwaiter().GetResult()`, ecappee au filtre
// semantique d'AGENTGUARD005 (le receiver du GetAwaiter y est de type
// `ConfiguredTaskAwaitable`, pas `Task`). L'agent genere cette forme en
// CROYANT que `ConfigureAwait(false)` "rend ca safe". Faux : ConfigureAwait
// reduit la capture du SynchronizationContext, mais le
// `.GetAwaiter().GetResult()` BLOQUE TOUJOURS le thread -- le
// sync-over-async reste entier. C'est precisement la confusion que la
// regle AGENTGUARD005b doit denoncer. Deux diagnostics attendus : un par
// ligne fautive (deux formes explicitement testees : `ConfigureAwait(false)`
// et `ConfigureAwait(true)`).
public static class AgentSyncOverAsyncConfigureAwait
{
    // Forme "rassurante" classique : l'agent a lu sur Stack Overflow que
    // ConfigureAwait(false) est une bonne pratique et l'a ajoute "pour
    // etre safe". Le defaut est exactement le meme que la variante
    // nue -- diagnostic AGENTGUARD005b attendu.
    public static string ReponseSynchroneSafeFalse(string prompt)
    {
        return CallLlmAsync(prompt).ConfigureAwait(false).GetAwaiter().GetResult();   // AGENTGUARD005b
    }

    // Forme `true` (explicite) -- meme defaut, l'analyseur doit le voir
    // aussi (le literal n'est pas blanchi : seul compte le pattern).
    public static string ReponseSynchroneSafeTrue(string prompt)
    {
        return CallLlmAsync(prompt).ConfigureAwait(true).GetAwaiter().GetResult();    // AGENTGUARD005b
    }

    private static async Task<string> CallLlmAsync(string prompt)
    {
        await Task.Delay(50);
        return $"[LLM] {prompt}";
    }
}
