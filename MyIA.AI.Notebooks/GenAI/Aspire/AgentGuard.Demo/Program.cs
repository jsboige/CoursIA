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
