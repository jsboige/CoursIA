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
