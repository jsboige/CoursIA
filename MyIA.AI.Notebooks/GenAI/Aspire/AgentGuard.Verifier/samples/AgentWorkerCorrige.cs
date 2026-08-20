// Version corrigee du terrain fautif (AgentGuard.Demo/Program.cs) :
// le worker attend la tache au lieu de la bloquer. C'est la version
// attendue "propre" au verdict du Verifier.

using System;
using System.Threading;
using System.Threading.Channels;
using System.Threading.Tasks;

public static class AgentWorkerCorrige
{
    // Le fix : async/await de bout en bout. Le thread rend la main pendant
    // l'attente au lieu de se bloquer -- plus de deadlock possible, et le
    // pipeline reste fluide sous charge.
    public static async Task<string> TranslateAsync(
        ChannelReader<string> inbound, CancellationToken ct = default)
    {
        var prompt = await inbound.ReadAsync(ct);
        return await CallLlmAsync(prompt, ct);
    }

    private static async Task<string> CallLlmAsync(string prompt, CancellationToken ct)
    {
        await Task.Delay(50, ct);       // simule la latence de l'appel LLM
        return $"[LLM] {prompt}";
    }
}
