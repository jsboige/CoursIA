// Version corrigee du terrain AsyncVoidFautif.cs : la methode rend une
// Task -- elle devient attendable, composable, testable, et ses
// exceptions sont observees par l'appelant. Verdict attendu : PROPRE.

using System;
using System.Threading;
using System.Threading.Tasks;

public static class GestionCommandesCorrige
{
    // Le fix : async Task au lieu d'async void. L'appelant decide :
    // await (composee) ou _ = ... (assume, explicite) -- plus d'echapatoire.
    public static async Task TraiterCommandeAsync(
        string orderId, CancellationToken ct = default)
    {
        var resultat = await AppelerLlmAsync(orderId, ct);
        Console.WriteLine(resultat);
    }

    private static async Task<string> AppelerLlmAsync(
        string orderId, CancellationToken ct)
    {
        await Task.Delay(50, ct);        // simule la latence de l'appel LLM
        return $"[LLM] commande {orderId} validee";
    }
}
