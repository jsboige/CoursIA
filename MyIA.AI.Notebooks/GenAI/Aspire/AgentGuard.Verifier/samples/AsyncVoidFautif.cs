// Terrain fautif pour AGENTGUARD002 : un agent "lance et oublie" un
// traitement d'ordre en ecrivant async void -- la signature ressemble a
// une async Task, mais la methode n'est pas attendable et ses exceptions
// ne sont observees par personne.

using System;
using System.Threading.Tasks;

public static class GestionCommandes
{
    // Genere par agent "pour aller vite" : async void hors handler.
    // Un diagnostic AGENTGUARD002 attendu ici.
    public static async void TraiterCommande(string orderId)
    {
        var resultat = await AppelerLlmAsync(orderId);
        Console.WriteLine(resultat);
    }

    private static async Task<string> AppelerLlmAsync(string orderId)
    {
        await Task.Delay(50);            // simule la latence de l'appel LLM
        return $"[LLM] commande {orderId} validee";
    }
}
