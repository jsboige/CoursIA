// Terrain d'exemption pour AGENTGUARD002 : un gestionnaire d'evenement
// AUTHENTIQUE. Le contrat C# des handlers EXIGE void -- on ne peut pas
// rendre une Task a un abonne d'evenement. async void y est donc la forme
// canonique, non un defaut. Deux signatures exemptees :
//   - (object sender, EventArgs e) : la forme canonique ;
//   - (object sender, ProgressEventArgs e) : EventArgs DERIVE, le modele
//     semantique remonte la chaine d'heritage.
// Verdict attendu : PROPRE -- c'est la demonstration que l'exemption est
// semantique (heritage), pas lexicale (nom du parametre).

using System;
using System.Threading.Tasks;

public sealed class ProgressEventArgs : EventArgs
{
    public int Pourcent { get; init; }
}

public sealed class OrchestrateurAgent
{
    public event EventHandler<ProgressEventArgs>? Progress;

    // Handler canonique (object, EventArgs) : exempt.
    public async void OnTimerElapsed(object sender, EventArgs e)
    {
        var resultat = await AppelerLlmAsync("tick");
        Console.WriteLine(resultat);
    }

    // Handler a EventArgs derive (object, ProgressEventArgs) : exempt --
    // l'exemption traverse la chaine d'heritage du second parametre.
    public async void OnProgressReported(object sender, ProgressEventArgs e)
    {
        var resultat = await AppelerLlmAsync($"progression {e.Pourcent}%");
        Console.WriteLine(resultat);
    }

    // L'evenement est bien utilise : c'est lui qui rend ces handlers
    // LEGITIMES -- le contrat C# des abonnes EXIGE void.
    public void SimulerProgress()
    {
        Progress?.Invoke(this, new ProgressEventArgs { Pourcent = 50 });
    }

    private static async Task<string> AppelerLlmAsync(string prompt)
    {
        await Task.Delay(50);            // simule la latence de l'appel LLM
        return $"[LLM] {prompt}";
    }
}
