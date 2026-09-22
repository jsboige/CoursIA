// Grains du lab Orleans : acteurs stateful pour workloads IA.
// Domaine coherant avec la serie The Unexpected AI Stack (jobs de transcription,
// sessions d'agents, compteurs de tokens).

using Orleans;

namespace OrleansAgentLab;

/// <summary>Compteur de tokens par modele, avec estimation de cout (exercice 1).</summary>
public interface ITokenCounterGrain : IGrainWithStringKey
{
    /// <summary>Enregistre une consommation et retourne le total cumule du grain.</summary>
    Task<long> RecordUsage(int tokens);

    /// <summary>Total cumule sans mutation.</summary>
    Task<long> GetTotalAsync();

    /// <summary>Estimation du cout en cents pour un tarif donne (centimes / 1k tokens).
    /// Exercice 1 : a completer par l'etudiant.</summary>
    Task<decimal> EstimateCostAsync(int centsPerThousandTokens);
}

/// <summary>Session d'agent conversationnelle : historique ordonne en memoire du grain.</summary>
public interface IAgentSessionGrain : IGrainWithStringKey
{
    /// <summary>Ajoute un tour (role + extrait) et retourne le nombre de tours cumules.</summary>
    Task<int> AppendTurnAsync(string role, string excerpt);

    /// <summary>Historique complet (role : extrait), dans l'ordre d'arrivee.</summary>
    Task<IReadOnlyList<string>> GetHistoryAsync();

    /// <summary>Dernier extrait enregistre, ou une chaine vide si aucun tour.
    /// Exercice 2 : a completer par l'etudiant.</summary>
    Task<string> LastExcerptAsync();

    /// <summary>Consommation totale de tokens declaree pour la session.</summary>
    Task<long> GetTokenTotalAsync();

    /// <summary>Declare une consommation de tokens pour la session (appele par le routeur).
    /// Exercice 3 : a completer par l'etudiant (le routeur doit rester coherents entre
    /// sessions multiples).</summary>
    Task RouteTokensAsync(string modelKey, int tokens);
}

public sealed class TokenCounterGrain : Grain, ITokenCounterGrain
{
    private long _total;

    public Task<long> RecordUsage(int tokens)
    {
        // Le modele acteur garantit qu'un seul appel a la fois entre ici :
        // l'increment n'a pas besoin de verrou ni d'Interlocked.
        _total += tokens;
        return Task.FromResult(_total);
    }

    public Task<long> GetTotalAsync() => Task.FromResult(_total);

    public Task<decimal> EstimateCostAsync(int centsPerThousandTokens)
    {
        // Exercice 1 : calculer le cout total = _total * centsPerThousandTokens / 1000m.
        // Indice : arrondir a 2 decimales avec Math.Round(..., 2).
        // Etape 1 : lire _total (deja en portee).
        // Etape 2 : appliquer le tarif lineaire.
        // Etape 3 : retourner Task.FromResult(...) du resultat.
        Console.WriteLine("Exercice 1 a completer : EstimateCostAsync retourne -1 par defaut");
        return Task.FromResult(-1m);
    }
}

public sealed class AgentSessionGrain : Grain, IAgentSessionGrain
{
    private readonly List<string> _history = [];
    private long _tokenTotal;

    public Task<int> AppendTurnAsync(string role, string excerpt)
    {
        _history.Add($"{role} : {excerpt}");
        return Task.FromResult(_history.Count);
    }

    public Task<IReadOnlyList<string>> GetHistoryAsync() =>
        Task.FromResult<IReadOnlyList<string>>(_history);

    public Task<string> LastExcerptAsync()
    {
        // Exercice 2 : retourner le dernier extrait enregistre (chaine vide si aucun tour).
        // Indice : _history est une List<string> de la forme "role : extrait".
        // Etape 1 : verifier le compte (_history.Count == 0 -> chaine vide).
        // Etape 2 : extraire la partie apres " : " du dernier element.
        Console.WriteLine("Exercice 2 a completer : LastExcerptAsync retourne une chaine vide par defaut");
        return Task.FromResult(string.Empty);
    }

    public Task<long> GetTokenTotalAsync() => Task.FromResult(_tokenTotal);

    public async Task RouteTokensAsync(string modelKey, int tokens)
    {
        // Exercice 3 : cumuler dans la session ET router vers le compteur du modele.
        // Indice : la propriete protegee GrainFactory (heritee de Grain) donne le
        // compteur du modele : GrainFactory.GetGrain<ITokenCounterGrain>(modelKey) ;
        // RecordUsage y cumule.
        // Etape 1 : cumuler tokens dans _tokenTotal.
        // Etape 2 : recuperer le grain compteur du modele via la cle modelKey.
        // Etape 3 : lui deleguer RecordUsage(tokens) avec await.
        Console.WriteLine("Exercice 3 a completer : RouteTokensAsync ne route rien par defaut");
        await Task.CompletedTask;
    }
}
