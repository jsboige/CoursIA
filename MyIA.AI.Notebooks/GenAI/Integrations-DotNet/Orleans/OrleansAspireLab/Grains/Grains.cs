using Orleans;

namespace OrleansAspireLab.Grains;

// Deux familles de cles dans ce lab :
//  - IConversationGrain : IGrainWithGuidKey — identite GENEE par l'appelant
//    (Guid.NewGuid()). Aucun registre central de noms : deux conversations
//    ouvertes simultanement ne peuvent pas entrer en collision.
//  - ITokenCounterGrain : IGrainWithStringKey — cle NOMMEE (le nom du modele),
//    partagee entre toutes les conversations du cluster.
public interface IConversationGrain : IGrainWithGuidKey
{
    Task<int> AppendTurnAsync(string role, string content);
    Task<IReadOnlyList<string>> GetHistoryAsync();
    Task<int> TurnCountAsync();
    Task<string> SummaryAsync();
    Task RouteTokensAsync(string modelKey, int tokens);
    Task<int> GetTokenTotalAsync();
}

public interface ITokenCounterGrain : IGrainWithStringKey
{
    Task<int> RecordUsage(int tokens);
    Task<int> GetTotalAsync();
    Task<decimal> EstimateCostAsync(int centsPerThousandTokens);
}

public class ConversationGrain : Grain, IConversationGrain
{
    private readonly List<(string Role, string Content)> _turns = new();
    private int _tokenTotal;

    public Task<int> AppendTurnAsync(string role, string content)
    {
        _turns.Add((role, content));
        return Task.FromResult(_turns.Count);
    }

    public Task<IReadOnlyList<string>> GetHistoryAsync() =>
        Task.FromResult<IReadOnlyList<string>>(
            _turns.Select(t => $"{t.Role} : {t.Content}").ToList());

    public Task<int> TurnCountAsync() => Task.FromResult(_turns.Count);

    // Exercice 1 : retourner une ligne de resume au format exact
    // "<nb> tours, dernier role : <role>" (chaine vide si aucun tour).
    public Task<string> SummaryAsync()
    {
        Console.WriteLine("Exercice a completer");
        return Task.FromResult(string.Empty);  // TODO etudiant
    }

    // Exercice 2 : cumuler les tokens LOCALEMENT (_tokenTotal) ET deleguer au
    // grain ITokenCounterGrain identifie par modelKey (via la propriete protegee GrainFactory).
    public Task RouteTokensAsync(string modelKey, int tokens)
    {
        Console.WriteLine("Exercice a completer");
        return Task.CompletedTask;  // TODO etudiant
    }

    public Task<int> GetTokenTotalAsync() => Task.FromResult(_tokenTotal);
}

public class TokenCounterGrain : Grain, ITokenCounterGrain
{
    private int _total;

    public Task<int> RecordUsage(int tokens)
    {
        _total += tokens;
        return Task.FromResult(_total);
    }

    public Task<int> GetTotalAsync() => Task.FromResult(_total);

    // Exercice 3 : retourner le cout total en cents pour un tarif de
    // centsPerThousandTokens (arrondi a 2 decimales, Math.Round).
    public Task<decimal> EstimateCostAsync(int centsPerThousandTokens)
    {
        Console.WriteLine("Exercice a completer");
        return Task.FromResult(-1m);  // TODO etudiant
    }
}
