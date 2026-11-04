// Services metier consommes par les endpoints : c'est la contrepartie des
// "dependances" (Depends) de FastAPI, resolues par DI au lieu d'etre
// injectees par le framework de routing.

namespace ScrutorLab;

/// <summary>Catalogue minimal d'exemple, implémentation singleton.</summary>
public interface ICatalogService
{
    IReadOnlyList<string> ModelIds();
}

public sealed class CatalogService : ICatalogService
{
    private static readonly string[] Models =
    [
        "qwen2.5-vl-7b",
        "llama-3.1-8b-instruct",
        "mistral-nemo-12b",
    ];

    public IReadOnlyList<string> ModelIds() => Models;
}

/// <summary>Compteur d'appels, implémentation singleton observable.</summary>
public interface IStatsService
{
    long Requests { get; }
    void Increment();
}

public sealed class StatsService : IStatsService
{
    private long _requests;
    public long Requests => Interlocked.Read(ref _requests);
    public void Increment() => Interlocked.Increment(ref _requests);
}
