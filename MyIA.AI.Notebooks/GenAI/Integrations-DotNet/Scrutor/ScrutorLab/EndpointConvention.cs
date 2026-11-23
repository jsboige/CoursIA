// Convention d'orchestration des endpoints : contrat + scan DI.
// Ce fichier est le coeur du lab : il definit la convention que le notebook
// enseigne. Aucun endpoint n'est reference explicitement dans Program.cs :
// ils sont decouverts par scan d'assemblement (Scrutor).

using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.DependencyInjection.Extensions;

namespace ScrutorLab;

/// <summary>
/// Contrat d'un endpoint minimal API. Une classe implementant cette
/// interface est automatiquement enregistree puis mappee par convention.
/// </summary>
public interface IEndpoint
{
    /// <summary>Mappe les routes de cet endpoint sur le routeur minimal API.</summary>
    void Map(IEndpointRouteBuilder app);
}

/// <summary>
/// Extensions d'enregistrement par convention : scan de l'assemblement
/// courant a la recherche des implementations de <see cref="IEndpoint"/>,
/// puis mapping automatique au demarrage.
/// </summary>
public static class EndpointConventionExtensions
{
    /// <summary>
    /// Enregistre toutes les classes implementant IEndpoint de l'assemblement
    /// donne, avec la duree de vie demandee (Transient par defaut : un
    /// endpoint est un adaptateur stateless, la duree de vie porte par les
    /// services qu'il consomme).
    /// </summary>
    public static IServiceCollection ScanEndpoints(
        this IServiceCollection services,
        ServiceLifetime lifetime = ServiceLifetime.Transient)
        => services.Scan(scan => scan
            .FromAssemblyOf<IEndpoint>()
            .AddClasses(classes => classes.AssignableTo<IEndpoint>())
            .As<IEndpoint>()
            .WithLifetime(lifetime));

    /// <summary>
    /// Mappe tous les endpoints enregistres : resolve chaque IEndpoint et
    /// laisse la classe poser ses propres routes. C'est l'equivalent
    /// structurel d'un include_router de FastAPI, pilote par la DI.
    /// </summary>
    public static IEndpointRouteBuilder MapEndpoints(this IEndpointRouteBuilder app)
    {
        // MapEndpoints est appele une fois au demarrage : on consomme le
        // provider racine pour resoudre les descripteurs, puis on mappe.
        using var scope = app.ServiceProvider.CreateScope();
        foreach (var endpoint in scope.ServiceProvider.GetServices<IEndpoint>())
        {
            endpoint.Map(app);
        }
        return app;
    }
}
