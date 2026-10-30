// Endpoints du lab : chaque classe porte ses routes. Aucune n'est
// referencee dans Program.cs -- elles sont decouvertes par la convention.

using Microsoft.AspNetCore.Mvc;

namespace ScrutorLab;

public sealed class HealthEndpoint : IEndpoint
{
    public void Map(IEndpointRouteBuilder app)
        => app.MapGet("/health", () => Results.Ok(new { status = "ok", endpoint = "HealthEndpoint" }));
}

public sealed class CatalogEndpoint(ICatalogService catalog) : IEndpoint
{
    public void Map(IEndpointRouteBuilder app)
        => app.MapGet("/catalog", () =>
        {
            var models = catalog.ModelIds();
            return Results.Ok(new { count = models.Count, models, endpoint = "CatalogEndpoint" });
        });
}

public sealed class EchoEndpoint : IEndpoint
{
    public void Map(IEndpointRouteBuilder app)
        => app.MapPost("/echo", ([FromBody] EchoRequest request) =>
            Results.Ok(new { received = request.Message, chars = request.Message.Length }));
}

public sealed record EchoRequest(string Message);

public sealed class StatsEndpoint(IStatsService stats) : IEndpoint
{
    public void Map(IEndpointRouteBuilder app)
        => app.MapGet("/stats", () =>
        {
            stats.Increment();
            return Results.Ok(new { requests = stats.Requests, endpoint = "StatsEndpoint" });
        });
}
