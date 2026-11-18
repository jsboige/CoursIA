// Program.cs du lab : 6 lignes utiles. Comparez a un Program.cs de
// minimal API classique qui enumererait chaque MapGet un par un -- ici,
// la convention ScanEndpoints + MapEndpoints fait l'orchestration.

using Microsoft.Extensions.DependencyInjection.Extensions;
using ScrutorLab;

var builder = WebApplication.CreateBuilder(args);

// Enregistrement des services metier (la DI classique), puis la convention.
builder.Services.TryAddSingleton<ICatalogService, CatalogService>();
builder.Services.TryAddSingleton<IStatsService, StatsService>();
builder.Services.ScanEndpoints();   // decouverte de toutes les classes IEndpoint

// Port dynamique : le notebook pilote ce process et lit l'URL sur stdout.
builder.WebHost.UseUrls("http://127.0.0.1:0");

var app = builder.Build();

app.Lifetime.ApplicationStarted.Register(() =>
{
    // WebApplication.Urls est peuple au demarrage (port dynamique :0).
    var url = app.Urls.FirstOrDefault() ?? "http://?";
    // Marqueur machine-lisible pour le notebook (precedent serie : 09-Aspire).
    Console.WriteLine($"LISTENING::{url}");
});

// Trace de la decouverte : ce que la convention a trouve, sans l'enumerer.
foreach (var endpoint in app.Services.GetServices<IEndpoint>())
    Console.WriteLine($"ENDPOINT::{endpoint.GetType().Name}");

app.MapEndpoints();                  // mapping automatique de tous les endpoints

app.Run();
