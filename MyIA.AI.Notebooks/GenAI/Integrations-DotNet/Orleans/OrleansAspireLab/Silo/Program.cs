// Silo Orleans du lab 02 — resource ORCHESTREE par l'AppHost Aspire (aspire run),
// contrairement au lab 01 ou le silo etait un process ad hoc lance par le notebook.
// Ports Orleans explicites : le client (autre process) s'y connecte directement.

using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using Orleans;

// Note : la config que l'AppHost injecte a ce process (WithReference(orleans))
// se lit dans les evenements de l'AppHost — le log CLI/Dashboard trace
// "Service silo-orleans-gateway is now in state Ready" et son pendant silo :
// c'est la preuve que la declaration AddOrleans est RESOLUE vers ce process.

using var host = new HostBuilder()
    .UseOrleans(silo =>
    {
        // Clustering dev localhost sur ports explicites (defaults Orleans :
        // silo 11111, gateway 30000) — le ClientDriver s'y connecte.
        silo.UseLocalhostClustering(
            gatewayPort: 30000,
            siloPort: 11111,
            serviceId: "orleans-aspire-lab",
            clusterId: "agent-cluster");
    })
    .ConfigureLogging(logging => logging.SetMinimumLevel(LogLevel.Warning))
    .Build();

await host.StartAsync();
Console.WriteLine("[silo] demarre (gateway 30000, silo 11111) — orchestre par l'AppHost Aspire");

await host.WaitForShutdownAsync();
