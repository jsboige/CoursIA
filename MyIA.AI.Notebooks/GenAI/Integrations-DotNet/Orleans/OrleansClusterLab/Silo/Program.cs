// Lab 04 : un silo Orleans configure par Aspire, expose en HTTP.
//
// Aucune ligne de clustering ni de stockage dans ce fichier : UseOrleans() lit la
// section "Orleans" de la configuration, que l'AppHost injecte dans chaque replique
// (ClusterId, ServiceId, ports, fournisseurs Redis designes par une cle de service).
// Comparer avec le lab 03, ou UseLocalhostClustering et AddRedisGrainStorage
// etaient ecrits a la main.

using System.Text.Json;
using Microsoft.Extensions.Options;
using Orleans.Configuration;
using Orleans.Placement;
using Orleans.Runtime;
using OrleansClusterLab;
using StackExchange.Redis;

var builder = WebApplication.CreateBuilder(args);

// Une connexion Redis par cle de service que la configuration Orleans cite. Si
// l'AppHost declare un Redis pour l'appartenance et un autre pour l'etat, le silo
// ouvre deux connexions sans qu'une ligne de ce fichier change.
var serviceKeys = ServiceKeys(builder.Configuration);
// AllowAdmin ouvre la commande INFO, dont l'endpoint /redis/persistence a besoin :
// un choix de laboratoire (introspection), pas un reglage de production.
foreach (var key in serviceKeys.Values.Distinct())
{
    builder.AddKeyedRedisClient(key, configureOptions: options => options.AllowAdmin = true);
}
builder.UseOrleans();                    // tout le reste vient de la configuration injectee
var app = builder.Build();

const string ServicePrefix = "orleans-cluster-lab/";

// Qui repond : la replique, son adresse de silo, son process.
app.MapGet("/whoami", (ILocalSiloDetails silo) =>
    new { replica = SiloReplica.Name, silo = silo.SiloAddress.ToString(), pid = Environment.ProcessId });

// La configuration Orleans recue d'Aspire, et la replique qui l'a recue. Seule la
// section "Orleans" est rendue : les chaines de connexion Redis (qui portent le mot de
// passe) n'en font pas partie.
app.MapGet("/config", (IConfiguration configuration) => new
{
    replica = SiloReplica.Name,
    settings = configuration.GetSection("Orleans").AsEnumerable(makePathsRelative: true)
        .Where(kv => kv.Value is not null)
        .OrderBy(kv => kv.Key, StringComparer.Ordinal)
        .Select(kv => $"{kv.Key} = {kv.Value}"),
});

// Les silos actifs du cluster, vus par le runtime Orleans.
app.MapGet("/cluster", async (IGrainFactory grains) =>
{
    var hosts = await grains.GetGrain<IManagementGrain>(0).GetHosts(onlyActive: true);
    return hosts.Select(h => $"{h.Key} {h.Value}").OrderBy(s => s, StringComparer.Ordinal);
});

// Ce que le cluster a ecrit dans chaque Redis : les cles du service, sans leurs valeurs.
app.MapGet("/redis/keys", async (IServiceProvider services) =>
{
    var result = new SortedDictionary<string, List<string>>(StringComparer.Ordinal);
    foreach (var key in serviceKeys.Values.Distinct())
    {
        var server = services.GetRequiredKeyedService<IConnectionMultiplexer>(key).GetServers().First();
        var keys = new List<string>();
        await foreach (var k in server.KeysAsync(pattern: ServicePrefix + "*"))
        {
            keys.Add(k.ToString());
        }
        keys.Sort(StringComparer.Ordinal);
        result[key] = keys;
    }
    return result;
});

// La table d'appartenance : un hash Redis, un champ par silo ayant rejoint le cluster
// (plus un champ "Version"). Chaque valeur est une entree JSON ; on en rend l'essentiel.
app.MapGet("/redis/members", async (IServiceProvider services) =>
{
    var db = services.GetRequiredKeyedService<IConnectionMultiplexer>(serviceKeys["clustering"]).GetDatabase();
    var fields = await db.HashGetAllAsync(ServicePrefix + "members/cluster-lab");
    return fields
        .Where(f => f.Name.ToString() != "Version")
        .Select(f =>
        {
            using var entry = JsonDocument.Parse(f.Value.ToString());
            var root = entry.RootElement;
            var status = (SiloStatus)root.GetProperty("Status").GetInt32();
            return $"{f.Name} status={status} demarre={root.GetProperty("StartTime").GetDateTime():HH:mm:ss}Z";
        })
        .OrderBy(s => s, StringComparer.Ordinal);
});

// Ce que le Redis de l'etat a mis sur disque : les ecritures pas encore dans un
// instantane RDB sont celles qu'un arret du conteneur ferait perdre.
app.MapGet("/redis/persistence", async (IServiceProvider services) =>
{
    var server = services.GetRequiredKeyedService<IConnectionMultiplexer>(serviceKeys["sessions"]).GetServers().First();
    var info = (await server.InfoAsync("persistence")).SelectMany(g => g)
        .ToDictionary(kv => kv.Key, kv => kv.Value);
    return new
    {
        serviceKey = serviceKeys["sessions"],
        changesSinceLastSave = int.Parse(info["rdb_changes_since_last_save"]),
        lastSaveAgeSeconds = DateTimeOffset.UtcNow.ToUnixTimeSeconds() - long.Parse(info["rdb_last_save_time"]),
        aofEnabled = info["aof_enabled"] == "1",
    };
});

// Le placement : la strategie par defaut du runtime, ses reglages, et l'attribut
// eventuellement pose sur la classe du grain de session (exercice 2).
app.MapGet("/placement", (IServiceProvider services, IOptions<ResourceOptimizedPlacementOptions> resource) => new
{
    defaultStrategy = services.GetService<PlacementStrategy>()?.GetType().Name ?? "(aucune)",
    sessionGrainAttribute = typeof(SessionGrain).GetCustomAttributes(typeof(PlacementAttribute), inherit: true)
        .Select(a => a.GetType().Name).FirstOrDefault() ?? "(aucun)",
    localSiloPreferenceMargin = resource.Value.LocalSiloPreferenceMargin,
    weights = new
    {
        cpuUsage = resource.Value.CpuUsageWeight,
        memoryUsage = resource.Value.MemoryUsageWeight,
        availableMemory = resource.Value.AvailableMemoryWeight,
        maxAvailableMemory = resource.Value.MaxAvailableMemoryWeight,
        activationCount = resource.Value.ActivationCountWeight,
    },
});

// Les reglages de detection de panne : ils fixent le delai entre la mort d'un silo
// et le moment ou le reste du cluster le declare mort (et reactive ses grains ailleurs).
app.MapGet("/membership/options", (IOptions<ClusterMembershipOptions> options) => new
{
    probeTimeout = options.Value.ProbeTimeout.TotalSeconds,
    numMissedProbesLimit = options.Value.NumMissedProbesLimit,
    numProbedSilos = options.Value.NumProbedSilos,
    numVotesForDeathDeclaration = options.Value.NumVotesForDeathDeclaration,
    iAmAliveTablePublishTimeout = options.Value.IAmAliveTablePublishTimeout.TotalSeconds,
});

app.MapPost("/session/{id}/turn", async (string id, string text, IGrainFactory grains) =>
    Respond(await grains.GetGrain<ISessionGrain>(id).AppendTurnAsync(text)));

app.MapGet("/session/{id}", async (string id, IGrainFactory grains) =>
    Respond(await grains.GetGrain<ISessionGrain>(id).GetReceiptAsync()));

app.MapPost("/session/{id}/once", async (string id, string requestId, string text, IGrainFactory grains) =>
    Respond(await grains.GetGrain<ISessionGrain>(id).AppendOnceAsync(requestId, text)));

app.Run();

// Les cles de service citees par la configuration Orleans, par usage :
// "clustering" pour la table d'appartenance, le nom du fournisseur pour un stockage.
static Dictionary<string, string> ServiceKeys(IConfiguration configuration)
{
    var orleans = configuration.GetSection("Orleans");
    var keys = new Dictionary<string, string>(StringComparer.Ordinal);
    if (orleans["Clustering:ServiceKey"] is { } clustering)
    {
        keys["clustering"] = clustering;
    }
    foreach (var storage in orleans.GetSection("GrainStorage").GetChildren())
    {
        if (storage["ServiceKey"] is { } key)
        {
            keys[storage.Key] = key;
        }
    }
    return keys;
}

// Le recu, complete par la replique qui a recu la requete HTTP.
static object Respond(TurnReceipt r) => new
{
    httpReplica = SiloReplica.Name,
    activationReplica = r.ActivationReplica,
    activationSilo = r.ActivationSilo,
    activationPid = r.ActivationPid,
    turns = r.TurnCount,
    etag = r.ETag,
};
