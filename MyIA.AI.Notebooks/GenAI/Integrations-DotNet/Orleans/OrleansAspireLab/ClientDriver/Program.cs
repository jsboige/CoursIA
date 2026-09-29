// ClientDriver : process SEPARE du silo, connecte au gateway Orleans (30000).
// Contrairement au lab 01 (silo + client dans le meme process), ici le client
// meurt entre chaque scenario — l'etat survit parce qu'il vit dans le silo.
// Scenarios : demo | ex1 | ex2 | resume <guid>

using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using Orleans;
using OrleansAspireLab.Grains;

var scenario = args.Length > 0 ? args[0] : "demo";
var resumeGuid = args.Length > 1 && Guid.TryParse(args[1], out var g) ? g : (Guid?)null;

var builder = Host.CreateApplicationBuilder(args);
builder.Logging.AddFilter("Orleans", LogLevel.Warning);
builder.Services.AddOrleansClient(cb => cb.UseLocalhostClustering(
    gatewayPort: 30000,
    serviceId: "orleans-aspire-lab",
    clusterId: "agent-cluster"));
using var host = builder.Build();
await host.StartAsync();
var client = host.Services.GetRequiredService<IClusterClient>();
Console.WriteLine($"[client] connecte au gateway 30000, scenario={scenario}");

switch (scenario)
{
    case "demo":
        await RunDemoAsync(client);
        break;
    case "ex1":
        await RunExercise1Async(client);
        break;
    case "ex2":
        await RunExercise2Async(client);
        break;
    case "ex3":
        await RunExercise3Async(client);
        break;
    case "resume":
        if (resumeGuid is null) { Console.WriteLine("[erreur] usage : resume <guid>"); break; }
        await RunResumeAsync(client, resumeGuid.Value);
        break;
    default:
        Console.WriteLine($"[erreur] scenario inconnu : {scenario}");
        break;
}

await host.StopAsync();
return 0;

static async Task RunDemoAsync(IClusterClient client)
{
    // 1. Identites GENEREES : deux conversations ouvertes simultanement.
    var idA = Guid.NewGuid();
    var idB = Guid.NewGuid();
    var convA = client.GetGrain<IConversationGrain>(idA);
    var convB = client.GetGrain<IConversationGrain>(idB);

    var toursA = await convA.AppendTurnAsync("user", "Genere un plan de cours sur Orleans");
    toursA = await convA.AppendTurnAsync("assistant", "1. Grains 2. Identites 3. Co-host Aspire");
    var toursB = await convB.AppendTurnAsync("user", "Traduis ce plan en anglais");

    Console.WriteLine($"[demo] conversation A : id={idA} -> {toursA} tours");
    Console.WriteLine($"[demo] conversation B : id={idB} -> {toursB} tour");
    Console.WriteLine($"[demo] identites distinctes : {idA != idB} (aucun registre de noms sollicite)");

    // 2. Relecture par l'identite : le Guid EST l'adresse du grain.
    var convAAgain = client.GetGrain<IConversationGrain>(idA);
    var toursAAgain = await convAAgain.TurnCountAsync();
    Console.WriteLine($"[demo] nouvelle reference sur le meme Guid -> {toursAAgain} tours "
        + (toursAAgain == toursA ? "(etat conserve, l'identite est l'adresse)" : "(etat perdu ?)"));

    // 3. Compteur a cle NOMMEE : partage entre toutes les conversations.
    var counter = client.GetGrain<ITokenCounterGrain>("qwen3-coder");
    await counter.RecordUsage(650);
    var total = await counter.RecordUsage(210);
    Console.WriteLine($"[demo] compteur 'qwen3-coder' (cle nommee) -> {total} tokens cumules");

    // 4. Le guid a reprendre pour le scenario resume.
    Console.WriteLine($"[demo] guid a reprendre : {idA}");
}

static async Task RunExercise1Async(IClusterClient client)
{
    var id = Guid.NewGuid();
    var conv = client.GetGrain<IConversationGrain>(id);
    await conv.AppendTurnAsync("user", "Premiere question");
    await conv.AppendTurnAsync("assistant", "Premiere reponse");
    await conv.AppendTurnAsync("user", "Deuxieme question");
    var summary = await conv.SummaryAsync();
    Console.WriteLine($"[ex1] resume -> \"{summary}\"");
    Console.WriteLine(string.IsNullOrEmpty(summary)
        ? "[ex1] SummaryAsync est encore le stub : complete Grains.cs puis relance cette cellule"
        : "[ex1] resume retourne par l'etudiant");
}

static async Task RunExercise2Async(IClusterClient client)
{
    var convA = client.GetGrain<IConversationGrain>(Guid.NewGuid());
    var convB = client.GetGrain<IConversationGrain>(Guid.NewGuid());

    await convA.RouteTokensAsync("qwen3-coder", 500);
    await convA.RouteTokensAsync("qwen3-coder", 300);
    await convB.RouteTokensAsync("qwen3-coder", 900);

    var counterTotal = await client.GetGrain<ITokenCounterGrain>("qwen3-coder").GetTotalAsync();
    var totalA = await convA.GetTokenTotalAsync();
    var totalB = await convB.GetTokenTotalAsync();
    Console.WriteLine($"[ex2] cumul local A={totalA} (attendu 800), B={totalB} (attendu 900)");
    Console.WriteLine(counterTotal >= 1700 && totalA == 800 && totalB == 900
        ? "[ex2] routage coherent : chaque conversation cumule ET le compteur du modele aussi"
        : "[ex2] RouteTokensAsync est encore le stub : complete Grains.cs puis relance cette cellule");
}

static async Task RunExercise3Async(IClusterClient client)
{
    var counter = client.GetGrain<ITokenCounterGrain>("estimate-lab");
    await counter.RecordUsage(1200);
    await counter.RecordUsage(340);
    await counter.RecordUsage(85);
    var cost = await counter.EstimateCostAsync(centsPerThousandTokens: 40);
    Console.WriteLine($"[ex3] total={(1200 + 340 + 85)} tokens, cout estime a 40 cents/1k -> {cost} cents");
    Console.WriteLine(cost == -1m
        ? "[ex3] EstimateCostAsync est encore le stub : complete Grains.cs puis relance cette cellule"
        : "[ex3] estimation retournee par l'etudiant");
}

static async Task RunResumeAsync(IClusterClient client, Guid id)
{
    var conv = client.GetGrain<IConversationGrain>(id);
    var tours = await conv.TurnCountAsync();
    Console.WriteLine($"[resume] conversation {id} -> {tours} tours retrouves");
    foreach (var line in await conv.GetHistoryAsync())
        Console.WriteLine($"[resume] | {line}");
    Console.WriteLine("[resume] le process client precedent est mort : l'etat vivait dans le silo");
}
