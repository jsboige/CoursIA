// Lab Orleans : silo co-hosté (silo + client dans le meme process).
// Scenarios deterministes pilotes depuis le notebook 01-Orleans-Grains-Agents.ipynb.

using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using Orleans;
using OrleansAgentLab;

var scenario = args.Length > 0 ? args[0] : "demo";

using var host = new HostBuilder()
    .UseOrleans(silo =>
    {
        // Silo en memoire, sans clustering externe : le pattern "co-host" du billet.
        silo.UseLocalhostClustering(serviceId: "orleans-agent-lab", clusterId: "agent-lab");
    })
    .ConfigureLogging(logging => logging.SetMinimumLevel(LogLevel.Warning))
    .Build();

await host.StartAsync();
var client = host.Services.GetRequiredService<IGrainFactory>();
Console.WriteLine($"[silo] demarre, scenario={scenario}");

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
    default:
        Console.WriteLine($"[erreur] scenario inconnu : {scenario}");
        break;
}

await host.StopAsync();
return 0;

static async Task RunDemoAsync(IGrainFactory client)
{
    // 1. Sessions d'agents : chaque session est un grain, son etat vit dans le grain.
    var sessionA = client.GetGrain<IAgentSessionGrain>("session-alpha");
    var sessionB = client.GetGrain<IAgentSessionGrain>("session-beta");

    var toursA = await sessionA.AppendTurnAsync("user", "Resume la reunion de ce matin en 3 points");
    toursA = await sessionA.AppendTurnAsync("assistant", "1. Objectifs du trimestre... 2. Projet client... 3. Echéances");
    var toursB = await sessionB.AppendTurnAsync("user", "Traduis le compte rendu en anglais");

    Console.WriteLine($"[demo] session-alpha : {toursA} tours ; session-beta : {toursB} tour");

    // 2. Historique isole par cle : le grain ne voit que ses propres tours.
    foreach (var line in await sessionA.GetHistoryAsync())
        Console.WriteLine($"[demo] alpha| {line}");
    foreach (var line in await sessionB.GetHistoryAsync())
        Console.WriteLine($"[demo] beta | {line}");

    // 3. Compteur de tokens par modele : etat partage entre sessions.
    var counterGpt = client.GetGrain<ITokenCounterGrain>("gpt-5.6-luna");
    var counterWhisper = client.GetGrain<ITokenCounterGrain>("whisper-1");
    await counterGpt.RecordUsage(1200);
    await counterGpt.RecordUsage(340);
    var totalGpt = await counterGpt.RecordUsage(85);
    var totalWhisper = await counterWhisper.RecordUsage(2100);

    Console.WriteLine($"[demo] tokens gpt-5.6-luna={totalGpt} (3 appels cumules), whisper-1={totalWhisper}");

    // 4. Concurrency : 50 appels concurrents sur le MEME grain compteur.
    //    Le modele acteur serialise les acces : le total final est exactement la somme,
    //    sans Interlocked ni lock dans le code du grain.
    var concurrent = Enumerable.Range(1, 50).Select(i => counterGpt.RecordUsage(10)).ToArray();
    var lastTotals = await Task.WhenAll(concurrent);
    var finalTotal = await counterGpt.GetTotalAsync();
    var expected = 1200 + 340 + 85 + 50 * 10;
    Console.WriteLine($"[demo] concurrence : 50 appels x10 tokens -> total={finalTotal}, attendu={expected}, "
        + (finalTotal == expected ? "COHERENT (pas de course)" : "INCOHERENT"));
    Console.WriteLine($"[demo] totaux intermediaires distincts vus par les appelants : {lastTotals.Distinct().Count()}");

    // 5. Re-activation : un grain dont on efface la reference reste identite + etat.
    var counterGptAgain = client.GetGrain<ITokenCounterGrain>("gpt-5.6-luna");
    var totalAgain = await counterGptAgain.GetTotalAsync();
    Console.WriteLine($"[demo] identite stable : nouvelle reference sur 'gpt-5.6-luna' -> total={totalAgain} "
        + (totalAgain == finalTotal ? "(etat conserve)" : "(etat perdu ?)"));
}

static async Task RunExercise1Async(IGrainFactory client)
{
    var counter = client.GetGrain<ITokenCounterGrain>("gpt-5.6-luna");
    await counter.RecordUsage(1200);
    await counter.RecordUsage(340);
    await counter.RecordUsage(85);
    var cost = await counter.EstimateCostAsync(centsPerThousandTokens: 40);
    Console.WriteLine($"[ex1] total={(1200 + 340 + 85)} tokens, cout estime a 40 cents/1k -> {cost} cents");
    Console.WriteLine(cost == -1m
        ? "[ex1] EstimateCostAsync est encore le stub : complete Grains.cs puis relance cette cellule"
        : "[ex1] estimation retournee par l'etudiant");
}

static async Task RunExercise2Async(IGrainFactory client)
{
    var session = client.GetGrain<IAgentSessionGrain>("session-exercice");
    await session.AppendTurnAsync("user", "Quel est le statut du projet client ?");
    await session.AppendTurnAsync("assistant", "Le projet client est en revue finale avant livraison");
    var last = await session.LastExcerptAsync();
    Console.WriteLine($"[ex2] dernier extrait -> \"{last}\"");
    Console.WriteLine(string.IsNullOrEmpty(last)
        ? "[ex2] LastExcerptAsync est encore le stub : complete Grains.cs puis relance cette cellule"
        : "[ex2] extrait retourne par l'etudiant");
}

static async Task RunExercise3Async(IGrainFactory client)
{
    var sessionA = client.GetGrain<IAgentSessionGrain>("session-route-a");
    var sessionB = client.GetGrain<IAgentSessionGrain>("session-route-b");
    var counter = client.GetGrain<ITokenCounterGrain>("qwen3-coder");

    await sessionA.RouteTokensAsync("qwen3-coder", 500);
    await sessionA.RouteTokensAsync("qwen3-coder", 300);
    await sessionB.RouteTokensAsync("qwen3-coder", 900);

    var counterTotal = await counter.GetTotalAsync();
    var totalA = await sessionA.GetTokenTotalAsync();
    var totalB = await sessionB.GetTokenTotalAsync();
    Console.WriteLine($"[ex3] compteur qwen3-coder={counterTotal} (attendu 1700), "
        + $"session-route-a={totalA} (attendu 800), session-route-b={totalB} (attendu 900)");
    Console.WriteLine(counterTotal == 1700 && totalA == 800 && totalB == 900
        ? "[ex3] routage coherent : chaque session cumule ET le compteur global aussi"
        : "[ex3] RouteTokensAsync est encore le stub : complete Grains.cs puis relance cette cellule");
}
