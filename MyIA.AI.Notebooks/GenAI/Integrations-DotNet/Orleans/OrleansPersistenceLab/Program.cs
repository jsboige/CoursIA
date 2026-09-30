// Lab 03 : persistance de l'etat des grains Orleans dans un Redis reel.
//
// Chaque invocation demarre un silo co-heberge (UseLocalhostClustering), joue un
// scenario, puis s'arrete : le process meurt a la fin. C'est ce qui rend la mesure
// honnete - ce qui survit d'une invocation a l'autre a forcement transite par le
// fournisseur de stockage, jamais par la memoire du process.
//
// Usage : dotnet run -- <scenario> [arguments]
//   write <redis|memory> <session> <tours>   ajoute des tours a une session
//   read  <redis|memory> <session>           relit une session dans un process neuf
//   conflict <session>                       deux silos, un meme grain, un conflit d'ETag
//   ex1 | ex2 | ex3                          verifications des exercices
//
// L'adresse Redis vient de la variable d'environnement ORLEANS_REDIS (host:port).
// Ports des silos : 11131/30031 (A) et 11132/30032 (B), distincts de ceux des labs
// 01 et 02 (11111/30000) pour que les labs puissent tourner en meme temps.

using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using Orleans.Storage;
using OrleansPersistenceLab;
using StackExchange.Redis;

var scenario = args.Length > 0 ? args[0] : "read";
var redisEndpoint = Environment.GetEnvironmentVariable("ORLEANS_REDIS") ?? "localhost:6379";
const string ServiceId = "orleans-persistence-lab";

// Un silo = un host. provider choisit le fournisseur enregistre sous le nom "sessions" ;
// le grain, lui, ne sait rien de ce choix.
IHost BuildSilo(string provider, string clusterId, int siloPort, int gatewayPort) =>
    new HostBuilder()
        .UseOrleans(silo =>
        {
            silo.UseLocalhostClustering(siloPort, gatewayPort, serviceId: ServiceId, clusterId: clusterId);
            if (provider == "redis")
            {
                silo.AddRedisGrainStorage("sessions", options =>
                    options.ConfigurationOptions = ConfigurationOptions.Parse(redisEndpoint));
            }
            else
            {
                silo.AddMemoryGrainStorage("sessions");
            }
        })
        .ConfigureLogging(logging => logging.SetMinimumLevel(LogLevel.Warning))
        .Build();

string Show(SessionSnapshot s) =>
    $"tours={s.TurnCount} tokens={s.TokenTotal} etag={s.ETag ?? "(aucun)"} existe={s.RecordExists}";

switch (scenario)
{
    case "write":
    {
        var (provider, session, count) = (args[1], args[2], int.Parse(args[3]));
        using var host = BuildSilo(provider, "lab-a", 11131, 30031);
        await host.StartAsync();
        var grain = host.Services.GetRequiredService<IGrainFactory>().GetGrain<IPersistentSessionGrain>(session);
        Console.WriteLine($"[write] fournisseur={provider} session={session} pid={Environment.ProcessId}");
        Console.WriteLine($"[write] avant   : {Show(await grain.GetSnapshotAsync())}");
        for (var i = 1; i <= count; i++)
        {
            await grain.AppendTurnAsync(i % 2 == 1 ? "user" : "assistant", $"message {i}", 40 * i);
        }
        Console.WriteLine($"[write] apres   : {Show(await grain.GetSnapshotAsync())}");
        await host.StopAsync();
        Console.WriteLine("[write] process termine");
        break;
    }

    case "read":
    {
        var (provider, session) = (args[1], args[2]);
        using var host = BuildSilo(provider, "lab-a", 11131, 30031);
        await host.StartAsync();
        var grain = host.Services.GetRequiredService<IGrainFactory>().GetGrain<IPersistentSessionGrain>(session);
        Console.WriteLine($"[read] fournisseur={provider} session={session} pid={Environment.ProcessId}");
        Console.WriteLine($"[read] etat relu : {Show(await grain.GetSnapshotAsync())}");
        foreach (var turn in await grain.GetTurnsAsync())
        {
            Console.WriteLine($"[read]   {turn}");
        }
        await host.StopAsync();
        break;
    }

    case "conflict":
    {
        var session = args[1];
        // Deux clusters distincts (ClusterId differents) partagent le meme ServiceId,
        // donc la meme cle Redis : le meme grain est active deux fois. C'est la
        // situation que le directory d'Orleans empeche a l'interieur d'un cluster,
        // et que l'ETag rattrape au niveau du stockage.
        using var hostA = BuildSilo("redis", "lab-a", 11131, 30031);
        using var hostB = BuildSilo("redis", "lab-b", 11132, 30032);
        await hostA.StartAsync();
        await hostB.StartAsync();
        var a = hostA.Services.GetRequiredService<IGrainFactory>().GetGrain<IPersistentSessionGrain>(session);
        var b = hostB.Services.GetRequiredService<IGrainFactory>().GetGrain<IPersistentSessionGrain>(session);

        Console.WriteLine($"[conflict] A lit : {Show(await a.GetSnapshotAsync())}");
        Console.WriteLine($"[conflict] B lit : {Show(await b.GetSnapshotAsync())}");
        await a.AppendTurnAsync("user", "ecrit par le silo A", 100);
        Console.WriteLine($"[conflict] A ecrit : {Show(await a.GetSnapshotAsync())}");
        try
        {
            await b.AppendTurnAsync("user", "ecrit par le silo B", 100);
            Console.WriteLine("[conflict] B ecrit sans conflit (ecrasement silencieux)");
        }
        catch (InconsistentStateException ex)
        {
            Console.WriteLine($"[conflict] B refuse : {ex.GetType().Name}");
            Console.WriteLine($"[conflict]   {ex.Message}");
        }
        await b.ReloadAsync();
        Console.WriteLine($"[conflict] B relit : {Show(await b.GetSnapshotAsync())}");
        foreach (var turn in await b.GetTurnsAsync())
        {
            Console.WriteLine($"[conflict]   {turn}");
        }
        await hostB.StopAsync();
        await hostA.StopAsync();
        break;
    }

    case "ex1":
    {
        using var host = BuildSilo("redis", "lab-a", 11131, 30031);
        await host.StartAsync();
        var grain = host.Services.GetRequiredService<IGrainFactory>().GetGrain<IPersistentSessionGrain>($"ex1-{Guid.NewGuid():N}");
        await grain.AppendTurnAsync("user", "a effacer", 50);
        Console.WriteLine($"[ex1] avant reset : {Show(await grain.GetSnapshotAsync())}");
        await grain.ResetAsync();
        var after = await grain.GetSnapshotAsync();
        Console.WriteLine($"[ex1] apres reset : {Show(after)}");
        if (after.TurnCount > 0)
        {
            Console.WriteLine("[ex1] ResetAsync est encore le stub : complete Grains.cs puis relance cette cellule");
        }
        else if (after.RecordExists)
        {
            Console.WriteLine("[ex1] a revoir : l'etat est vide mais l'enregistrement existe encore (un etat vide a ete ecrit, rien n'a ete efface)");
        }
        else
        {
            Console.WriteLine("[ex1] OK : l'enregistrement est efface");
        }
        await host.StopAsync();
        break;
    }

    case "ex2":
    {
        using var host = BuildSilo("redis", "lab-a", 11131, 30031);
        await host.StartAsync();
        var grain = host.Services.GetRequiredService<IGrainFactory>().GetGrain<IPersistentSessionGrain>($"ex2-{Guid.NewGuid():N}");
        var first = await grain.TryConsumeAsync(300, 500);
        var etagAfterFirst = (await grain.GetSnapshotAsync()).ETag;
        var second = await grain.TryConsumeAsync(300, 500);
        var final = await grain.GetSnapshotAsync();
        Console.WriteLine($"[ex2] 300/500 -> {first} ; 300 de plus -> {second} ; {Show(final)}");
        if (!first)
        {
            Console.WriteLine("[ex2] TryConsumeAsync est encore le stub : complete Grains.cs puis relance cette cellule");
        }
        else if (!second && final.TokenTotal == 300 && final.ETag == etagAfterFirst)
        {
            Console.WriteLine("[ex2] OK : le depassement est refuse sans ecriture (ETag inchange)");
        }
        else
        {
            Console.WriteLine("[ex2] a revoir : le refus ne doit ni cumuler ni ecrire");
        }
        await host.StopAsync();
        break;
    }

    case "ex3":
    {
        var session = $"ex3-{Guid.NewGuid():N}";
        using var hostA = BuildSilo("redis", "lab-a", 11131, 30031);
        using var hostB = BuildSilo("redis", "lab-b", 11132, 30032);
        await hostA.StartAsync();
        await hostB.StartAsync();
        var a = hostA.Services.GetRequiredService<IGrainFactory>().GetGrain<IPersistentSessionGrain>(session);
        var b = hostB.Services.GetRequiredService<IGrainFactory>().GetGrain<IPersistentSessionGrain>(session);
        await a.GetSnapshotAsync();
        await b.GetSnapshotAsync();
        await a.AppendTurnAsync("user", "ecrit par le silo A", 100);
        var count = await b.AppendTurnWithRetryAsync("user", "ecrit par le silo B", 100);
        Console.WriteLine($"[ex3] B apres ecriture avec reprise : tours={count}");
        if (count < 0)
        {
            Console.WriteLine("[ex3] AppendTurnWithRetryAsync est encore le stub : complete Grains.cs puis relance cette cellule");
        }
        else if (count == 2)
        {
            Console.WriteLine("[ex3] OK : le tour de A est conserve et celui de B ajoute par-dessus");
        }
        else
        {
            Console.WriteLine("[ex3] a revoir : attendu 2 tours (A puis B)");
        }
        await hostB.StopAsync();
        await hostA.StopAsync();
        break;
    }

    default:
        Console.WriteLine($"[erreur] scenario inconnu : {scenario}");
        break;
}
