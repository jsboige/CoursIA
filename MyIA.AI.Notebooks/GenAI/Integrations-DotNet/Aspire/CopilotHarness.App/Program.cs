// CopilotHarness.App : le harness GitHub.Copilot.SDK exécute pour de vrai.
// Le package embarque son runtime (FFI native) : aucune CLI externe à installer.
// Modes :
//   auth            -- état d'authentification du harness (aucun appel modèle)
//   models          -- catalogue des modèles servis par Copilot (aucun appel modèle)
//   ask "<prompt>"  -- un tour complet : session + envoi + attente de la réponse
//   events "<prompt>" -- même tour, mais en consommant le flux SessionEvent au fil de l'eau
using System.Text;
using System.Text.Json;
using GitHub.Copilot;

var mode = args.Length > 0 ? args[0] : "auth";
if (mode is "ask" or "events" && args.Length < 2)
{
    Console.WriteLine($"usage : CopilotHarness.App {mode} \"<prompt>\"");
    return 1;
}
var jsonOpts = new JsonSerializerOptions { WriteIndented = true };

var options = new CopilotClientOptions
{
    // Le harness est un agent : son répertoire de travail délimite son terrain d'action.
    WorkingDirectory = Environment.CurrentDirectory,
};
using var client = new CopilotClient(options);
await client.StartAsync();

switch (mode)
{
    case "auth":
    {
        var auth = await client.GetAuthStatusAsync();
        Console.WriteLine(JsonSerializer.Serialize(auth, jsonOpts));
        break;
    }
    case "models":
    {
        var models = await client.ListModelsAsync();
        Console.WriteLine($"{"id",-24} {"nom",-22} vision");
        foreach (var m in models.OrderBy(m => m.Id, StringComparer.Ordinal))
        {
            var vision = m.Capabilities?.Supports?.Vision is true ? "oui" : "non";
            Console.WriteLine($"{m.Id,-24} {m.Name,-22} {vision}");
        }
        Console.WriteLine($"TOTAL {models.Count} modeles");
        break;
    }
    case "ask":
    {
        var session = await client.CreateSessionAsync(new SessionConfig());
        Console.WriteLine($"session {session.SessionId}");
        var reply = await session.SendAndWaitAsync(args[1], TimeSpan.FromMinutes(2));
        Console.WriteLine(JsonSerializer.Serialize(reply, reply.GetType(), jsonOpts));
        break;
    }
    case "events":
    {
        var session = await client.CreateSessionAsync(new SessionConfig());
        Console.WriteLine($"session {session.SessionId}");
        var reply = await session.SendAndWaitAsync(args[1], TimeSpan.FromMinutes(2));
        var events = await session.GetEventsAsync();
        var histogram = new SortedDictionary<string, int>();
        var streamed = new StringBuilder();
        foreach (var ev in events)
        {
            var typeName = ev.Type?.ToString() ?? "?";
            histogram[typeName] = histogram.GetValueOrDefault(typeName) + 1;
            if ((typeName.Contains("AssistantMessageDelta") || typeName.Contains("assistant.message"))
                && streamed.Length < 400)
            {
                var je = JsonSerializer.SerializeToElement(ev, ev.GetType());
                if (je.TryGetProperty("data", out var d)
                    && d.TryGetProperty("content", out var c)
                    && c.ValueKind == JsonValueKind.String)
                    streamed.Append(c.GetString());
            }
        }
        Console.WriteLine("histogramme des SessionEvent du tour :");
        foreach (var (typeName, count) in histogram)
            Console.WriteLine($"  {typeName,-40} {count}");
        Console.WriteLine($"texte assemble depuis les deltas ({streamed.Length} car.) :");
        Console.WriteLine(streamed.ToString());
        break;
    }
    default:
        Console.WriteLine($"mode inconnu : {mode}");
        return 1;
}
return 0;
