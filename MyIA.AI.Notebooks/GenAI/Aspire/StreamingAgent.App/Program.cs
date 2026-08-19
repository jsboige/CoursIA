using System.Text.Json;
using System.Threading.Channels;
using Microsoft.AspNetCore.Builder;
using Microsoft.AspNetCore.Http;
using Microsoft.AspNetCore.Http.HttpResults;

var builder = WebApplication.CreateBuilder(new WebApplicationOptions { Args = args });
// builder.Logging.ClearProviders();
builder.Services.AddSingleton<AgentService>();
builder.Services.AddHostedService(sp => sp.GetRequiredService<AgentService>());
var app = builder.Build();

app.MapGet("/health", () => TypedResults.Ok(new HealthResponse("ok", "streaming-agent")));
app.MapPost("/greet", GreetHandler.Handle);
app.MapPost("/stream", StreamHandler.Handle);

if (args.Length == 0)
{
    app.Urls.Add("http://127.0.0.1:5128");
}
app.Run();

public record HealthResponse(string Status, string Service);
public record GreetRequest(string Name);
public record GreetResponse(string Message);
public record StreamRequest(string Prompt);
public record AgentRequest(string Prompt);
public record AgentEvent(string Kind, string Payload);

// Handler en classe typée : requête forte en entrée, TypedResults en sortie.
// (Le contrat "endpoint as class" de la minimal API : une méthode statique
// dont les paramètres sont résolus par le framework — requête JSON + services DI.)
public static class GreetHandler
{
    public static IResult Handle(GreetRequest request)
        => TypedResults.Ok(new GreetResponse($"Bonjour {request.Name} depuis un endpoint typé .NET 10."));
}

public static class StreamHandler
{
    public static async Task<IResult> Handle(StreamRequest request, AgentService service, CancellationToken ct)
    {
        await service.SubmitAsync(new AgentRequest(request.Prompt), ct);
        var events = new List<AgentEvent>();
        await foreach (var evt in service.Stream.ReadAllAsync(ct))
        {
            events.Add(evt);
            if (evt.Kind == "done")
            {
                break;
            }
        }
        return TypedResults.Text(JsonSerializer.Serialize(events, new JsonSerializerOptions(JsonSerializerDefaults.Web)), "application/json");
    }
}

public sealed class AgentService : BackgroundService
{
    private readonly Channel<AgentRequest> _inbound = Channel.CreateUnbounded<AgentRequest>();
    private readonly Channel<AgentEvent> _outbound = Channel.CreateUnbounded<AgentEvent>();

    public ChannelReader<AgentEvent> Stream => _outbound.Reader;

    public ValueTask SubmitAsync(AgentRequest request, CancellationToken ct)
        => _inbound.Writer.WriteAsync(request, ct);

    protected override async Task ExecuteAsync(CancellationToken stoppingToken)
    {
        try
        {
            await foreach (var request in _inbound.Reader.ReadAllAsync(stoppingToken))
            {
                foreach (var word in request.Prompt.Split(' '))
                {
                    await _outbound.Writer.WriteAsync(new AgentEvent("token", word), stoppingToken);
                    await Task.Delay(80, stoppingToken);
                }
                await _outbound.Writer.WriteAsync(new AgentEvent("done", request.Prompt), stoppingToken);
            }
        }
        finally
        {
            _outbound.Writer.Complete();
        }
    }
}
