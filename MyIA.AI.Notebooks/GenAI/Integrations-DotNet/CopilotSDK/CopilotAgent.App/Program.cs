using System.Text;
using System.Threading.Channels;
using GitHub.Copilot;
using Microsoft.AspNetCore.Builder;
using Microsoft.AspNetCore.Http;
using Microsoft.AspNetCore.Routing;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;

// -----------------------------------------------------------------------------
// Top-level statements : composition ASP.NET Core (precedent les types).
// -----------------------------------------------------------------------------

var builder = WebApplication.CreateBuilder(args);
builder.Services.AddSingleton<CopilotAgentService>();
builder.Services.AddHostedService(sp => sp.GetRequiredService<CopilotAgentService>());
builder.Services.ScanEndpoints();

var app = builder.Build();
app.MapEndpoints();

app.Run();

// -----------------------------------------------------------------------------
// Types : contrat IEndpoint, glue Scrutor, endpoints, service d'agent.
// (Les declarations de type suivent les instructions de niveau superieur.)
// -----------------------------------------------------------------------------

public interface IEndpoint
{
    void Map(IEndpointRouteBuilder app);
}

public static class EndpointExtensions
{
    public static IServiceCollection ScanEndpoints(this IServiceCollection services)
        => services.Scan(scan => scan
            .FromAssemblyOf<HealthEndpoint>()
            .AddClasses(c => c.AssignableTo<IEndpoint>())
            .As<IEndpoint>()
            .WithTransientLifetime());

    public static IEndpointRouteBuilder MapEndpoints(this IEndpointRouteBuilder app)
    {
        var endpoints = app.ServiceProvider.GetServices<IEndpoint>();
        foreach (var endpoint in endpoints)
        {
            endpoint.Map(app);
        }
        return app;
    }
}

public sealed class HealthEndpoint : IEndpoint
{
    public void Map(IEndpointRouteBuilder app)
        => app.MapGet("/health", () => Results.Ok(new { status = "ok", endpoint = "HealthEndpoint" }));
}

public sealed class PromptEndpoint : IEndpoint
{
    public void Map(IEndpointRouteBuilder app)
        => app.MapPost("/prompt", async (PromptRequest req, CopilotAgentService svc, CancellationToken ct) =>
        {
            var ask = svc.AskAsync(req.Prompt, ct);

            // Le canal deltas est expose en SSE ligne par ligne.
            var sse = new StringBuilder();
            await foreach (var chunk in svc.Stream.ReadAllAsync(ct))
            {
                sse.Append("data: ").Append(chunk).Append("\n\n");
            }
            await ask;
            return Results.Text(sse.ToString(), "text/event-stream");
        });

    public record PromptRequest(string Prompt);
}

public sealed class CopilotAgentService : BackgroundService
{
    private readonly Channel<string> _outbound = Channel.CreateUnbounded<string>();

    public ChannelReader<string> Stream => _outbound.Reader;

    public async Task AskAsync(string prompt, CancellationToken ct)
    {
        await using var client = new CopilotClient();
        await client.StartAsync();
        await using var session = await client.CreateSessionAsync(new SessionConfig
        {
            Model = "gpt-4.1",
            Streaming = true,
            OnPermissionRequest = PermissionHandler.ApproveAll,
        });

        var tcs = new TaskCompletionSource();
        session.On<SessionEvent>(evt =>
        {
            switch (evt)
            {
                case AssistantMessageDeltaEvent d:
                    _outbound.Writer.TryWrite(d.Data.DeltaContent);
                    break;
                case SessionIdleEvent:
                    _outbound.Writer.TryComplete();
                    tcs.TrySetResult();
                    break;
                case SessionErrorEvent err:
                    _outbound.Writer.TryComplete();
                    tcs.TrySetException(new InvalidOperationException(err.Data.Message));
                    break;
            }
        });
        await session.SendAsync(new MessageOptions { Prompt = prompt }, ct);
        await tcs.Task;
    }

    protected override Task ExecuteAsync(CancellationToken stoppingToken) => Task.CompletedTask;
}
