using System.Threading;
using System.Threading.Tasks;

public static class AgentCancellationCorrige
{
    public static async Task RepondreAsync(
        string prompt,
        CancellationToken cancellationToken)
    {
        await EnvoyerAuModeleAsync(prompt, cancellationToken);
    }

    private static Task EnvoyerAuModeleAsync(
        string prompt,
        CancellationToken cancellationToken = default)
        => Task.Delay(10, cancellationToken);
}
