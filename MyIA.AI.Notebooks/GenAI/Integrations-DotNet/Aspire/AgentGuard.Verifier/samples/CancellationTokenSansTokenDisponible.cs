using System.Threading;
using System.Threading.Tasks;

public static class AgentSansTokenDisponible
{
    public static async Task RepondreAsync(string prompt)
    {
        await EnvoyerAuModeleAsync(prompt);
    }

    private static Task EnvoyerAuModeleAsync(
        string prompt,
        CancellationToken cancellationToken = default)
        => Task.Delay(10, cancellationToken);
}
