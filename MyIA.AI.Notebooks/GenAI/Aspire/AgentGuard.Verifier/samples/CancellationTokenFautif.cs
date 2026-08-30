using System.Threading;
using System.Threading.Tasks;

public static class AgentCancellationFautif
{
    public static async Task RepondreAsync(
        string prompt,
        CancellationToken cancellationToken)
    {
        await EnvoyerAuModeleAsync(prompt); // AGENTGUARD004
    }

    private static Task EnvoyerAuModeleAsync(
        string prompt,
        CancellationToken cancellationToken = default)
        => Task.Delay(10, cancellationToken);
}
