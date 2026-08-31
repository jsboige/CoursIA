using System.Threading;
using System.Threading.Tasks;

public static class AgentSurchargeSansToken
{
    public static async Task RepondreAsync(
        string prompt,
        CancellationToken cancellationToken)
    {
        await EnvoyerAuModeleAsync(prompt);
    }

    private static Task EnvoyerAuModeleAsync(string prompt)
        => Task.Delay(10);

    private static Task EnvoyerAuModeleAsync(
        string prompt,
        int priorite,
        CancellationToken cancellationToken = default)
        => Task.Delay(priorite, cancellationToken);
}
