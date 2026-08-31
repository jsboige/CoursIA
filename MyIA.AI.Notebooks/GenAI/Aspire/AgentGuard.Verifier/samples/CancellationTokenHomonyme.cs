using System.Threading.Tasks;

namespace AgentCustom;

public readonly record struct CancellationToken(bool PeutAnnuler);

public static class AgentTokenHomonyme
{
    public static async Task RepondreAsync(
        string prompt,
        CancellationToken cancellationToken)
    {
        await EnvoyerAuModeleAsync(prompt);
    }

    private static Task EnvoyerAuModeleAsync(
        string prompt,
        CancellationToken cancellationToken = default)
        => Task.CompletedTask;
}
