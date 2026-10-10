using System.Diagnostics;

namespace MyIA.AI.Shared.Search.Adversarial.Go.Gtp;

/// <summary>
/// Lance un moteur GTP (gnugo en tete) en processus et l'expose comme canal
/// <see cref="GtpClient"/>. EPIC #7265, pepite B3, tranche 7.
/// </summary>
/// <remarks>
/// <para>
/// <b>Resolution du binaire, sans repli silencieux</b> : la variable
/// <c>GNUGO_CMD</c> prime (ligne de commande complete, espaces compris — le
/// pont WSL teste dans la PR s'ecrit <c>wsl -d Ubuntu -- gnugo</c>) ; a defaut
/// le PATH est sonde pour <c>gnugo</c> ; a defaut encore, le pont WSL par
/// defaut. Si les trois echouent, l'exception nomme le geste d'installation
/// (<c>apt install gnugo</c> sous WSL/Ubuntu) — jamais un adversaire fictif a
/// la place du vrai (regle F : on repare l'environnement, on ne le contourne pas).
/// </para>
/// <para>
/// <b>Arguments</b> : <c>--mode gtp</c> (le protocole) et <c>--quiet</c>
/// (sans banniere de copyright, qui n'est pas une trame GTP). Le niveau par
/// defaut de gnugo reste celui du moteur ; un appelant qui veut un adversaire
/// plus faible passe <c>level</c> en commande GTP, pas en option de lancement.
/// </para>
/// </remarks>
public static class GnuGoLauncher
{
    /// <summary>Variable d'environnement qui force la ligne de commande du moteur.</summary>
    public const string CommandVariable = "GNUGO_CMD";

    private static readonly string[] WslBridge = ["wsl", "-d", "Ubuntu", "--", "gnugo"];

    /// <summary>
    /// Trouve la ligne de commande du moteur : <c>GNUGO_CMD</c>, puis gnugo sur
    /// le PATH, puis le pont WSL par defaut. Leve <see cref="GtpException"/> en
    /// nommant l'installation si rien n'est joignable.
    /// </summary>
    public static IReadOnlyList<string> Resolve()
    {
        string? forced = Environment.GetEnvironmentVariable(CommandVariable);
        if (!string.IsNullOrWhiteSpace(forced))
        {
            return forced.Split(' ', StringSplitOptions.RemoveEmptyEntries);
        }

        if (IsOnPath("gnugo"))
        {
            return ["gnugo"];
        }

        if (IsOnPath(WslBridge[0]))
        {
            return WslBridge;
        }

        throw new GtpException(
            $"aucun moteur gnugo joignable : poser {CommandVariable} (ex. « wsl -d Ubuntu -- gnugo »), "
            + "ou installer gnugo (apt install gnugo sous WSL/Ubuntu) — pas d'adversaire de substitution");
    }

    /// <summary>
    /// Lance le moteur resolu et rend le client branche sur son stdin/stdout.
    /// L'appelant dispose le client ET le processus rendu.
    /// </summary>
    public static (GtpClient Client, Process Process) Start(TimeSpan? timeout = null)
    {
        IReadOnlyList<string> command = Resolve();
        var start = new ProcessStartInfo
        {
            FileName = command[0],
            RedirectStandardInput = true,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
            CreateNoWindow = true,
        };

        foreach (string arg in command.Skip(1))
        {
            start.ArgumentList.Add(arg);
        }

        start.ArgumentList.Add("--mode");
        start.ArgumentList.Add("gtp");
        start.ArgumentList.Add("--quiet");

        Process process = Process.Start(start)
            ?? throw new GtpException($"le moteur GTP n'a pas demarre : {string.Join(' ', command)}");

        var client = new GtpClient(process.StandardInput, process.StandardOutput, timeout);
        return (client, process);
    }

    private static bool IsOnPath(string executable)
    {
        string suffix = OperatingSystem.IsWindows() ? ".exe" : string.Empty;
        string[] dirs = (Environment.GetEnvironmentVariable("PATH") ?? string.Empty)
            .Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries);

        foreach (string dir in dirs)
        {
            try
            {
                string candidate = Path.Combine(dir, executable + suffix);
                if (File.Exists(candidate))
                {
                    return true;
                }
            }
            catch (Exception ex) when (ex is ArgumentException or PathTooLongException)
            {
                // Une entree PATH malformee ne disqualifie pas les autres.
            }
        }

        return false;
    }

}
