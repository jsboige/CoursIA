// FastDownwardBackend.cs -- un seul point d'appel a Fast Downward pour les jumeaux C# de Planners.
//
// Un notebook le charge par un chemin relatif a son dossier :
//
//     #load "../FastDownwardBackend.cs"
//     string body = FastDownwardBackend.PlanJson(domainPddl, problemPddl, "astar(lmcut())");
//     Console.WriteLine("Moteur : " + FastDownwardBackend.Description);
//
// PlanJson rend le corps JSON {returncode, stdout, stderr}, le contrat de POST /plan du
// conteneur coursia-fast-downward. Le moteur est choisi une fois par session :
//   1. le service Docker (http://localhost:8200), s'il repond a /health ;
//   2. sinon le pilote fast-downward.py que livre le paquet Python up_fast_downward
//      (pip install up-fast-downward), lance dans un dossier temporaire. Le paquet publie
//      des wheels compilees pour Linux, macOS et Windows : Docker n'est donc pas requis.
// Les candidats Python sont python3 puis python (python puis python3 sous Windows) ; le
// premier qui importe up_fast_downward est retenu.
//
// Sans service ni paquet, PlanJson leve InvalidOperationException avec la commande d'installation :
// pas de sortie de substitution.
// Les chemins machine (interpreteur, dossier temporaire) ne sont jamais imprimes.

#nullable enable

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Net.Http;
using System.Text;
using System.Text.Json;

public static class FastDownwardBackend
{
    public const string ServiceUrl = "http://localhost:8200";

    static readonly HttpClient Http = new HttpClient { Timeout = TimeSpan.FromSeconds(120) };
    static bool resolved;
    static bool useService;
    static string? serviceVersion;
    static string? interpreter;
    static string? driver;
    static string? localVersion;

    // Moteur retenu pour la session, en clair (ex. "Fast Downward 26.6, plugin local up_fast_downward").
    public static string Description
    {
        get
        {
            Resolve();
            if (useService)
                return (serviceVersion != null ? "Fast Downward " + serviceVersion : "Fast Downward")
                    + ", service Docker coursia-fast-downward (port 8200)";
            if (driver != null) return (localVersion ?? "Fast Downward") + ", plugin local up_fast_downward";
            return "aucun (ni service Docker sur le port 8200, ni paquet Python up-fast-downward)";
        }
    }

    public static bool Available { get { Resolve(); return useService || driver != null; } }

    // Planifie et rend {returncode, stdout, stderr}, comme POST /plan.
    public static string PlanJson(string domain, string problem, string search, int timeoutSeconds = 60)
    {
        Resolve();
        if (useService) return PostToService(domain, problem, search);
        if (driver == null)
            throw new InvalidOperationException(
                "Fast Downward indisponible : demarrer le conteneur coursia-fast-downward (port 8200) "
                + "ou installer le paquet Python : pip install up-fast-downward");
        return RunLocalDriver(domain, problem, search, timeoutSeconds);
    }

    static void Resolve()
    {
        if (resolved) return;
        resolved = true;
        useService = ServiceAnswers();
        if (useService) return;
        foreach (var candidate in Candidates())
        {
            var path = LocateDriver(candidate);
            if (path == null) continue;
            interpreter = candidate;
            driver = path;
            localVersion = ReadLocalVersion();
            return;
        }
    }

    static bool ServiceAnswers()
    {
        try
        {
            using var probe = new HttpClient { Timeout = TimeSpan.FromSeconds(2) };
            using var resp = probe.GetAsync(ServiceUrl + "/health").Result;
            if (!resp.IsSuccessStatusCode) return false;
            try
            {
                using var health = JsonDocument.Parse(resp.Content.ReadAsStringAsync().Result);
                if (health.RootElement.ValueKind == JsonValueKind.Object
                    && health.RootElement.TryGetProperty("version", out var v) && v.ValueKind == JsonValueKind.String)
                    serviceVersion = v.GetString();
            }
            catch (JsonException) { }   // corps de /health sans version lisible
            return true;
        }
        catch (Exception) { return false; }   // refus de connexion, delai, hote inconnu
    }

    static string PostToService(string domain, string problem, string search)
    {
        var payload = JsonSerializer.Serialize(new { domain, problem, search });
        using var resp = Http.PostAsync(ServiceUrl + "/plan",
            new StringContent(payload, Encoding.UTF8, "application/json")).Result;
        return resp.Content.ReadAsStringAsync().Result;
    }

    static IEnumerable<string> Candidates()
    {
        if (OperatingSystem.IsWindows()) { yield return "python"; yield return "python3"; }
        else { yield return "python3"; yield return "python"; }
    }

    static string? LocateDriver(string candidate)
    {
        const string script =
            "import os, up_fast_downward\n" +
            "print(os.path.join(os.path.dirname(up_fast_downward.__file__), 'downward', 'fast-downward.py'))\n";
        var (code, stdout, _) = Run(candidate, new[] { "-c", script }, null, 60);
        if (code != 0) return null;
        var lines = stdout.Split('\n', StringSplitOptions.RemoveEmptyEntries);
        var path = lines.Length > 0 ? lines[^1].Trim() : "";
        return File.Exists(path) ? path : null;
    }

    static string? ReadLocalVersion()
    {
        var (code, stdout, _) = Run(interpreter!, new[] { driver!, "--version" }, null, 60);
        if (code != 0) return null;
        foreach (var line in stdout.Split('\n'))
            if (line.StartsWith("Fast Downward", StringComparison.Ordinal)) return line.Trim();
        return null;
    }

    // Le pilote ecrit output.sas et sas_plan dans son dossier courant : un dossier temporaire
    // par appel, supprime ensuite, garde l'arbre du depot propre.
    static string RunLocalDriver(string domain, string problem, string search, int timeoutSeconds)
    {
        var work = Path.Combine(Path.GetTempPath(), "coursia-fd-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(work);
        try
        {
            File.WriteAllText(Path.Combine(work, "domain.pddl"), domain);
            File.WriteAllText(Path.Combine(work, "problem.pddl"), problem);
            var (code, stdout, stderr) = Run(interpreter!,
                new[] { driver!, "domain.pddl", "problem.pddl", "--search", search }, work, timeoutSeconds);
            return Serialize(code, stdout, stderr);
        }
        finally
        {
            try { Directory.Delete(work, recursive: true); } catch (IOException) { } catch (UnauthorizedAccessException) { }
        }
    }

    static (int Code, string Stdout, string Stderr) Run(string file, IEnumerable<string> args, string? cwd, int timeoutSeconds)
    {
        try
        {
            var psi = new ProcessStartInfo(file)
            { RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false };
            foreach (var a in args) psi.ArgumentList.Add(a);
            if (cwd != null) psi.WorkingDirectory = cwd;
            using var process = Process.Start(psi);
            if (process == null) return (-1, "", "processus non demarre");
            var stdout = process.StandardOutput.ReadToEndAsync();
            var stderr = process.StandardError.ReadToEndAsync();
            if (!process.WaitForExit(timeoutSeconds * 1000))
            {
                process.Kill(entireProcessTree: true);
                return (-1, stdout.Result, $"delai de {timeoutSeconds} s depasse");
            }
            return (process.ExitCode, stdout.Result, stderr.Result);
        }
        catch (System.ComponentModel.Win32Exception) { return (-1, "", "interpreteur introuvable"); }
    }

    static string Serialize(int returncode, string stdout, string stderr)
        => JsonSerializer.Serialize(new { returncode, stdout, stderr });
}
