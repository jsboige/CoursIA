// FactorGraphHelper.cs - Helper pour afficher les graphes de facteurs Infer.NET inline
// Usage dans un notebook: #load "FactorGraphHelper.cs"

using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using System.Diagnostics;

/// <summary>
/// Helper pour generer et afficher les factor graphs Infer.NET dans les notebooks Jupyter.
/// Necessite Graphviz installe pour la conversion .gv -> .svg
/// </summary>
public static class FactorGraphHelper
{
    private static bool? _graphvizAvailable = null;
    private static string _dotPath = null;
    private static bool _dotResolved = false;

    /// <summary>
    /// Localise le binaire `dot` de Graphviz. Tente d'abord le PATH du kernel
    /// (comportement historique) puis, en cas d'echec, les emplacements
    /// d'installation usuels (env conda, Program Files, /usr/bin...). Le kernel
    /// .net-csharp n'herite pas toujours du PATH conda ou Graphviz est installe,
    /// d'ou ce fallback (issue #3473). Retourne le chemin resolu (ou "dot" si
    /// present sur le PATH), ou null si introuvable. Resultat mis en cache.
    /// </summary>
    private static string ResolveDotPath()
    {
        if (_dotResolved) return _dotPath;
        _dotResolved = true;

        // 1. PATH du kernel (comportement historique inchange si dot y est)
        if (TryRunDot("dot")) { _dotPath = "dot"; return _dotPath; }

        // 2. Emplacements d'installation usuels
        bool isWindows = Path.DirectorySeparatorChar == '\\';
        string exe = isWindows ? "dot.exe" : "dot";
        var candidates = new List<string>();

        // Env conda qui a lance le kernel (CONDA_PREFIX), Windows puis Unix
        var condaPrefix = Environment.GetEnvironmentVariable("CONDA_PREFIX");
        if (!string.IsNullOrEmpty(condaPrefix))
        {
            candidates.Add(Path.Combine(condaPrefix, "Library", "bin", exe));
            candidates.Add(Path.Combine(condaPrefix, "bin", exe));
        }

        if (isWindows)
        {
            candidates.Add(@"C:\Program Files\Graphviz\bin\dot.exe");
            candidates.Add(@"C:\Program Files (x86)\Graphviz\bin\dot.exe");
            var userProfile = Environment.GetEnvironmentVariable("USERPROFILE");
            if (!string.IsNullOrEmpty(userProfile))
            {
                foreach (var env in new[] { "mcp-jupyter", "coursia-ml-training", "coursia-ml", "base" })
                foreach (var root in new[] { ".conda", "miniconda3", "anaconda3" })
                {
                    var sub = root == ".conda" ? Path.Combine(".conda", "envs", env)
                                               : Path.Combine(root, "envs", env);
                    candidates.Add(Path.Combine(userProfile, sub, "Library", "bin", exe));
                }
            }
        }
        else
        {
            candidates.Add("/usr/bin/dot");
            candidates.Add("/usr/local/bin/dot");
            candidates.Add("/opt/homebrew/bin/dot");
        }

        foreach (var c in candidates)
        {
            if (File.Exists(c) && TryRunDot(c)) { _dotPath = c; return _dotPath; }
        }

        _dotPath = null;
        return null;
    }

    private static bool TryRunDot(string dotExe)
    {
        try
        {
            var psi = new ProcessStartInfo
            {
                FileName = dotExe,
                Arguments = "-V",
                RedirectStandardError = true,
                RedirectStandardOutput = true,
                UseShellExecute = false,
                CreateNoWindow = true
            };
            using var proc = Process.Start(psi);
            if (proc == null) return false;
            proc.WaitForExit(3000);
            return proc.ExitCode == 0;
        }
        catch
        {
            return false;
        }
    }

    /// <summary>
    /// Verifie si Graphviz (dot) est disponible, en cherchant au-dela du PATH
    /// du kernel (cf ResolveDotPath, issue #3473).
    /// </summary>
    public static bool IsGraphvizAvailable()
    {
        if (_graphvizAvailable.HasValue) return _graphvizAvailable.Value;
        _graphvizAvailable = (ResolveDotPath() != null);
        return _graphvizAvailable.Value;
    }

    /// <summary>
    /// Retourne le HTML pour afficher le dernier fichier SVG genere par Infer.NET
    /// Usage: FactorGraphHelper.GetLatestFactorGraphHtml().DisplayAs("text/html")
    /// display(HTML(...)) lie IHtmlContent, type porte par un assemblage compile
    /// contre Microsoft.AspNetCore.Html.Abstractions 2.x : chaque cellule qui
    /// l'emploie declenche un CS1701. DisplayAs ne prend qu'une chaine et un
    /// type MIME, et rend le meme SVG sans le div d'enrobage (cf #14122).
    /// </summary>
    /// <summary>
    /// Liste des repertoires candidats ou Infer.NET peut avoir ecrit les artefacts
    /// Model_*.gv / Model_*.svg. En kernel .NET Interactive, le cwd d'Infer.NET
    /// n'est pas garanti etre celui du notebook : on cherche donc dans plusieurs
    /// endroits (cwd du process, cwd alternatif, dossier courant, dossier du
    /// binaire) et on agrege. Voir issue #18672.
    /// </summary>
    private static string[] GetFactorGraphSearchDirectories()
    {
        var seen = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        var list = new List<string>();
        void Add(string? p)
        {
            if (string.IsNullOrEmpty(p)) return;
            try
            {
                var full = Path.GetFullPath(p);
                if (Directory.Exists(full) && seen.Add(full))
                {
                    list.Add(full);
                }
            }
            catch
            {
                // chemin invalide -> on ignore
            }
        }

        Add(Environment.CurrentDirectory);
        // cwd alternatif selon l'OS (certains hosts basculent sur / ou %TEMP%)
        Add(Directory.GetCurrentDirectory());
        // dossier du binaire en cours (sert de repli pour un worker sans cwd)
        try { Add(AppContext.BaseDirectory); } catch { }
        // %TEMP% local : dernier recours quand aucun cwd n'est defini
        try { Add(Path.GetTempPath()); } catch { }

        return list.ToArray();
    }

    public static string GetLatestFactorGraphHtml(int maxWidth = 800)
    {
        var gvFiles = GetFactorGraphSearchDirectories()
            .SelectMany(d => SafeEnumerateFiles(d, "Model_*.gv"))
            .Distinct()
            .ToArray();
        var svgFiles = GetFactorGraphSearchDirectories()
            .SelectMany(d => SafeEnumerateFiles(d, "Model_*.svg"))
            .Distinct()
            .ToArray();

        // Prefere reconvertir le .gv le plus recent (la source de verite produite
        // par la derniere inference) quand Graphviz est disponible, pour que le
        // graphe affiche corresponde au modele courant et non a un .svg perime
        // ou issu d'un autre modele (bug #3473 stale-pick).
        if (gvFiles.Length > 0 && IsGraphvizAvailable())
        {
            return ConvertAndGetLatestGvHtml(maxWidth);
        }

        // Sinon (Graphviz absent, ou seulement un .svg pre-rendu disponible),
        // reutiliser le .svg le plus recent s'il existe.
        if (svgFiles.Length > 0)
        {
            var latestSvg = svgFiles
                .OrderByDescending(f => new FileInfo(f).LastWriteTime)
                .First();
            return GetSvgFileHtml(latestSvg, maxWidth);
        }

        return ConvertAndGetLatestGvHtml(maxWidth);
    }

    private static IEnumerable<string> SafeEnumerateFiles(string dir, string pattern)
    {
        try
        {
            return Directory.EnumerateFiles(dir, pattern, SearchOption.TopDirectoryOnly);
        }
        catch
        {
            return Array.Empty<string>();
        }
    }

    /// <summary>
    /// Retourne le HTML pour afficher un fichier SVG inline dans le notebook
    /// </summary>
    public static string GetSvgFileHtml(string svgPath, int maxWidth = 800)
    {
        if (!File.Exists(svgPath))
        {
            return $"<div style='color:red'>Fichier non trouve : {svgPath}</div>";
        }

        var svgContent = File.ReadAllText(svgPath);
        var fileName = Path.GetFileName(svgPath);
        return GetSvgContentHtml(svgContent, fileName, maxWidth);
    }

    /// <summary>
    /// Retourne le HTML pour afficher du contenu SVG inline
    /// </summary>
    public static string GetSvgContentHtml(string svgContent, string title = "Factor Graph", int maxWidth = 800)
    {
        return $@"
<div style=""margin: 10px 0; padding: 10px; border: 1px solid #ddd; border-radius: 5px; background: #fafafa;"">
    <div style=""font-weight: bold; margin-bottom: 8px; color: #333;"">{title}</div>
    <div style=""max-width: {maxWidth}px; overflow: auto;"">
        {svgContent}
    </div>
</div>";
    }

    /// <summary>
    /// Convertit un fichier .gv en SVG et retourne le HTML
    /// </summary>
    public static string ConvertAndGetGvHtml(string gvPath, int maxWidth = 800)
    {
        if (!File.Exists(gvPath))
        {
            return $"<div style='color:red'>Fichier .gv non trouve : {gvPath}</div>";
        }

        if (!IsGraphvizAvailable())
        {
            var fileName = Path.GetFileName(gvPath);
            return $@"<div style='padding: 10px; border: 1px solid #f0ad4e; background: #fcf8e3; border-radius: 5px;'>
                <strong>Graphviz non disponible.</strong><br/>
                Copiez le contenu de <code>{fileName}</code> sur <a href='https://viz-js.com/' target='_blank'>viz-js.com</a>
            </div>";
        }

        var svgPath = Path.ChangeExtension(gvPath, ".svg");

        try
        {
            var psi = new ProcessStartInfo
            {
                FileName = ResolveDotPath() ?? "dot",
                Arguments = $"-Tsvg \"{gvPath}\" -o \"{svgPath}\"",
                RedirectStandardError = true,
                UseShellExecute = false,
                CreateNoWindow = true
            };

            using var proc = Process.Start(psi);
            proc.WaitForExit(5000);

            if (proc.ExitCode == 0 && File.Exists(svgPath))
            {
                return GetSvgFileHtml(svgPath, maxWidth);
            }
            else
            {
                var error = proc.StandardError.ReadToEnd();
                return $"<div style='color:red'>Erreur Graphviz : {error}</div>";
            }
        }
        catch (Exception ex)
        {
            return $"<div style='color:red'>Erreur : {ex.Message}</div>";
        }
    }

    /// <summary>
    /// Trouve et convertit le dernier fichier .gv, retourne le HTML
    /// </summary>
    public static string ConvertAndGetLatestGvHtml(int maxWidth = 800)
    {
        var gvFiles = GetFactorGraphSearchDirectories()
            .SelectMany(d => SafeEnumerateFiles(d, "Model_*.gv"))
            .Distinct()
            .ToArray();

        if (gvFiles.Length == 0)
        {
            return @"<div style='padding: 10px; border: 1px solid #d9534f; background: #f2dede; border-radius: 5px;'>
                Aucun fichier .gv trouve.<br/>
                Activez <code>ShowFactorGraph = true</code> sur le moteur d'inference.
            </div>";
        }

        var latestGv = gvFiles
            .OrderByDescending(f => new FileInfo(f).LastWriteTime)
            .First();

        return ConvertAndGetGvHtml(latestGv, maxWidth);
    }

    /// <summary>
    /// Nettoie les fichiers .gv et .svg generes
    /// </summary>
    public static int CleanupGeneratedFiles()
    {
        var files = GetFactorGraphSearchDirectories()
            .SelectMany(d => SafeEnumerateFiles(d, "Model_*.gv"))
            .Concat(GetFactorGraphSearchDirectories()
                .SelectMany(d => SafeEnumerateFiles(d, "Model_*.svg")))
            .Distinct();

        int count = 0;
        foreach (var file in files)
        {
            try { File.Delete(file); count++; } catch { }
        }
        return count;
    }

    /// <summary>
    /// Configure un InferenceEngine pour generer des factor graphs
    /// </summary>
    public static void ConfigureEngine(dynamic engine)
    {
        engine.ShowFactorGraph = true;
        engine.Compiler.WriteSourceFiles = true;
        engine.Compiler.GeneratedSourceFolder = "GeneratedSource";
    }
}
