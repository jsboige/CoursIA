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
    internal static string[] GetFactorGraphSearchDirectories(string? scope = null)
    {
        var seen = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        var list = new List<string>();
        void Add(string p)
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

        // Sous-dossier GeneratedSource : Infer.NET.Compiler.GeneratedSourceFolder
        // vaut "GeneratedSource" par defaut, donc les .gv sont sous {cwd}/GeneratedSource/
        // et le pattern Model_*.gv ne les trouve pas au niveau superieur. Voir #18672.
        var roots = list.ToArray();
        foreach (var root in roots)
        {
            Add(Path.Combine(root, "GeneratedSource"));
            // Portee par carnet/modele : les artefacts ecrits sous un sous-dossier de
            // nom de portee (ConfigureEngine(engine, scope) -> GeneratedSource/<scope>/)
            // ne sont pas vus par TopDirectoryOnly au niveau GeneratedSource/ ; on
            // l'ajoute explicitement pour que la portee devienne effective (defaut
            // #25276, remede 1+2).
            if (!string.IsNullOrEmpty(scope))
            {
                Add(Path.Combine(root, "GeneratedSource", scope));
            }
        }

        return list.ToArray();
    }

    public static string GetLatestFactorGraphHtml(int maxWidth = 800, string? modelScope = null)
    {
        var gvFiles = GetFactorGraphSearchDirectories(modelScope)
            .SelectMany(d => SafeEnumerateFiles(d, "Model_*.gv"))
            .Distinct()
            .ToArray();
        var svgFiles = GetFactorGraphSearchDirectories(modelScope)
            .SelectMany(d => SafeEnumerateFiles(d, "Model_*.svg"))
            .Distinct()
            .ToArray();

        // Prefere reconvertir le .gv (la source de verite produite par la
        // derniere inference) quand Graphviz est disponible, pour que le graphe
        // affiche corresponde au modele courant et non a un .svg perime ou issu
        // d'un autre modele (bug #3473 stale-pick). La portee est transmise :
        // un .gv unique dans la portee est choisi, l'ambiguite est nommee
        // (defaut #25276).
        if (gvFiles.Length > 0 && IsGraphvizAvailable())
        {
            return ConvertAndGetLatestGvHtml(maxWidth, modelScope);
        }

        // Sinon (Graphviz absent, ou seulement un .svg pre-rendu disponible),
        // reutiliser le .svg de la portee s'il existe — selection unique,
        // jamais par mtime global.
        if (svgFiles.Length > 0)
        {
            var chosenSvg = SelectFactorGraphFile(svgFiles, modelScope, out int svgRemaining);
            if (chosenSvg == null)
            {
                return FormatGraphUnavailable(svgRemaining, modelScope, "svg");
            }
            return GetSvgFileHtml(chosenSvg, maxWidth);
        }

        return ConvertAndGetLatestGvHtml(maxWidth, modelScope);
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
    /// Selectionne UNIQUEMENT un fichier de graphe parmi une liste de candidats,
    /// sans jamais trancher par <c>LastWriteTime</c> global quand l'ensemble est
    /// ambiguo (defaut #25276 : deux carnets du meme dossier <c>Probas/Infer/</c>
    /// s'echangent mutuellement leur graphe car le "plus recent" global est une
    /// course d'horodatage, pas une portee par carnet).
    ///
    /// Regle de selection :
    /// <list type="bullet">
    /// <item><c>scope</c> non nul : ne garder que les candidats dont le chemin
    /// contient <c>scope</c> (le nom de modele du carnet appelant, transmis par
    /// celui-ci) ;</item>
    /// <item>exactement <b>1</b> candidat restant : il est choisi (deterministe,
    /// pas de course) ;</item>
    /// <item><b>0</b> ou <b>plusieurs</b> candidats restants : <b>pas</b> de
    /// selection — le caller rend un message qui nomme l'ambiguite (ou l'absence)
    /// plutot qu'un choix silencieux.</item>
    /// </list>
    ///
    /// Fonction pure (aucun acces disque) : testable en isolation.
    /// </summary>
    /// <param name="candidates">Fichiers candidats (deja distincts).</param>
    /// <param name="scope">Cle de portee optionnelle (sous-chaine du chemin), ou null.</param>
    /// <param name="remaining">Nombre de candidats apres le filtre de portee :
    /// 0 = aucun, 1 = selection, &gt;1 = ambiguo.</param>
    /// <returns>Le fichier choisi, ou null (aucun, ou ambiguo).</returns>
    internal static string? SelectFactorGraphFile(
        IReadOnlyCollection<string> candidates, string? scope, out int remaining)
    {
        var kept = candidates
            .Where(f => string.IsNullOrEmpty(scope)
                || f.Contains(scope, StringComparison.OrdinalIgnoreCase))
            .Distinct()
            .ToList();
        remaining = kept.Count;
        return kept.Count == 1 ? kept[0] : null;
    }

    /// <summary>
    /// Rend le HTML d'information quand aucun graphe ne peut etre selectionne de
    /// facon non-ambigue : soit aucun fichier n'existe (<c>remaining == 0</c>),
    /// soit plusieurs coexistent (<c>remaining &gt; 1</c>, ambiguite nommee —
    /// on refuse un choix par mtime global, cf #25276).
    /// </summary>
    private static string FormatGraphUnavailable(int remaining, string? scope, string ext)
    {
        if (remaining == 0)
        {
            var scopeNote = string.IsNullOrEmpty(scope)
                ? ""
                : $", pour la portee <code>{scope}</code>";
            return $@"<div style='padding: 10px; border: 1px solid #d9534f; background: #f2dede; border-radius: 5px;'>
                Aucun fichier .{ext} trouve{scopeNote}.<br/>
                Activez <code>ShowFactorGraph = true</code> sur le moteur d'inference.
            </div>";
        }
        return $@"<div style='padding: 10px; border: 1px solid #f0ad4e; background: #fcf8e3; border-radius: 5px;'>
            <strong>Grille de facteurs ambigue : {remaining} fichiers .{ext} en cours.</strong><br/>
            Plusieurs carnets ont ecrit des <code>Model_*.{ext}</code> au meme endroit ;
            choisir le plus recent global serait un choix silencieux (defaut #25276).<br/>
            Passez la portee du carnet a <code>GetLatestFactorGraphHtml</code>
            (argument <code>modelScope</code> = nom de modele distinctif) pour afficher
            le bon graphe.
        </div>";
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
    /// Trouve et convertit le .gv de la portee demandee, retourne le HTML.
    ///
    /// <paramref name="modelScope"/> (optionnel) borne la selection aux
    /// candidats dont le chemin contient cette cle (le nom de modele du carnet
    /// appelant). Sans portee, un seul candidat dans tout l'espace de recherche
    /// est choisi ; plusieurs candidats = ambiguite nommee, jamais un choix par
    /// <c>LastWriteTime</c> global (defaut #25276 : les carnets de
    /// <c>Probas/Infer/</c> s'echangent mutuellement leur graphe).
    /// </summary>
    public static string ConvertAndGetLatestGvHtml(int maxWidth = 800, string? modelScope = null)
    {
        var gvFiles = GetFactorGraphSearchDirectories(modelScope)
            .SelectMany(d => SafeEnumerateFiles(d, "Model_*.gv"))
            .Distinct()
            .ToArray();

        if (gvFiles.Length == 0)
        {
            return FormatGraphUnavailable(0, modelScope, "gv");
        }

        var chosen = SelectFactorGraphFile(gvFiles, modelScope, out int remaining);
        if (chosen == null)
        {
            return FormatGraphUnavailable(remaining, modelScope, "gv");
        }

        return ConvertAndGetGvHtml(chosen, maxWidth);
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
    public static void ConfigureEngine(dynamic engine, string? scope = null)
    {
        engine.ShowFactorGraph = true;
        engine.Compiler.WriteSourceFiles = true;
        // Portee par carnet/modele : ecrire les artefacts sous GeneratedSource/<scope>/
        // pour que la selection par portee (SelectFactorGraphFile) devienne effective.
        // Les noms de fichiers Infer.NET sont des horodatages purs (Model_<ts>.gv),
        // sans identite de modele : la portee ne peut matcher que le chemin, donc le
        // dossier d'ecriture doit le porter (defaut #25276, remede 1+2).
        engine.Compiler.GeneratedSourceFolder = string.IsNullOrEmpty(scope)
            ? "GeneratedSource"
            : Path.Combine("GeneratedSource", scope);
    }
}
