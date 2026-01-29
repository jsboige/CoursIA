// FactorGraphHelper.cs - Helper pour afficher les graphes de facteurs Infer.NET inline
// Usage dans un notebook: #load "FactorGraphHelper.cs"

using System;
using System.IO;
using System.Linq;
using System.Diagnostics;

/// <summary>
/// Helper pour generer et afficher les factor graphs Infer.NET dans les notebooks Jupyter.
/// Necessite Graphviz installe pour la conversion .gv -> .svg
/// </summary>
public static class FactorGraphHelper
{
    private static bool? _graphvizAvailable = null;

    /// <summary>
    /// Verifie si Graphviz (dot) est disponible
    /// </summary>
    public static bool IsGraphvizAvailable()
    {
        if (_graphvizAvailable.HasValue) return _graphvizAvailable.Value;

        try
        {
            var psi = new ProcessStartInfo
            {
                FileName = "dot",
                Arguments = "-V",
                RedirectStandardError = true,
                RedirectStandardOutput = true,
                UseShellExecute = false,
                CreateNoWindow = true
            };
            using var proc = Process.Start(psi);
            proc.WaitForExit(3000);
            _graphvizAvailable = (proc.ExitCode == 0);
        }
        catch
        {
            _graphvizAvailable = false;
        }
        return _graphvizAvailable.Value;
    }

    /// <summary>
    /// Retourne le HTML pour afficher le dernier fichier SVG genere par Infer.NET
    /// Usage: display(HTML(FactorGraphHelper.GetLatestFactorGraphHtml()))
    /// </summary>
    public static string GetLatestFactorGraphHtml(int maxWidth = 800)
    {
        var svgFiles = Directory.GetFiles(Environment.CurrentDirectory, "Model_*.svg");

        if (svgFiles.Length > 0)
        {
            var latestSvg = svgFiles
                .OrderByDescending(f => new FileInfo(f).LastWriteTime)
                .First();
            return GetSvgFileHtml(latestSvg, maxWidth);
        }
        else
        {
            return ConvertAndGetLatestGvHtml(maxWidth);
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
                FileName = "dot",
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
        var gvFiles = Directory.GetFiles(Environment.CurrentDirectory, "Model_*.gv");

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
        var files = Directory.GetFiles(Environment.CurrentDirectory, "Model_*.gv")
            .Concat(Directory.GetFiles(Environment.CurrentDirectory, "Model_*.svg"));

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
