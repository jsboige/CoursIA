// SvgChartHelper.cs - Helper pour generer des graphiques SVG STATIQUES inline dans les notebooks .NET
// Usage dans un notebook: #load "SvgChartHelper.cs"
//
// Zero-dependance : pur C# (echappement XML manuel), AUCUN nuget / kaleido / node.
// Rend sur GitHub / nbviewer / offline (SVG = XML inline, pas de <script>, pas de CDN externe).
//
// Contexte : remplace le canon `record PlotlyHtml` (#6694/#6695/#6696) dont la sortie
// `<script src="https://cdn.plot.ly/..."></script>` rendait BLANC en consultation statique
// (GitHub sandbox les <script>). Ici le rendu est un <svg>... </svg> embarque qui s'affiche
// partout. L'interactivite (tooltips/zoom) est perdue, mais la portabilite du rendu est gagnee.
// Cf #6927 / #3801 (Prong-A : vrai rendu statique zero-dependance, pas un workaround degrade).
// L'investigation firsthand (po-2025, c.553) a elimine (a) Plotly.NET/kaleido (timeout >=150s)
// et (c) ScottPlot (restore timeout >=240s) sur worker CPU ; seule (b) SVG inline est viable.

using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Text;
using Microsoft.DotNet.Interactive.Formatting;

/// <summary>
/// Conteneur de rendu SVG. Enregistrer via <see cref="SvgChartHelper"/> (Formatter text/html)
/// pour qu'un <c>display(SvgChartHelper.Bar(...))</c> affiche le SVG inline dans le notebook.
/// </summary>
public record SvgChart(string Markup);

/// <summary>
/// Generateur de graphiques SVG statiques zero-dependance. Rend sur GitHub/nbviewer/offline.
/// <example>
/// <code>
/// #load "SvgChartHelper.cs"
/// display(SvgChartHelper.Bar("EVPI vs P(petrole)", new[]{"0.1","0.3","0.5"}, new[]{0.5,1.2,2.0}));
/// display(SvgChartHelper.Line("Convergence mu", new[]{"m1","m2","m3"}, new[]{25,27.5,29}));
/// display(SvgChartHelper.Scatter("skill vs perf", new[]{1,2,3,4}, new[]{2,3.9,6.1,8}));
/// </code>
/// </example>
/// </summary>
public static class SvgChartHelper
{
    // Palette (alignee sur le canon PlotlyHtml C548-L2 : bleu positif, rouge negatif).
    private const string ColorPrimary = "#4C72B0";
    private const string ColorNegative = "#C44E52";
    private const string ColorAccent = "#55A868";
    private const string ColorAxis = "#888888";
    private const string ColorGrid = "#E5E5E5";
    private const string ColorText = "#333333";

    static SvgChartHelper()
    {
        // Enregistrement idempotent du Formatter : un SvgChart s'affiche comme SVG inline.
        // Re-enregistrer ecrase simplement l'entree precedente (safe si #load plusieurs fois).
        Formatter.Register(typeof(SvgChart),
            (obj, writer) => ((TextWriter)writer).Write(((SvgChart)obj).Markup), "text/html");
    }

    // ---------------------------------------------------------------------------------------------
    // API publique
    // ---------------------------------------------------------------------------------------------

    /// <summary>Diagramme en barres verticales. Valeurs negatives tracees vers le bas.</summary>
    public static SvgChart Bar(string title, string[] categories, double[] values,
        int width = 560, int height = 320, string color = null)
        => new SvgChart(BuildBar(title, categories, values, width, height, color ?? ColorPrimary));

    /// <summary>Graphique lineaire (polyline + marqueurs).</summary>
    public static SvgChart Line(string title, string[] categories, double[] values,
        int width = 560, int height = 320, string color = null)
        => new SvgChart(BuildLine(title, categories, values, width, height, color ?? ColorPrimary));

    /// <summary>Nuage de points (axes numeriques x et y).</summary>
    public static SvgChart Scatter(string title, double[] xs, double[] ys,
        int width = 560, int height = 320, string color = null)
        => new SvgChart(BuildScatter(title, xs, ys, width, height, color ?? ColorAccent));

    // ---------------------------------------------------------------------------------------------
    // Generateurs
    // ---------------------------------------------------------------------------------------------

    private static string BuildBar(string title, string[] categories, double[] values,
        int w, int h, string color)
    {
        int n = AssertPairs(categories, values);
        var (yMin, yMax) = NiceBounds(values);
        var layout = new PlotLayout(w, h, yMin, yMax, categories.Length);

        var sb = new StringBuilder();
        sb.Append(OpenSvg(w, h, title));
        sb.Append(GridAndYAxis(layout));
        double cell = layout.PlotW / (double)n;
        double barW = cell * 0.62;
        for (int i = 0; i < n; i++)
        {
            double v = values[i];
            double x = layout.PadL + i * cell + (cell - barW) / 2.0;
            double barH = Math.Abs(v - 0) / layout.YRange * layout.PlotH;
            // y = sommet (SVG) de la barre : Y(v) si v>=0 (croit vers le haut depuis 0),
            // Y(0) si v<0 (croit vers le bas depuis 0). Hauteur = barH.
            double y = v >= 0 ? layout.Y(v) : layout.Y(0);
            string c = v >= 0 ? color : ColorNegative;
            sb.Append($"<rect x='{F(x)}' y='{F(y)}' width='{F(barW)}' height='{F(barH)}' fill='{c}'/>");
            sb.Append(CategoryLabel(layout, x + barW / 2.0, categories[i]));
        }
        sb.Append(CloseSvg());
        return sb.ToString();
    }

    private static string BuildLine(string title, string[] categories, double[] values,
        int w, int h, string color)
    {
        int n = AssertPairs(categories, values);
        var (yMin, yMax) = NiceBounds(values);
        var layout = new PlotLayout(w, h, yMin, yMax, n);

        var sb = new StringBuilder();
        sb.Append(OpenSvg(w, h, title));
        sb.Append(GridAndYAxis(layout));
        var pts = new List<string>(n);
        for (int i = 0; i < n; i++)
        {
            double x = layout.CatX(i);
            double y = layout.Y(values[i]);
            pts.Add($"{F(x)},{F(y)}");
            sb.Append(CategoryLabel(layout, x, categories[i]));
        }
        sb.Append($"<polyline points='{string.Join(" ", pts)}' fill='none' stroke='{color}' stroke-width='2'/>");
        foreach (var p in pts)
            sb.Append($"<circle cx='{p.Split(',')[0]}' cy='{p.Split(',')[1]}' r='3' fill='{color}'/>");
        sb.Append(CloseSvg());
        return sb.ToString();
    }

    private static string BuildScatter(string title, double[] xs, double[] ys,
        int w, int h, string color)
    {
        if (xs == null || ys == null || xs.Length != ys.Length || xs.Length == 0)
            throw new ArgumentException("Scatter: xs et ys doivent etre de meme longueur non nulle.");
        int n = xs.Length;
        double xMin = xs.Min(), xMax = xs.Max();
        double yMin = ys.Min(), yMax = ys.Max();
        var (nyMin, nyMax) = NiceBounds(ys);
        var layout = new PlotLayout(w, h, nyMin, nyMax, n);
        double xRange = (xMax - xMin); if (xRange == 0) xRange = 1;

        var sb = new StringBuilder();
        sb.Append(OpenSvg(w, h, title));
        sb.Append(GridAndYAxis(layout));
        // Axe X numerique : 5 graduations
        for (int g = 0; g <= 4; g++)
        {
            double xv = xMin + xRange * g / 4.0;
            double px = layout.PadL + layout.PlotW * g / 4.0;
            sb.Append($"<text x='{F(px)}' y='{h - layout.PadB + 16}' text-anchor='middle' fill='{ColorText}'>{F(xv)}</text>");
        }
        for (int i = 0; i < n; i++)
        {
            double px = layout.PadL + (xs[i] - xMin) / xRange * layout.PlotW;
            double py = layout.Y(ys[i]);
            sb.Append($"<circle cx='{F(px)}' cy='{F(py)}' r='4' fill='{color}'/>");
        }
        sb.Append(CloseSvg());
        return sb.ToString();
    }

    // ---------------------------------------------------------------------------------------------
    // Layout & helpers
    // ---------------------------------------------------------------------------------------------

    private readonly struct PlotLayout
    {
        public readonly int W, H, N, PadL, PadR, PadT, PadB, PlotW, PlotH;
        public readonly double YMin, YMax, YRange;
        public PlotLayout(int w, int h, double yMin, double yMax, int n)
        {
            W = w; H = h; N = Math.Max(1, n); PadL = 52; PadR = 16; PadT = 34; PadB = 42;
            PlotW = w - PadL - PadR; PlotH = h - PadT - PadB;
            YMin = yMin; YMax = yMax; YRange = (yMax - yMin == 0 ? 1 : yMax - yMin);
        }
        public double Y(double v) => PadT + PlotH * (1 - (v - YMin) / YRange); // SVG y croit vers le bas
        public double CatX(int i) => PadL + (i + 0.5) * (PlotW / (double)N);
    }

    private static string OpenSvg(int w, int h, string title)
    {
        var t = Esc(title);
        return $"<svg xmlns='http://www.w3.org/2000/svg' width='{w}' height='{h}' viewBox='0 0 {w} {h}'" +
               $" font-family='sans-serif' font-size='12'>" +
               $"<rect width='{w}' height='{h}' fill='white'/>" +
               $"<text x='{w / 2}' y='20' text-anchor='middle' font-size='14' font-weight='bold' fill='{ColorText}'>{t}</text>";
    }

    private static string CloseSvg() => "</svg>";

    private static string GridAndYAxis(PlotLayout l)
    {
        var sb = new StringBuilder();
        // 5 lignes de grille + labels Y
        for (int g = 0; g <= 4; g++)
        {
            double yv = l.YMin + l.YRange * g / 4.0;
            double py = l.Y(yv);
            sb.Append($"<line x1='{l.PadL}' y1='{F(py)}' x2='{l.W - l.PadR}' y2='{F(py)}' stroke='{ColorGrid}' stroke-width='1'/>");
            sb.Append($"<text x='{l.PadL - 8}' y='{F(py + 4)}' text-anchor='end' fill='{ColorText}'>{F(yv)}</text>");
        }
        // Axe vertical
        sb.Append($"<line x1='{l.PadL}' y1='{l.PadT}' x2='{l.PadL}' y2='{l.H - l.PadB}' stroke='{ColorAxis}' stroke-width='1'/>");
        // Axe horizontal a y=0 si dans la plage, sinon en bas
        double axisY = (l.YMin <= 0 && l.YMax >= 0) ? l.Y(0) : (l.H - l.PadB);
        sb.Append($"<line x1='{l.PadL}' y1='{F(axisY)}' x2='{l.W - l.PadR}' y2='{F(axisY)}' stroke='{ColorAxis}' stroke-width='1'/>");
        return sb.ToString();
    }

    private static string CategoryLabel(PlotLayout l, double x, string label)
        => $"<text x='{F(x)}' y='{l.H - l.PadB + 16}' text-anchor='middle' fill='{ColorText}'>{Esc(label)}</text>";

    // Bornes Y "propres" : incluent 0 si les valeurs le traversent ou sont toutes >=0,
    // avec une petite marge pour ne pas coller au bord.
    private static (double min, double max) NiceBounds(double[] values)
    {
        double lo = values.Min(), hi = values.Max();
        if (lo > 0) lo = 0;
        if (hi < 0) hi = 0;
        double pad = (hi - lo) * 0.08; if (pad == 0) pad = Math.Max(1, Math.Abs(hi) * 0.1);
        return (lo - (lo < 0 ? pad : 0), hi + pad);
    }

    private static int AssertPairs(string[] categories, double[] values)
    {
        if (categories == null || values == null || categories.Length != values.Length || values.Length == 0)
            throw new ArgumentException("categories et values doivent etre de meme longueur non nulle.");
        return values.Length;
    }

    // Format invariant (point decimal) pour les nombres dans les attributs SVG.
    private static string F(double v) => v.ToString("0.###", CultureInfo.InvariantCulture);

    // Echappement XML du texte (titres, labels) : manuel, zero-dependance (pas de System.Xml.Linq,
    // non reference par defaut dans le kernel .NET Interactive -> evite un hang de resolution).
    private static string Esc(string text)
        => (text ?? "").Replace("&", "&amp;").Replace("<", "&lt;").Replace(">", "&gt;")
                       .Replace("'", "&apos;").Replace("\"", "&quot;");
}
