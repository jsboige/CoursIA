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

/// <summary>Style de trace pour <see cref="SvgChartHelper.Overlay"/>.</summary>
public enum TraceStyle { Line, Markers, LineMarkers }

/// <summary>
/// Une serie de <see cref="SvgChartHelper.Overlay"/> : label (legende) + points (xs, ys) sur un
/// axe X numerique partage, style de trace, couleur (null = palette auto) et sigma optionnel
/// (barres d'erreur +-1 sigma tracees par point).
/// </summary>
public sealed record SvgSeries(string Label, double[] Xs, double[] Ys,
    TraceStyle Style = TraceStyle.LineMarkers, string Color = null, double[] Sigma = null);

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

    /// <summary>
    /// Superposition multi-series sur un axe X numerique partage. Chaque serie se trace en ligne,
    /// marqueurs, ou ligne+marqueurs, avec des barres d'erreur +-sigma optionnelles. Une legende
    /// est generee automatiquement a partir des labels. Rend un SVG inline statique (GitHub /
    /// nbviewer / offline), unique primitive multi-trace du helper (les series a courbe unique
    /// restent servies par <see cref="Line"/> / <see cref="Scatter"/> / <see cref="Bar"/>).
    /// </summary>
    public static SvgChart Overlay(string title, string xLabel, string yLabel,
        IReadOnlyList<SvgSeries> series, int width = 820, int height = 480)
        => new SvgChart(BuildOverlay(title, xLabel, yLabel, series, width, height));

    /// <summary>
    /// Carte de chaleur (heatmap) sur une grille categorielle : <paramref name="values"/>[ligne][colonne]
    /// mappee a une palette sequentielle interpolant <paramref name="colorLow"/> (valeur min) vers
    /// <paramref name="colorHigh"/> (valeur max). Les lignes = <paramref name="yLabels"/> (ex. variantes),
    /// les colonnes = <paramref name="xLabels"/> (ex. positions N). Rend les bandes de periodicite
    /// d'une sequence (ex. valeurs de Grundy) visibles d'un coup d'oeil. SVG inline statique.
    /// </summary>
    public static SvgChart Heatmap(string title, string[] xLabels, string[] yLabels,
        double[][] values, int width = 640, int height = 320,
        string colorLow = "#F7FBFF", string colorHigh = "#08306B")
        => new SvgChart(BuildHeatmap(title, xLabels, yLabels, values, width, height, colorLow, colorHigh));

    /// <summary>
    /// Barres groupees : pour chaque categorie, plusieurs series tracees cote a cote (ex.
    /// comparaison de N solveurs sur une meme famille de problemes, ou score multi-criteres par
    /// methode). Une legende (haut-droite) identifie chaque serie par sa couleur. SVG inline statique.
    /// </summary>
    /// <param name="categories">Labels de l'axe X (une entree par groupe).</param>
    /// <param name="seriesValues">Une sous-liste par serie ; chaque sous-liste a une valeur par categorie.</param>
    /// <param name="seriesLabels">Nom de chaque serie (legende), une entree par serie.</param>
    /// <param name="colors">Couleurs optionnelles par serie (defaut = palette SvgChartHelper).</param>
    public static SvgChart GroupedBar(string title, string[] categories,
        double[][] seriesValues, string[] seriesLabels,
        int width = 640, int height = 360, string[] colors = null)
        => new SvgChart(BuildGroupedBar(title, categories, seriesValues, seriesLabels, width, height, colors));

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

    private static string BuildGroupedBar(string title, string[] categories,
        double[][] seriesValues, string[] seriesLabels, int w, int h, string[] colors)
    {
        int catCount = categories?.Length ?? 0;
        int seriesCount = seriesValues?.Length ?? 0;
        if (catCount == 0 || seriesCount == 0)
            throw new ArgumentException("GroupedBar: categories et seriesValues ne doivent pas etre vides.");
        if (seriesLabels == null || seriesLabels.Length != seriesCount)
            throw new ArgumentException("GroupedBar: seriesLabels doit avoir une entree par serie.");
        for (int j = 0; j < seriesCount; j++)
            if (seriesValues[j] == null || seriesValues[j].Length != catCount)
                throw new ArgumentException("GroupedBar: chaque serie doit avoir une valeur par categorie.");

        // Bornes Y sur l'union de toutes les series (NiceBounds attend un double[] plat).
        double[] all = new double[catCount * seriesCount];
        int k = 0;
        for (int j = 0; j < seriesCount; j++)
            for (int i = 0; i < catCount; i++)
                all[k++] = seriesValues[j][i];
        var (yMin, yMax) = NiceBounds(all);
        var layout = new PlotLayout(w, h, yMin, yMax, catCount);

        string[] palette = { ColorPrimary, ColorAccent, "#DD8452", ColorNegative, "#8172B3", "#937860" };
        string SeriesColor(int j) => colors != null && j < colors.Length ? colors[j] : palette[j % palette.Length];

        var sb = new StringBuilder();
        sb.Append(OpenSvg(w, h, title));
        sb.Append(GridAndYAxis(layout));

        // Groupe = 80% de la cellule categorie ; sous-barres cote a cote, centrees sur CatX(i).
        double groupW = (layout.PlotW / (double)catCount) * 0.80;
        double barW = groupW / seriesCount;
        for (int i = 0; i < catCount; i++)
        {
            double gx = layout.CatX(i) - groupW / 2.0;
            for (int j = 0; j < seriesCount; j++)
            {
                double v = seriesValues[j][i];
                double barH = Math.Abs(v - 0) / layout.YRange * layout.PlotH;
                // y = sommet (SVG) de la barre : Y(v) si v>=0, Y(0) si v<0 (geometrie = BuildBar).
                double y = v >= 0 ? layout.Y(v) : layout.Y(0);
                sb.Append($"<rect x='{F(gx + j * barW)}' y='{F(y)}' width='{F(barW)}' height='{F(barH)}' fill='{SeriesColor(j)}'/>");
            }
            sb.Append(CategoryLabel(layout, layout.CatX(i), categories[i]));
        }

        // Legende (haut-droite de la zone de plot), une entree par serie : carre couleur + label.
        double lx = layout.PadL + layout.PlotW - 172, ly = layout.PadT + 8;
        double lh = 14 + seriesCount * 18;
        sb.Append($"<rect x='{F(lx)}' y='{F(ly)}' width='168' height='{F(lh)}' fill='white' stroke='{ColorGrid}' stroke-width='1'/>");
        for (int j = 0; j < seriesCount; j++)
        {
            double ey = ly + 16 + j * 18;
            sb.Append($"<rect x='{F(lx + 12)}' y='{F(ey - 9)}' width='12' height='8' fill='{SeriesColor(j)}'/>");
            sb.Append($"<text x='{F(lx + 30)}' y='{F(ey)}' fill='{ColorText}'>{Esc(seriesLabels[j])}</text>");
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

    private static string BuildOverlay(string title, string xLabel, string yLabel,
        IReadOnlyList<SvgSeries> series, int w, int h)
    {
        if (series == null || series.Count == 0)
            throw new ArgumentException("Overlay: au moins une serie requise.");
        foreach (var s in series)
            if (s.Xs == null || s.Ys == null || s.Xs.Length != s.Ys.Length || s.Xs.Length == 0)
                throw new ArgumentException($"Overlay: serie '{s.Label}' doit avoir xs/ys de meme longueur non nulle.");

        // Bornes X (union de toutes les series) et Y (union ys +- sigma).
        double xMin = double.PositiveInfinity, xMax = double.NegativeInfinity;
        double yLo = double.PositiveInfinity, yHi = double.NegativeInfinity;
        foreach (var s in series)
            for (int i = 0; i < s.Xs.Length; i++)
            {
                xMin = Math.Min(xMin, s.Xs[i]); xMax = Math.Max(xMax, s.Xs[i]);
                double sig = (s.Sigma != null && i < s.Sigma.Length) ? Math.Abs(s.Sigma[i]) : 0.0;
                yLo = Math.Min(yLo, s.Ys[i] - sig); yHi = Math.Max(yHi, s.Ys[i] + sig);
            }
        double xRange = xMax - xMin; if (xRange == 0) xRange = 1;
        double ypad = (yHi - yLo) * 0.06; if (ypad == 0) ypad = Math.Max(1, Math.Abs(yHi) * 0.1);
        var layout = new PlotLayout(w, h, yLo - ypad, yHi + ypad, series.Count);
        Func<double, double> PX = x => layout.PadL + (x - xMin) / xRange * layout.PlotW;

        var sb = new StringBuilder();
        sb.Append(OpenSvg(w, h, title));
        sb.Append(GridAndYAxis(layout));

        // Graduations X numeriques (5 ticks) + labels d'axes.
        for (int g = 0; g <= 4; g++)
        {
            double xv = xMin + xRange * g / 4.0;
            double pxg = layout.PadL + layout.PlotW * g / 4.0;
            sb.Append($"<text x='{F(pxg)}' y='{h - layout.PadB + 16}' text-anchor='middle' fill='{ColorText}'>{F(xv)}</text>");
        }
        if (!string.IsNullOrEmpty(xLabel))
            sb.Append($"<text x='{F(layout.PadL + layout.PlotW / 2.0)}' y='{h - 6}' text-anchor='middle' fill='{ColorText}'>{Esc(xLabel)}</text>");
        if (!string.IsNullOrEmpty(yLabel))
        {
            double cy = layout.PadT + layout.PlotH / 2.0;
            sb.Append($"<text x='14' y='{F(cy)}' text-anchor='middle' fill='{ColorText}' transform='rotate(-90 14 {F(cy)})'>{Esc(yLabel)}</text>");
        }

        string[] palette = { ColorPrimary, ColorAccent, "#DD8452", ColorNegative, "#8172B3", "#937860" };
        for (int si = 0; si < series.Count; si++)
        {
            var s = series[si];
            string color = s.Color ?? palette[si % palette.Length];
            var pts = new List<string>(s.Xs.Length);
            for (int i = 0; i < s.Xs.Length; i++)
                pts.Add($"{F(PX(s.Xs[i]))},{F(layout.Y(s.Ys[i]))}");
            bool line = s.Style == TraceStyle.Line || s.Style == TraceStyle.LineMarkers;
            bool marks = s.Style == TraceStyle.Markers || s.Style == TraceStyle.LineMarkers;

            if (line)
                sb.Append($"<polyline points='{string.Join(" ", pts)}' fill='none' stroke='{color}' stroke-width='2'/>");

            // Barres d'erreur +-sigma (tracees avant les marqueurs pour rester dessous).
            if (s.Sigma != null)
                for (int i = 0; i < s.Xs.Length && i < s.Sigma.Length; i++)
                {
                    double xp = PX(s.Xs[i]);
                    double yTop = layout.Y(s.Ys[i] + Math.Abs(s.Sigma[i]));
                    double yBot = layout.Y(s.Ys[i] - Math.Abs(s.Sigma[i]));
                    sb.Append($"<line x1='{F(xp)}' y1='{F(yTop)}' x2='{F(xp)}' y2='{F(yBot)}' stroke='{color}' stroke-opacity='0.4' stroke-width='1.5'/>");
                    sb.Append($"<line x1='{F(xp - 3)}' y1='{F(yTop)}' x2='{F(xp + 3)}' y2='{F(yTop)}' stroke='{color}' stroke-opacity='0.4' stroke-width='1.5'/>");
                    sb.Append($"<line x1='{F(xp - 3)}' y1='{F(yBot)}' x2='{F(xp + 3)}' y2='{F(yBot)}' stroke='{color}' stroke-opacity='0.4' stroke-width='1.5'/>");
                }

            if (marks)
                foreach (var p in pts)
                {
                    var xy = p.Split(',');
                    sb.Append($"<circle cx='{xy[0]}' cy='{xy[1]}' r='3' fill='{color}'/>");
                }
        }

        // Legende (haut-droite de la zone de plot), une entree par serie.
        double lx = layout.PadL + layout.PlotW - 172, ly = layout.PadT + 8;
        double lh = 14 + series.Count * 18;
        sb.Append($"<rect x='{F(lx)}' y='{F(ly)}' width='168' height='{F(lh)}' fill='white' stroke='{ColorGrid}' stroke-width='1'/>");
        for (int si = 0; si < series.Count; si++)
        {
            var s = series[si];
            string color = s.Color ?? palette[si % palette.Length];
            double ey = ly + 16 + si * 18;
            if (s.Style == TraceStyle.Markers)
                sb.Append($"<circle cx='{F(lx + 22)}' cy='{F(ey - 4)}' r='3' fill='{color}'/>");
            else
                sb.Append($"<line x1='{F(lx + 10)}' y1='{F(ey - 4)}' x2='{F(lx + 34)}' y2='{F(ey - 4)}' stroke='{color}' stroke-width='2'/>");
            sb.Append($"<text x='{F(lx + 42)}' y='{F(ey)}' fill='{ColorText}'>{Esc(s.Label)}</text>");
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

    // Carte de chaleur : grille de cellules colorees par interpolation sequentielle colorLow->colorHigh.
    private static string BuildHeatmap(string title, string[] xLabels, string[] yLabels,
        double[][] values, int w, int h, string colorLow, string colorHigh)
    {
        int nR = yLabels.Length, nC = xLabels.Length;
        if (values == null || values.Length != nR)
            throw new ArgumentException("Heatmap: values doit avoir yLabels.Length lignes.");
        foreach (var row in values)
            if (row == null || row.Length != nC)
                throw new ArgumentException("Heatmap: chaque ligne de values doit avoir xLabels.Length colonnes.");

        double vMin = double.PositiveInfinity, vMax = double.NegativeInfinity;
        foreach (var row in values)
            foreach (var v in row) { vMin = Math.Min(vMin, v); vMax = Math.Max(vMax, v); }
        double vRange = (vMax - vMin == 0 ? 1 : vMax - vMin);

        int padL = 104, padR = 16, padT = 34, padB = 52;
        double plotW = w - padL - padR, plotH = h - padT - padB;
        double cellW = plotW / nC, cellH = plotH / nR;

        var sb = new StringBuilder();
        sb.Append(OpenSvg(w, h, title));
        for (int r = 0; r < nR; r++)
        {
            double yTop = padT + r * cellH;
            for (int c = 0; c < nC; c++)
            {
                double xLeft = padL + c * cellW;
                double t = (values[r][c] - vMin) / vRange;
                string fill = InterpolateHex(colorLow, colorHigh, t);
                sb.Append($"<rect x='{F(xLeft)}' y='{F(yTop)}' width='{F(cellW)}' height='{F(cellH)}' fill='{fill}'/>");
            }
        }
        // Labels de colonnes (axe X) sous la grille.
        for (int c = 0; c < nC; c++)
        {
            double cx = padL + (c + 0.5) * cellW;
            sb.Append($"<text x='{F(cx)}' y='{h - padB + 16}' text-anchor='middle' fill='{ColorText}'>{Esc(xLabels[c])}</text>");
        }
        // Labels de lignes (axe Y) a gauche de la grille.
        for (int r = 0; r < nR; r++)
        {
            double cy = padT + (r + 0.5) * cellH;
            sb.Append($"<text x='{padL - 6}' y='{F(cy + 4)}' text-anchor='end' fill='{ColorText}'>{Esc(yLabels[r])}</text>");
        }
        // Bordure de grille + legende de l'echelle (min/max).
        sb.Append($"<rect x='{padL}' y='{padT}' width='{F(plotW)}' height='{F(plotH)}' fill='none' stroke='{ColorAxis}' stroke-width='1'/>");
        sb.Append($"<text x='{padL}' y='{h - padB + 34}' text-anchor='start' fill='{ColorText}'>{F(vMin)} (min)</text>");
        sb.Append($"<text x='{w - padR}' y='{h - padB + 34}' text-anchor='end' fill='{ColorText}'>(max) {F(vMax)}</text>");
        sb.Append(CloseSvg());
        return sb.ToString();
    }

    // Interpolation lineaire entre deux couleurs hex (#RRGGBB ou #RGB) au facteur t dans [0,1].
    private static string InterpolateHex(string hexLow, string hexHigh, double t)
    {
        t = Math.Max(0, Math.Min(1, t));
        var (lr, lg, lb) = ParseHex(hexLow);
        var (hr, hg, hb) = ParseHex(hexHigh);
        int r = (int)Math.Round(lr + (hr - lr) * t);
        int g = (int)Math.Round(lg + (hg - lg) * t);
        int b = (int)Math.Round(lb + (hb - lb) * t);
        return $"#{r:X2}{g:X2}{b:X2}";
    }

    private static (int r, int g, int b) ParseHex(string hex)
    {
        string h = (hex ?? "#000000").TrimStart('#');
        if (h.Length == 3) h = string.Concat($"{h[0]}", $"{h[0]}", $"{h[1]}", $"{h[1]}", $"{h[2]}", $"{h[2]}");
        int r = Convert.ToInt32(h.Substring(0, 2), 16);
        int g = Convert.ToInt32(h.Substring(2, 2), 16);
        int b = Convert.ToInt32(h.Substring(4, 2), 16);
        return (r, g, b);
    }

    // Echappement XML du texte (titres, labels) : manuel, zero-dependance (pas de System.Xml.Linq,
    // non reference par defaut dans le kernel .NET Interactive -> evite un hang de resolution).
    private static string Esc(string text)
        => (text ?? "").Replace("&", "&amp;").Replace("<", "&lt;").Replace(">", "&gt;")
                       .Replace("'", "&apos;").Replace("\"", "&quot;");
}
