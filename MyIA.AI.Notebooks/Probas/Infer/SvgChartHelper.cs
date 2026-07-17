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

    /// <summary>
    /// Diagramme en barres verticales. Valeurs negatives tracees vers le bas.
    /// <para><paramref name="colors"/> (optionnel) : une couleur hex par barre (meme longueur que
    /// <paramref name="values"/>), pour porter une semantique par-barre — ex. bleu <c>#4C72B0</c> =
    /// rentable / orange <c>#DD8452</c> = non rentable — qu'une couleur unique ne peut exprimer.
    /// Quand fourni, prime sur <paramref name="color"/> et sur la couleur negative automatique.</para>
    /// <para><paramref name="legend"/> (optionnel) : entrees (couleur, label) rendues dans un encart
    /// de legende SVG inline (haut-droite) pour expliciter le code couleur, sans legende console ASCII.</para>
    /// <para><paramref name="yMax"/> (optionnel) : force le sommet de l'echelle Y (au lieu de la borne
    /// calculee automatiquement), pour comparer visuellement des barres entre plusieurs charts sur une
    /// echelle Y commune. Quand <c>null</c>, l'echelle est calculee comme avant (retro-compatible).</para>
    /// </summary>
    public static SvgChart Bar(string title, string[] categories, double[] values,
        int width = 560, int height = 320, string color = null,
        string[] colors = null, IReadOnlyList<(string Color, string Label)> legend = null,
        double? yMax = null)
        => new SvgChart(BuildBar(title, categories, values, width, height, color ?? ColorPrimary, colors, legend, yMax));

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
    /// <para><paramref name="logY"/> (opt-in, defaut <c>false</c>) : echelle Y logarithmique (base 10).
    /// Necesaire quand les Y couvrent un grand rapport (ex. 0.55 -> 34.38, ~63x) qu'une echelle lineaire
    /// ecrase. Exige des POINTS Y strictement positifs ; les barres d'erreur +-sigma qui croisent zero
    /// (borne inferieure negative) sont clippees au sol de l'axe plutot que de rejeter la donnee. Les graduations sont
    /// placees aux valeurs "propres" 1-2-5 x 10^k, labellees en valeur originale. Les barres d'erreur
    /// +-sigma deviennent asymetriques (correct en log). Backward-compatible : tous les appels existants
    /// sans <paramref name="logY"/> rendent en echelle lineaire, inchanges.</para>
    /// </summary>
    public static SvgChart Overlay(string title, string xLabel, string yLabel,
        IReadOnlyList<SvgSeries> series, int width = 820, int height = 480, bool logY = false)
        => new SvgChart(BuildOverlay(title, xLabel, yLabel, series, width, height, logY));

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
    /// <param name="logY">Si <c>true</c>, axe Y en echelle logarithmique (base 10). Adapté aux
    /// distributions de temps de calcul sur plusieurs ordres de grandeur (ex. benchmark de solveurs
    /// ou BT explose a 10000 ms pendant que Norvig reste a 3 ms). Valeurs <= 0 sont exclues de la
    /// borne basse avec clipping (cf L641-L3★ borne INF Math.Max) pour eviter l'explosion des ticks.
    /// Defaut <c>false</c> (retro-compatible).</param>
    public static SvgChart GroupedBar(string title, string[] categories,
        double[][] seriesValues, string[] seriesLabels,
        int width = 640, int height = 360, string[] colors = null, bool logY = false)
        => new SvgChart(BuildGroupedBar(title, categories, seriesValues, seriesLabels, width, height, colors, logY));

    /// <summary>
    /// Boites a moustaches (boxplots) : pour chaque categorie (ex. difficultes), une boite
    /// Q1..Q3, une medianne, des moustaches min/max, et un point individuel par observation
    /// (jitter horizontal aleatoire pour eviter le chevauchement). Une legende par serie
    /// (categorie de boxplot). SVG inline statique.
    /// </summary>
    /// <param name="categories">Labels de l'axe X (une entree par groupe de boites).</param>
    /// <param name="samples">Pour chaque categorie, une liste d'observations (les valeurs tracees).
    /// Si <paramref name="samples"/> est vide pour une categorie, la boite est omise.</param>
    /// <param name="logY">Si <c>true</c>, axe Y en echelle log10. Convention identique a
    /// <see cref="GroupedBar"/> : valeurs &lt;= 0 ramenees a la borne basse clippee, graduations
    /// en decades (cf L641-L3★ anti-explosion). Defaut <c>false</c>.</param>
    public static SvgChart BoxPlot(string title, string[] categories,
        IReadOnlyList<double[]> samples, int width = 720, int height = 400, bool logY = false)
        => new SvgChart(BuildBoxPlot(title, categories, samples, width, height, logY));

    // ---------------------------------------------------------------------------------------------
    // Generateurs
    // ---------------------------------------------------------------------------------------------

    private static string BuildBar(string title, string[] categories, double[] values,
        int w, int h, string color, string[] colors = null,
        IReadOnlyList<(string Color, string Label)> legend = null, double? yMaxOverride = null)
    {
        int n = AssertPairs(categories, values);
        if (colors != null && colors.Length != n)
            throw new ArgumentException("Bar: colors doit avoir la meme longueur que values (une couleur par barre).");
        var (yMin, yMax) = NiceBounds(values);
        // Echelle Y commune optionnelle : si un sommet est impose, il prime sur la borne calculee
        // (permet de comparer des barres entre charts). Chemin null = comportement precedent inchange.
        if (yMaxOverride.HasValue) yMax = yMaxOverride.Value;
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
            // Couleur par-barre (colors[i]) si fournie, sinon couleur unique / rouge auto pour negatifs.
            string c = colors != null ? colors[i] : (v >= 0 ? color : ColorNegative);
            sb.Append($"<rect x='{F(x)}' y='{F(y)}' width='{F(barW)}' height='{F(barH)}' fill='{c}'/>");
            sb.Append(CategoryLabel(layout, x + barW / 2.0, categories[i]));
        }
        if (legend != null && legend.Count > 0)
            sb.Append(LegendBox(layout, legend));
        sb.Append(CloseSvg());
        return sb.ToString();
    }

    private static string BuildGroupedBar(string title, string[] categories,
        double[][] seriesValues, string[] seriesLabels, int w, int h, string[] colors, bool logY)
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

        // Mode logY : on transforme les bornes et la fonction Y(v) en log10. Convention :
        // - si toutes les valeurs sont <= 0, retomber sur le mode lineaire (defensif).
        // - sinon, calculer yLoLog = log10(min_positif), borne inf clippee vers le haut via
        //   Math.Max(yLoRaw, yLoClipped) (cf L641-L3★ : anti-explosion des graduations).
        // - toutes les barres <=0 sont ramenees a la borne basse en log (pas affichees).
        bool useLog = logY && all.Any(v => v > 0);
        double yLoPlot = yMin, yHiPlot = yMax;
        Func<double, double> YF;
        if (useLog)
        {
            double minPos = all.Where(v => v > 0).Min();
            double yLoRaw = Math.Log10(minPos);
            double yLoClipped = Math.Log10(yMax) - 1.0;  // 1 decade en dessous du max (defaut raisonnable)
            yLoPlot = Math.Max(yLoRaw, yLoClipped);
            yHiPlot = Math.Log10(yMax);
            double range = yHiPlot - yLoPlot; if (range == 0) range = 1;
            YF = v => layout.PadT + layout.PlotH * (1 - (Math.Log10(Math.Max(v, minPos)) - yLoPlot) / range);
        }
        else
        {
            YF = v => layout.Y(v);
        }

        string[] palette = { ColorPrimary, ColorAccent, "#DD8452", ColorNegative, "#8172B3", "#937860" };
        string SeriesColor(int j) => colors != null && j < colors.Length ? colors[j] : palette[j % palette.Length];

        var sb = new StringBuilder();
        sb.Append(OpenSvg(w, h, title));
        if (useLog)
        {
            // Graduations Y en log : 3 decades (10^-1, 10^0, 10^1, ...) jusqu'a yHiPlot.
            // Chaque decade est affichee comme une ligne de grille + un label.
            int expLo = (int)Math.Floor(yLoPlot);
            int expHi = (int)Math.Ceiling(yHiPlot);
            // Re-render : on doit placer manuellement les graduations, GridAndYAxis etant lineaire.
            // Astuce : on appelle GridAndYAxis avec le layout lineaire d'origine pour la grille
            // horizontale, puis on annote par-dessus les labels de decades logarithmiques.
            sb.Append(GridAndYAxis(layout));
            // Labels de decades logarithmiques : pour chaque exposant dans [expLo..expHi], calculer
            // la position SVG via YF(10^exp) -- YF est lineaire en log, donc inverse lineaire.
            double yHiSvg = layout.Y(yMax);  // sommet du plot (lineaire)
            double yLoSvg = layout.Y(yMin);  // base du plot (lineaire)
            double yHiLogSvg = layout.PadT;
            double yLoLogSvg = layout.PadT + layout.PlotH;
            Func<double, double> YSvgForDecade = logVal =>
                yLoLogSvg + (yHiLogSvg - yLoLogSvg) * (1 - (logVal - yLoPlot) / (yHiPlot - yLoPlot));
            for (int exp = expLo; exp <= expHi; exp++)
            {
                double v = Math.Pow(10, exp);
                double py = YSvgForDecade(Math.Log10(v));
                string lbl = exp == 0 ? "1" : exp == 1 ? "10" : exp == -1 ? "0.1" : $"10^{exp}";
                sb.Append($"<text x='{layout.PadL - 8}' y='{F(py + 4)}' text-anchor='end' fill='{ColorText}'>{lbl}</text>");
                sb.Append($"<line x1='{layout.PadL - 4}' y1='{F(py)}' x2='{layout.PadL}' y2='{F(py)}' stroke='{ColorAxis}' stroke-width='1'/>");
            }
        }
        else
        {
            sb.Append(GridAndYAxis(layout));
        }

        // Groupe = 80% de la cellule categorie ; sous-barres cote a cote, centrees sur CatX(i).
        double groupW = (layout.PlotW / (double)catCount) * 0.80;
        double barW = groupW / seriesCount;
        for (int i = 0; i < catCount; i++)
        {
            double gx = layout.CatX(i) - groupW / 2.0;
            for (int j = 0; j < seriesCount; j++)
            {
                double v = seriesValues[j][i];
                // Hauteur en mode log : si v<=0, la barre va jusqu'a la borne basse clippee.
                // Si v>0, on calcule la hauteur entre YF(v) et la base du plot.
                double yTop, barH;
                if (useLog)
                {
                    double vEff = v > 0 ? v : Math.Pow(10, yLoPlot);
                    yTop = YF(vEff);
                    barH = (layout.PadT + layout.PlotH) - yTop;
                }
                else
                {
                    yTop = v >= 0 ? YF(v) : YF(0);
                    barH = Math.Abs(v - 0) / (yMax - yMin == 0 ? 1 : yMax - yMin) * layout.PlotH;
                }
                sb.Append($"<rect x='{F(gx + j * barW)}' y='{F(yTop)}' width='{F(barW)}' height='{F(barH)}' fill='{SeriesColor(j)}'/>");
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

    private static string BuildBoxPlot(string title, string[] categories,
        IReadOnlyList<double[]> samples, int w, int h, bool logY)
    {
        int n = categories?.Length ?? 0;
        if (n == 0 || samples == null || samples.Count != n)
            throw new ArgumentException("BoxPlot: categories et samples doivent avoir la meme longueur non nulle.");

        // Aplatir toutes les observations pour calculer les bornes Y sur l'union.
        int total = 0;
        for (int i = 0; i < n; i++) if (samples[i] != null) total += samples[i].Length;
        double[] all = new double[total];
        int p = 0;
        for (int i = 0; i < n; i++)
            if (samples[i] != null)
                for (int j = 0; j < samples[i].Length; j++)
                    all[p++] = samples[i][j];

        if (all.Length == 0)
            throw new ArgumentException("BoxPlot: aucune observation dans samples.");

        // Borne basse en log : minPositif. Si toutes <= 0, retomber sur lineaire.
        bool useLog = logY && all.Any(v => v > 0);
        double yMin, yMax;
        if (useLog)
        {
            double minPos = all.Where(v => v > 0).Min();
            double yLoRaw = Math.Log10(minPos);
            double yLoClipped = Math.Log10(all.Max()) - 1.0;
            yMin = Math.Max(yLoRaw, yLoClipped);
            yMax = Math.Log10(all.Max());
        }
        else
        {
            var nb = NiceBounds(all);
            yMin = nb.min; yMax = nb.max;
        }

        var layout = new PlotLayout(w, h, yMin, yMax, n);
        // Fonction Y adaptee au mode log.
        Func<double, double> YF;
        if (useLog)
        {
            double minPos = all.Where(v => v > 0).Min();
            double range = yMax - yMin; if (range == 0) range = 1;
            YF = v => layout.PadT + layout.PlotH * (1 - (Math.Log10(Math.Max(v, minPos)) - yMin) / range);
        }
        else
        {
            YF = v => layout.Y(v);
        }

        string[] palette = { ColorPrimary, ColorAccent, "#DD8452", ColorNegative, "#8172B3", "#937860" };

        var sb = new StringBuilder();
        sb.Append(OpenSvg(w, h, title));
        // Grille + axe Y. En mode log on conserve la grille lineaire (esthetique homogene avec
        // les autres primitives), et on annote par-dessus les decades comme dans BuildGroupedBar.
        sb.Append(GridAndYAxis(layout));
        if (useLog)
        {
            int expLo = (int)Math.Floor(yMin);
            int expHi = (int)Math.Ceiling(yMax);
            for (int exp = expLo; exp <= expHi; exp++)
            {
                double v = Math.Pow(10, exp);
                double py = YF(v);
                string lbl = exp == 0 ? "1" : exp == 1 ? "10" : exp == -1 ? "0.1" : $"10^{exp}";
                sb.Append($"<text x='{layout.PadL - 8}' y='{F(py + 4)}' text-anchor='end' fill='{ColorText}'>{lbl}</text>");
            }
        }

        // Pour chaque categorie : 5 statistiques + points individuels + labels.
        double catW = layout.PlotW / (double)n;
        var rnd = new Random(42);  // graine fixe pour jitter reproductible
        for (int i = 0; i < n; i++)
        {
            double[] data = samples[i];
            if (data == null || data.Length == 0) continue;
            // Filtrer <= 0 en log pour les stats (sinon min/max = 0 = indetermine).
            double[] valid = useLog ? data.Where(v => v > 0).ToArray() : data;
            if (valid.Length == 0) continue;
            Array.Sort(valid);
            double q1 = Quantile(valid, 0.25);
            double med = Quantile(valid, 0.50);
            double q3 = Quantile(valid, 0.75);
            double iqr = q3 - q1;
            double whiskerLo = Math.Max(valid.Min(), q1 - 1.5 * iqr);
            double whiskerHi = Math.Min(valid.Max(), q3 + 1.5 * iqr);

            double cx = layout.CatX(i);
            string c = palette[i % palette.Length];
            double halfBox = catW * 0.20;
            // Boite Q1..Q3
            double yQ1 = YF(q1), yQ3 = YF(q3);
            double yMid = YF(med);
            sb.Append($"<rect x='{F(cx - halfBox)}' y='{F(yQ3)}' width='{F(2 * halfBox)}' height='{F(Math.Max(0, yQ1 - yQ3))}' fill='{c}' fill-opacity='0.6' stroke='{c}' stroke-width='1.5'/>");
            // Mediane (ligne horizontale epaisse)
            sb.Append($"<line x1='{F(cx - halfBox)}' y1='{F(yMid)}' x2='{F(cx + halfBox)}' y2='{F(yMid)}' stroke='{ColorText}' stroke-width='2'/>");
            // Moustaches
            double yWhLo = YF(whiskerLo), yWhHi = YF(whiskerHi);
            sb.Append($"<line x1='{F(cx)}' y1='{F(yQ1)}' x2='{F(cx)}' y2='{F(yWhLo)}' stroke='{c}' stroke-width='1.5'/>");
            sb.Append($"<line x1='{F(cx)}' y1='{F(yQ3)}' x2='{F(cx)}' y2='{F(yWhHi)}' stroke='{c}' stroke-width='1.5'/>");
            // Capuches des moustaches (petites barres horizontales)
            sb.Append($"<line x1='{F(cx - halfBox * 0.5)}' y1='{F(yWhLo)}' x2='{F(cx + halfBox * 0.5)}' y2='{F(yWhLo)}' stroke='{c}' stroke-width='1.5'/>");
            sb.Append($"<line x1='{F(cx - halfBox * 0.5)}' y1='{F(yWhHi)}' x2='{F(cx + halfBox * 0.5)}' y2='{F(yWhHi)}' stroke='{c}' stroke-width='1.5'/>");

            // Points individuels (jitter horizontal +/- 30% de halfBox).
            foreach (var v in valid)
            {
                double jx = cx + (rnd.NextDouble() - 0.5) * 0.6 * halfBox;
                double py = YF(v);
                sb.Append($"<circle cx='{F(jx)}' cy='{F(py)}' r='2.5' fill='{c}' fill-opacity='0.5'/>");
            }
            // Label de categorie
            sb.Append(CategoryLabel(layout, cx, categories[i]));
        }

        sb.Append(CloseSvg());
        return sb.ToString();
    }

    // Quantile par interpolation lineaire (Type 7, convention R/numpy).
    private static double Quantile(double[] sorted, double q)
    {
        if (sorted.Length == 0) return double.NaN;
        if (sorted.Length == 1) return sorted[0];
        double pos = q * (sorted.Length - 1);
        int lo = (int)Math.Floor(pos);
        int hi = (int)Math.Ceiling(pos);
        if (lo == hi) return sorted[lo];
        double frac = pos - lo;
        return sorted[lo] + (sorted[hi] - sorted[lo]) * frac;
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
        IReadOnlyList<SvgSeries> series, int w, int h, bool logY = false)
    {
        if (series == null || series.Count == 0)
            throw new ArgumentException("Overlay: au moins une serie requise.");
        foreach (var s in series)
            if (s.Xs == null || s.Ys == null || s.Xs.Length != s.Ys.Length || s.Xs.Length == 0)
                throw new ArgumentException($"Overlay: serie '{s.Label}' doit avoir xs/ys de meme longueur non nulle.");

        // Bornes X (union de toutes les series) et Y (union ys +- sigma), en espace original.
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

        // Bornes Y : lineaires (defaut) ou log10 (opt-in logY). L'echelle log est necessaire pour
        // les rapports grands (ex. 0.55 -> 34.38, ~63x, ou le lineaire ecrase le regime convergent
        // contre le point aberrant). Exige des Y strictement positifs (couvre aussi y+-sigma, pour
        // que les barres d'erreur restent definies en log). Le layout est alors en espace log10 ;
        // PYy mappe une valeur originale -> y SVG via log10(v), et les graduations sont placees aux
        // valeurs "propres" 1-2-5 x 10^k (labellees en valeur originale, pas en log10).
        double bMin, bMax;
        if (logY)
        {
            // Echelle log : les POINTS (ys) doivent etre strictement positifs. Les barres d'erreur
            // +-sigma peuvent croiser zero (ex. limite=50 : moyenne 0.90, std 1.00 -> borne inf -0.10) ;
            // leur segment inferieur est clippe au sol de l'axe plutot que de rejeter la donnee (comportement
            // matplotlib / Plotly en axe log avec barres d'erreur asymetriques). Bornes en espace log10
            // calculees sur les candidats positifs (points + bornes d'erreur restant positives).
            foreach (var s in series)
                for (int i = 0; i < s.Ys.Length; i++)
                    if (s.Ys[i] <= 0)
                        throw new ArgumentException("Overlay logY: les valeurs Y (points) doivent etre strictement positives.");
            double posLo = double.PositiveInfinity, posHi = double.NegativeInfinity;
            foreach (var s in series)
                for (int i = 0; i < s.Ys.Length; i++)
                {
                    double sig = (s.Sigma != null && i < s.Sigma.Length) ? Math.Abs(s.Sigma[i]) : 0.0;
                    posLo = Math.Min(posLo, s.Ys[i]);
                    posHi = Math.Max(posHi, s.Ys[i] + sig);
                    if (s.Ys[i] - sig > 0) posLo = Math.Min(posLo, s.Ys[i] - sig);
                }
            double lgLo = Math.Log10(posLo), lgHi = Math.Log10(posHi);
            double lgPad = (lgHi - lgLo) * 0.06; if (lgPad == 0) lgPad = 0.2;
            bMin = lgLo - lgPad; bMax = lgHi + lgPad;
        }
        else
        {
            double ypad = (yHi - yLo) * 0.06; if (ypad == 0) ypad = Math.Max(1, Math.Abs(yHi) * 0.1);
            bMin = yLo - ypad; bMax = yHi + ypad;
        }
        var layout = new PlotLayout(w, h, bMin, bMax, series.Count);
        // PYy : valeur originale -> y SVG (lineaire, ou via log10(v) en echelle log). En log, une valeur
        // non positive (segment inferieur d'une barre d'erreur croisant zero) est clippee au sol de l'axe ;
        // les points etant valides > 0, ils ne declenchent jamais ce clip.
        Func<double, double> PYy;
        if (logY) PYy = v => v > 0 ? layout.Y(Math.Log10(v)) : (layout.PadT + layout.PlotH);
        else PYy = v => layout.Y(v);
        Func<double, double> PX = x => layout.PadL + (x - xMin) / xRange * layout.PlotW;

        var sb = new StringBuilder();
        sb.Append(OpenSvg(w, h, title));
        sb.Append(logY ? GridAndYAxisLog(layout, LogTicks(Math.Pow(10, bMin), Math.Pow(10, bMax)))
                       : GridAndYAxis(layout));

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
                pts.Add($"{F(PX(s.Xs[i]))},{F(PYy(s.Ys[i]))}");
            bool line = s.Style == TraceStyle.Line || s.Style == TraceStyle.LineMarkers;
            bool marks = s.Style == TraceStyle.Markers || s.Style == TraceStyle.LineMarkers;

            if (line)
                sb.Append($"<polyline points='{string.Join(" ", pts)}' fill='none' stroke='{color}' stroke-width='2'/>");

            // Barres d'erreur +-sigma (tracees avant les marqueurs pour rester dessous).
            if (s.Sigma != null)
                for (int i = 0; i < s.Xs.Length && i < s.Sigma.Length; i++)
                {
                    double xp = PX(s.Xs[i]);
                    double yTop = PYy(s.Ys[i] + Math.Abs(s.Sigma[i]));
                    double yBot = PYy(s.Ys[i] - Math.Abs(s.Sigma[i]));
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

    // Grille + axe Y en echelle log : une ligne horizontale par graduation "propre" (1-2-5 x 10^k)
    // dans la plage [vLo, vHi], labellee en valeur originale (pas en log10). Le layout est en espace
    // log10 (YMin/YMax = log10 des bornes). Pas d'axe horizontal a y=0 (indefini en log) : la ligne
    // de base reste en bas de la zone. Utilisee par Overlay(logY: true).
    private static string GridAndYAxisLog(PlotLayout l, IReadOnlyList<double> ticks)
    {
        var sb = new StringBuilder();
        foreach (double t in ticks)
        {
            double py = l.Y(Math.Log10(t));
            sb.Append($"<line x1='{l.PadL}' y1='{F(py)}' x2='{l.W - l.PadR}' y2='{F(py)}' stroke='{ColorGrid}' stroke-width='1'/>");
            sb.Append($"<text x='{l.PadL - 8}' y='{F(py + 4)}' text-anchor='end' fill='{ColorText}'>{F(t)}</text>");
        }
        sb.Append($"<line x1='{l.PadL}' y1='{l.PadT}' x2='{l.PadL}' y2='{l.H - l.PadB}' stroke='{ColorAxis}' stroke-width='1'/>");
        sb.Append($"<line x1='{l.PadL}' y1='{l.H - l.PadB}' x2='{l.W - l.PadR}' y2='{l.H - l.PadB}' stroke='{ColorAxis}' stroke-width='1'/>");
        return sb.ToString();
    }

    // Graduations "propres" d'une echelle log (base 10) sur [vLo, vHi] : les multiples 1, 2, 5 de
    // chaque decade (ex. 0.1, 0.2, 0.5, 1, 2, 5, 10, 20, 50). Convention par defaut de matplotlib
    // en echelle log ; garde les ticks dans la plage visible.
    private static List<double> LogTicks(double vLo, double vHi)
    {
        var ticks = new List<double>();
        if (vLo <= 0) vLo = 1e-9;
        int kLo = (int)Math.Floor(Math.Log10(vLo));
        int kHi = (int)Math.Ceiling(Math.Log10(vHi));
        for (int k = kLo; k <= kHi; k++)
            foreach (double m in new[] { 1.0, 2.0, 5.0 })
            {
                double t = m * Math.Pow(10, k);
                if (t >= vLo && t <= vHi) ticks.Add(t);
            }
        if (ticks.Count == 0) { ticks.Add(vLo); ticks.Add(vHi); }
        return ticks;
    }

    private static string CategoryLabel(PlotLayout l, double x, string label)
        => $"<text x='{F(x)}' y='{l.H - l.PadB + 16}' text-anchor='middle' fill='{ColorText}'>{Esc(label)}</text>";

    // Encart de legende SVG inline (coin haut-droit de la zone de plot) : une pastille coloree +
    // label par entree. Utilise par Bar() pour expliciter une semantique de couleur par-barre
    // (ex. bleu=rentable / orange=non rentable) sans recourir a une legende console ASCII degradee.
    private static string LegendBox(PlotLayout l, IReadOnlyList<(string Color, string Label)> entries)
    {
        var sb = new StringBuilder();
        int maxLabel = entries.Max(e => (e.Label ?? "").Length);
        double boxW = 30 + maxLabel * 6.6;
        double boxH = 8 + entries.Count * 17;
        double lx = l.PadL + l.PlotW - boxW - 4, ly = l.PadT + 6;
        sb.Append($"<rect x='{F(lx)}' y='{F(ly)}' width='{F(boxW)}' height='{F(boxH)}' fill='white' fill-opacity='0.85' stroke='{ColorGrid}' stroke-width='1'/>");
        for (int i = 0; i < entries.Count; i++)
        {
            double ey = ly + 13 + i * 17;
            sb.Append($"<rect x='{F(lx + 7)}' y='{F(ey - 9)}' width='12' height='12' fill='{entries[i].Color}'/>");
            sb.Append($"<text x='{F(lx + 24)}' y='{F(ey)}' fill='{ColorText}'>{Esc(entries[i].Label)}</text>");
        }
        return sb.ToString();
    }

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
