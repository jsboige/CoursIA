using System.ComponentModel;
using System.Text;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using Microsoft.SemanticKernel;
using ModelContextProtocol.Server;

var builder = Host.CreateApplicationBuilder(args);
builder.Logging.ClearProviders(); // stdout est réservé au protocole
var server = builder.Services.AddMcpServer().WithStdioServerTransport();
if (args.Contains("--sk"))
{
    var kernel = Kernel.CreateBuilder().Build();
    var plugin = kernel.ImportPluginFromObject(new PrixPlugin(), "prix");
    server.WithTools(plugin.AsAIFunctions(kernel).Select(f => McpServerTool.Create(f)));
}
else server.WithTools<DemoTools>();
await builder.Build().RunAsync();

[McpServerToolType]
public class DemoTools
{
    [McpServerTool(Name = "prix_ttc", UseStructuredContent = true), Description("Calcule le prix TTC après remise et TVA de 20%.")]
    public static PrixResult PrixTtc([Description("Prix HT strictement positif")] double @base, [Description("Remise de 0 à 100 pour cent")] int remise_pct = 0)
    {
        if (@base <= 0 || remise_pct < 0 || remise_pct > 100) throw new ArgumentException("base doit être positive et remise_pct entre 0 et 100");
        double htBrut = @base * (1 - remise_pct / 100.0);
        return new(Math.Round(htBrut, 2), Math.Round(htBrut * 1.2, 2));
    }
    [McpServerTool(Name = "calcule_tva", UseStructuredContent = true), Description("Détaille la TVA à 20%.")]
    public static TvaResult CalculeTva(double montant_ht)
    {
        if (montant_ht <= 0) throw new ArgumentException("montant_ht doit être positif");
        return new(montant_ht, Math.Round(montant_ht * .2, 2), Math.Round(montant_ht + montant_ht * .2, 2));
    }
    [McpServerTool(Name = "tva_inverse", UseStructuredContent = true), Description("Retrouve le HT depuis le TTC et le taux.")]
    public static InverseResult TvaInverse(double montant_ttc, double taux_tva)
    {
        if (montant_ttc <= 0 || taux_tva <= 0 || taux_tva >= 1) throw new ArgumentException("montant_ttc positif et taux_tva entre 0 et 1 requis");
        return new(montant_ttc, taux_tva, Math.Round(montant_ttc / (1 + taux_tva), 4));
    }
    [McpServerTool(Name = "verifie_chemin", UseStructuredContent = true), Description("Teste si un chemin se situe dans une zone autorisée (sans résoudre les liens symboliques).")]
    public static CheminResult VerifieChemin(string chemin, string zone_autorisee)
    {
        if (string.IsNullOrWhiteSpace(chemin) || string.IsNullOrWhiteSpace(zone_autorisee)) return new(chemin, zone_autorisee, false);
        try
        {
            var relative = Path.GetRelativePath(Path.GetFullPath(zone_autorisee), Path.GetFullPath(chemin));
            bool inside = !Path.IsPathRooted(relative) && relative != ".." && !relative.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal);
            return new(chemin, zone_autorisee, inside);
        }
        catch (Exception ex) when (ex is ArgumentException or IOException or NotSupportedException)
        {
            return new(chemin, zone_autorisee, false);
        }
    }
    [McpServerTool(Name = "analyse_chaine", UseStructuredContent = true), Description("Compte caractères et mots et donne le premier mot.")]
    public static AnalyseResult AnalyseChaine(string texte)
    {
        var mots = texte.Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries);
        return new(texte.EnumerateRunes().Count(), mots.Length, mots.FirstOrDefault() ?? "");
    }
}
public class PrixPlugin
{
    [KernelFunction("prix_ttc"), Description("Calcule le prix après remise, sans TVA (nom historique).") ]
    public double PrixTtc(double @base, int remise_pct = 0) => @base * (1 - remise_pct / 100.0);
}

public record PrixResult(double ht, double ttc);
public record TvaResult(double ht, double tva, double ttc);
public record InverseResult(double ttc, double taux_tva, double ht);
public record CheminResult(string chemin, string zone_autorisee, bool dans_zone);
public record AnalyseResult(int nb_caracteres, int nb_mots, string premier_mot);
