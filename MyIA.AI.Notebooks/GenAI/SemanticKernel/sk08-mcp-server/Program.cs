using System.ComponentModel;
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
    [McpServerTool(Name = "prix_ttc"), Description("Calcule le prix TTC après remise et TVA de 20%.")]
    public static object PrixTtc([Description("Prix HT strictement positif")] double @base, [Description("Remise de 0 à 100 pour cent")] int remise_pct = 0)
    {
        if (@base <= 0 || remise_pct < 0 || remise_pct > 100) throw new ArgumentException("base doit être positive et remise_pct entre 0 et 100");
        double ht = Math.Round(@base * (1 - remise_pct / 100.0), 2);
        return new { ht, ttc = Math.Round(ht * 1.2, 2) };
    }
    [McpServerTool(Name = "calcule_tva"), Description("Détaille la TVA à 20%.")]
    public static object CalculeTva(double montant_ht)
    {
        if (montant_ht <= 0) throw new ArgumentException("montant_ht doit être positif");
        return new { ht = montant_ht, tva = Math.Round(montant_ht * .2, 2), ttc = Math.Round(montant_ht * 1.2, 2) };
    }
    [McpServerTool(Name = "tva_inverse"), Description("Retrouve le HT depuis le TTC et le taux.")]
    public static object TvaInverse(double montant_ttc, double taux_tva)
    {
        if (montant_ttc <= 0 || taux_tva <= 0 || taux_tva >= 1) throw new ArgumentException("montant_ttc positif et taux_tva entre 0 et 1 requis");
        return new { ttc = montant_ttc, taux_tva, ht = Math.Round(montant_ttc / (1 + taux_tva), 4) };
    }
    [McpServerTool(Name = "verifie_chemin"), Description("Teste si un chemin se situe dans une zone autorisée (sans résoudre les liens symboliques).")]
    public static object VerifieChemin(string chemin, string zone_autorisee)
    {
        if (string.IsNullOrWhiteSpace(chemin) || string.IsNullOrWhiteSpace(zone_autorisee)) return new { chemin, zone_autorisee, dans_zone = false };
        var relative = Path.GetRelativePath(Path.GetFullPath(zone_autorisee), Path.GetFullPath(chemin));
        bool inside = !Path.IsPathRooted(relative) && relative != ".." && !relative.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal);
        return new { chemin, zone_autorisee, dans_zone = inside };
    }
    [McpServerTool(Name = "analyse_chaine"), Description("Compte caractères et mots et donne le premier mot.")]
    public static object AnalyseChaine(string texte)
    {
        var mots = texte.Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries);
        return new { nb_caracteres = texte.Length, nb_mots = mots.Length, premier_mot = mots.FirstOrDefault() ?? "" };
    }
}
public class PrixPlugin
{
    [KernelFunction("prix_ttc"), Description("Calcule le prix TTC après remise à TVA 20%.")]
    public double PrixTtc(double @base, int remise_pct = 0) => Math.Round(@base * (1 - remise_pct / 100.0) * 1.2, 2);
}
