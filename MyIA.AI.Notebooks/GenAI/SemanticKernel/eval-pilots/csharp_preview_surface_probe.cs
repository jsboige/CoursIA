#:package Microsoft.SemanticKernel.Agents.Core@1.81.0
#:package Microsoft.SemanticKernel.Agents.Orchestration@1.81.0-preview
#:package Microsoft.SemanticKernel.Agents.Magentic@1.81.0-preview

// Sonde T9 (issue #14499, tranche Q17) : la SURFACE PREVIEW de la couche agents
// C# de Semantic Kernel.
//
// Pourquoi une sonde separee de `csharp_coverage_probe.cs` : la sonde T6 mesure
// la surface STABLE, et ses comptes (union 210 pour SK) alimentent le §2.7 du
// document d'evaluation. Or la restitution de paquets ici ENCHANGE les
// assemblages deployes : un `Microsoft.SemanticKernel.Agents.Orchestration.dll`
// supplementaire gonflerait l'union et invaliderait la comparaison avec T6. Les
// deux surfaces se mesurent donc dans deux processus distincts.
//
// Ce que la sonde etablit (fait mesure le 2026-11-04, contre un echantillon
// taken au crayon le 2026-11-04 qui disait « SK C# n'a aucune orchestration ») :
// la couche d'orchestration C# de SK EXISTE et est PUBLIEE sur NuGet, mais
// UNIQUEMENT en version `-preview` -- `Microsoft.SemanticKernel.Agents.
// Orchestration` et `Microsoft.SemanticKernel.Agents.Magentic` n'ont jamais
// eu de version stable. La surface stable `Microsoft.SemanticKernel.Agents.Core`
// 1.81.0 ne les embarque pas. L'absence mesuree par T6 n'est donc pas une
// absence de la capacite : c'est une absence de version STABLE.
//
// Methode : meme principe que T6 -- on enumere les TYPES PUBLICS des
// assemblages reellement deployes, en gardant le detail PAR ASSEMBLAGE, pour
// que la provenance soit lisible (quel assemblage porte quel type).
//
// Controles : POSITIF (les cinq topologies doivent etre presentes dans la
// surface preview) et NEGATIF (les assemblages stable-only ne doivent pas
// embarquer ces types : le controle etablit QUE le type vient bien de la
// couche preview).
//
// Forme « app mono-fichier » (.NET 10) : `dotnet run csharp_preview_surface_probe.cs`.
// Aucun .csproj n'est livre. Necessite le reseau pour la restauration.
//
// Sortie : exit 0 si les deux controles passent, 1 sinon.

using System.Reflection;

// IL2026 : l'analyseur de trimming signale `Assembly.LoadFrom` et
// `GetExportedTypes` commeRequiresUnreferencedCode. L'avertissement est sans
// objet ici -- la sonde n'est ni trimmee ni publiee, elle charge les
// assemblages DEPLOYES pour les enumerer. Le neutraliser evite que le build
// n'imprime un avertissement porteur du CHEMIN LOCAL du fichier source, qui
// se retrouverait dans la trace commitee.
#pragma warning disable IL2026

// En-tete produit par la SONDE elle-meme : la trace commitee doit etre le
// stdout BRUT, jamais un fichier retouche apres coup (cf `README.md`).
// La date est calculee au runtime ; aucun chemin local n'y figure.
Console.WriteLine("# Sonde T9 -- surface PREVIEW de la couche agents C# de Semantic Kernel");
Console.WriteLine($"# generee le {DateTime.UtcNow:yyyy-MM-dd} par csharp_preview_surface_probe.cs");
Console.WriteLine("# packages : Agents.Core 1.81.0 (stable) + Agents.Orchestration 1.81.0-preview + Agents.Magentic 1.81.0-preview");
Console.WriteLine("# aucune requete LLM, aucune cle API ; mesure de SURFACE, pas de comportement");
Console.WriteLine();

var baseDir = AppContext.BaseDirectory;

// Par assemblage ET par type : pour attribuer chaque type a son assemblage
// d'origine (c'est ce qui permet le controle negatif de provenance).
var assemblies = new List<(string File, Assembly Asm, string[] Names)>();
foreach (var file in Directory.GetFiles(baseDir, "*.dll")
             .Where(f => Path.GetFileName(f).StartsWith("Microsoft.SemanticKernel.Agents", StringComparison.OrdinalIgnoreCase))
             .OrderBy(f => f, StringComparer.Ordinal))
{
    Assembly asm;
    try { asm = Assembly.LoadFrom(file); } catch { continue; }
    Type[] types;
    try { types = asm.GetExportedTypes(); }
    catch (ReflectionTypeLoadException ex) { types = ex.Types.Where(t => t != null).ToArray()!; }
    assemblies.Add((Path.GetFileName(file)!, asm, types.Where(t => t.IsPublic).Select(t => t.Name).ToArray()));
}

Console.WriteLine("ASSEMBLAGES DEPLOYES (prefixe Microsoft.SemanticKernel.Agents) :");
foreach (var (file, _, names) in assemblies)
    Console.WriteLine($"   {file,-62} {names.Length,5} type(s) public(s)");
Console.WriteLine();

var union = new HashSet<string>(assemblies.SelectMany(a => a.Names), StringComparer.Ordinal);
Console.WriteLine($"union dedoublonnee (nom court) : {union.Count}  <- PLANCHER, pas un compte de types");
Console.WriteLine();

// Les cinq topologies de la couche agents SK Python, mesurees presentes en
// 1.46.0 (voir `current_api_probe.py`). En C#, la surface preview doit les
// porter ; la surface stable, non.
string[] fiveTopologies =
[
    "ConcurrentOrchestration", "SequentialOrchestration", "GroupChatOrchestration",
    "HandoffOrchestration", "MagenticOrchestration",
];

Console.WriteLine("CONTROLE POSITIF -- les cinq topologies doivent etre PRESENTES dans la surface PREVIEW");
var missing = new List<string>();
foreach (var n in fiveTopologies)
{
    var owner = assemblies.FirstOrDefault(a => a.Names.Contains(n));
    if (owner.File is null) { missing.Add(n); Console.WriteLine($"   ABSENT !!  {n}"); }
    else Console.WriteLine($"   present OK  {n,-30} <- {owner.File}");
}
Console.WriteLine();

// CONTROLE NEGATIF DE PROVENANCE : ces types ne doivent pas venir de
// l'assemblage STABLE. Sans ce controle, un « present » ne dit pas d'ou il
// vient -- et la distinction est justement le point mesure.
var stableAsm = assemblies.FirstOrDefault(a =>
    a.File.Equals("Microsoft.SemanticKernel.Agents.Core.dll", StringComparison.OrdinalIgnoreCase));

Console.WriteLine("CONTROLE NEGATIF DE PROVENANCE -- la surface STABLE ne doit PAS porter ces types");
if (stableAsm.File is null)
{
    Console.WriteLine("   assemblage Agents.Core absent du deploiement  (!!)");
}
else
{
    foreach (var n in fiveTopologies)
        Console.WriteLine($"   {(stableAsm.Names.Contains(n) ? "PRESENT !! (la surface stable les expose)" : "absent  OK")}  {n}");
}
Console.WriteLine();

// Ce que la surface preview apporte en plus, par fragment de nom.
Console.WriteLine("SURFACE PREVIEW -- fragments de nom (reprise / telemetry / workflow)");
foreach (var frag in new[] { "Checkpoint", "OpenTelemetry", "Telemetry", "Workflow", "Resume", "Persistence" })
{
    var hits = union.Where(n => n.Contains(frag, StringComparison.OrdinalIgnoreCase))
                    .OrderBy(n => n, StringComparer.Ordinal).ToList();
    Console.WriteLine($"   fragment \"{frag}\" -> {(hits.Count == 0 ? "AUCUN" : string.Join(", ", hits))}");
}

var negativeOk = stableAsm.File is not null
              && fiveTopologies.All(n => !stableAsm.Names.Contains(n));
var positiveOk = missing.Count == 0;

Console.WriteLine();
Console.WriteLine($"VERDICT controles : negatif={(negativeOk ? "OK" : "ECHEC")} positif={(positiveOk ? "OK" : "ECHEC")}");
return negativeOk && positiveOk ? 0 : 1;
