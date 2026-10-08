#:package Microsoft.SemanticKernel.Agents.Core@1.81.0
#:package Microsoft.Agents.AI@1.24.0
#:package Microsoft.Agents.AI.Workflows@1.24.0

// Sonde T6 (issue #14499, point 4) : ce que chaque moteur offre REELLEMENT en C#.
//
// Methode : on n'interroge pas la documentation, on enumere les TYPES PUBLICS des
// assemblages reellement deployes par le restaurateur de paquets. Un type absent
// de cette enumeration n'est pas utilisable, quelle que soit la doc.
//
// Deux precisions de methode, toutes deux payees par une erreur reelle :
//
// 1. `Assembly.Load("<nom>")` NE SUFFIT PAS. Rien ne reference ces assemblages,
//    donc rien ne les charge, et la sonde rend « aucune assembly » sur un projet
//    pourtant correctement restaure. Il faut charger par CHEMIN depuis le
//    repertoire de sortie -- ce qui mesure d'ailleurs ce qui est deploye.
// 2. Un detecteur se valide par ses FAUX NEGATIFS, pas par ses hits. La sonde
//    porte donc un CONTROLE POSITIF (ce qui doit etre present) ET un CONTROLE
//    NEGATIF (ce qui doit etre absent). Sans le second, « 0 hit » serait
//    indiscernable de « sonde cassee » -- et c'est exactement le mode de defaut
//    qui a fait passer un lake portant 80 % de la dette formelle du depot pour
//    un « residu » pendant onze jours (regle anti-regression du depot).
//
// Forme « app mono-fichier » (.NET 10) : `dotnet run csharp_coverage_probe.cs`.
// Aucun .csproj n'est livre, donc aucun impact sur les solutions du depot
// (`MyIA.CoursIA.sln`, `MyIA.AI.Shared.sln`) ni sur les workflows .NET, qui sont
// tous filtres par chemin. Reproduction : necessite le reseau pour la
// restauration des paquets.
//
// Sortie : exit 0 si les deux controles passent, 1 sinon.

using System.Reflection;

var baseDir = AppContext.BaseDirectory;

// Enumere les noms de types PUBLICS exportes par tous les assemblages deployes
// dont le nom commence par `prefix`.
HashSet<string> ExportedNames(string prefix)
{
    var names = new HashSet<string>(StringComparer.Ordinal);
    foreach (var file in Directory.GetFiles(baseDir, "*.dll")
                 .Where(f => Path.GetFileName(f).StartsWith(prefix, StringComparison.OrdinalIgnoreCase)))
    {
        Assembly asm;
        try { asm = Assembly.LoadFrom(file); } catch { continue; }

        Type[] types;
        try { types = asm.GetExportedTypes(); }
        catch (ReflectionTypeLoadException ex) { types = ex.Types.Where(t => t != null).ToArray()!; }

        foreach (var t in types.Where(t => t.IsPublic)) names.Add(t.Name);
    }
    return names;
}

var sk = ExportedNames("Microsoft.SemanticKernel");
var maf = ExportedNames("Microsoft.Agents.AI");

Console.WriteLine($"SK (C#)  : {sk.Count} types publics exportes");
Console.WriteLine($"MAF (C#) : {maf.Count} types publics exportes");
Console.WriteLine();

// CONTROLE NEGATIF -- les cinq objets d'orchestration de la couche agents de
// Semantic Kernel Python 1.41.3 (mesures en T2 et T4 de ce chantier) ne doivent
// PAS exister cote C# 1.81.0. Si l'un ressort, l'hypothese de parite est fausse.
string[] skPythonOnly =
[
    "SequentialOrchestration", "ConcurrentOrchestration", "GroupChatOrchestration",
    "MagenticOrchestration", "HandoffOrchestration",
];
Console.WriteLine("CONTROLE NEGATIF -- orchestration de la couche agents SK Python doit etre ABSENTE du C#");
foreach (var n in skPythonOnly)
    Console.WriteLine($"   {(sk.Contains(n) ? "PRESENT !! (hypothese fausse)" : "absent  OK")}  {n}");

// CONTROLE POSITIF -- les cinq topologies doivent etre PRESENTES cote MAF C#.
string[] mafBuilders =
[
    "SequentialWorkflowBuilder", "ConcurrentWorkflowBuilder", "GroupChatWorkflowBuilder",
    "MagenticWorkflowBuilder", "HandoffWorkflowBuilder", "WorkflowBuilder",
];
Console.WriteLine();
Console.WriteLine("CONTROLE POSITIF -- les cinq topologies doivent etre PRESENTES dans MAF C#");
foreach (var n in mafBuilders)
    Console.WriteLine($"   {(maf.Contains(n) ? "present OK" : "ABSENT !!")}  {n}");

// Capacites que l'issue demande explicitement (point 3) et qui ne sont pas des
// topologies : reprise d'un long run (checkpoint) et observabilite (OTel).
string[] capabilities =
[
    "CheckpointManager", "CheckpointInfo", "FileSystemJsonCheckpointStore",
    "WorkflowSessionCheckpointRecovery", "OpenTelemetryWorkflowBuilderExtensions",
    "MagenticProgressLedger", "RoundRobinGroupChatManager",
];
Console.WriteLine();
Console.WriteLine("CAPACITES (checkpoint, OTel, ledger Magentic) -- attendues PRESENTES dans MAF C#");
foreach (var n in capabilities)
    Console.WriteLine($"   {(maf.Contains(n) ? "present OK" : "ABSENT !!")}  {n}");

// Ce que SK C# expose REELLEMENT pour le multi-agents : le modele historique.
string[] skLegacy = ["AgentGroupChat", "AgentGroupChatSettings", "SequentialSelectionStrategy", "ChatCompletionAgent"];
Console.WriteLine();
Console.WriteLine("CE QUE SK C# EXPOSE (modele historique AgentGroupChat) -- attendu PRESENT");
foreach (var n in skLegacy)
    Console.WriteLine($"   {(sk.Contains(n) ? "present OK" : "ABSENT !!")}  {n}");

// Google ADK : aucun paquet officiel n'existe sur NuGet. La mesure est le
// balayage du repertoire de sortie -- la seule assembly « Google » attendue est
// `Google.Protobuf.dll`, dependance transitive, pas un moteur agentique.
Console.WriteLine();
Console.WriteLine("GOOGLE ADK (C#) -- balayage des assemblages deployes");
var google = Directory.GetFiles(baseDir, "*.dll")
    .Select(Path.GetFileName)
    .Where(f => f!.Contains("Google", StringComparison.OrdinalIgnoreCase)
             || f!.Contains("Adk", StringComparison.OrdinalIgnoreCase))
    .OrderBy(f => f, StringComparer.Ordinal)
    .ToList();
Console.WriteLine(google.Count == 0
    ? "   aucune assembly Google/ADK deployee"
    : "   " + string.Join(", ", google));

var negativeOk = skPythonOnly.All(n => !sk.Contains(n));
var positiveOk = mafBuilders.All(maf.Contains)
              && capabilities.All(maf.Contains)
              && skLegacy.All(sk.Contains);

Console.WriteLine();
Console.WriteLine($"VERDICT controles : negatif={(negativeOk ? "OK" : "ECHEC")} positif={(positiveOk ? "OK" : "ECHEC")}");
return negativeOk && positiveOk ? 0 : 1;
