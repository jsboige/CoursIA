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
// tous filtres par chemin. Les versions des trois paquets sont epinglees par les
// directives `#:package ...@<version>` ci-dessus, qui sont la forme de pin de
// l'app mono-fichier : c'est ce qui rend la sonde rejouable depuis le depot seul
// (cf `eval-pilots/README.md`, qui porte la commande). Reproduction : necessite
// le reseau pour la restauration des paquets.
//
// Sortie : exit 0 si les deux controles passent, 1 sinon.

using System.Reflection;

var baseDir = AppContext.BaseDirectory;

// Enumere les noms de types PUBLICS exportes par tous les assemblages deployes
// dont le nom commence par `prefix`, en gardant le detail PAR ASSEMBLAGE.
//
// Le detail n'est pas cosmetique. Additionner tous les assemblages d'un prefixe
// produit un total qui (a) depend de ce que le projet hote a restaure dans son
// repertoire de sortie -- un connecteur de plus gonfle le total -- et (b)
// dedoublonne sur le NOM COURT, tous namespaces confondus : deux types distincts
// homonymes fusionnent, donc l'union est un PLANCHER, pas un compte de types.
// Publier les deux -- par assemblage ET l'union -- rend la provenance du chiffre
// lisible, au lieu d'attacher un total large a une etiquette etroite.
(Dictionary<string, int> PerAssembly, HashSet<string> Union) ExportedNames(string prefix)
{
    var perAssembly = new Dictionary<string, int>(StringComparer.Ordinal);
    var names = new HashSet<string>(StringComparer.Ordinal);
    foreach (var file in Directory.GetFiles(baseDir, "*.dll")
                 .Where(f => Path.GetFileName(f).StartsWith(prefix, StringComparison.OrdinalIgnoreCase))
                 .OrderBy(f => f, StringComparer.Ordinal))
    {
        Assembly asm;
        try { asm = Assembly.LoadFrom(file); } catch { continue; }

        Type[] types;
        try { types = asm.GetExportedTypes(); }
        catch (ReflectionTypeLoadException ex) { types = ex.Types.Where(t => t != null).ToArray()!; }

        var pub = types.Where(t => t.IsPublic).ToList();
        perAssembly[Path.GetFileName(file)!] = pub.Count;
        foreach (var t in pub) names.Add(t.Name);
    }
    return (perAssembly, names);
}

void Dump(string label, Dictionary<string, int> perAsm, HashSet<string> union)
{
    Console.WriteLine($"{label} -- {perAsm.Count} assemblage(s) balaye(s) :");
    foreach (var kv in perAsm)
        Console.WriteLine($"   {kv.Key,-58} {kv.Value,5}");
    Console.WriteLine($"   {"union dedoublonnee (nom court)",-58} {union.Count,5}   <- PLANCHER, pas un compte de types");
    Console.WriteLine();
}

var (skPerAsm, sk) = ExportedNames("Microsoft.SemanticKernel");
var (mafPerAsm, maf) = ExportedNames("Microsoft.Agents.AI");

Dump("SK (C#)", skPerAsm, sk);
Dump("MAF (C#)", mafPerAsm, maf);

// CONTROLE NEGATIF -- trois mesures independantes, parce qu'un controle par nom
// exact ne teste qu'une CONVENTION DE NOMMAGE (celle de la couche agents Python),
// pas la surface d'API C#. Les deux premieres sont des controles de FORME et
// d'ASSEMBLAGE ; la troisieme (noms exacts) reste, en second rideau.
var skOrchestrationShaped = sk
    .Where(n => n.EndsWith("Orchestration", StringComparison.Ordinal))
    .OrderBy(n => n, StringComparer.Ordinal).ToList();
var skOrchestrationAsm = skPerAsm.Keys
    .Where(f => f.Contains("Agents.Orchestration", StringComparison.OrdinalIgnoreCase))
    .OrderBy(f => f, StringComparer.Ordinal).ToList();

Console.WriteLine("CONTROLE NEGATIF -- l'orchestration de la couche agents SK Python doit etre ABSENTE du C#");
Console.WriteLine($"   (a) par FORME -- types SK C# en `*Orchestration` : "
    + (skOrchestrationShaped.Count == 0 ? "aucun  OK" : string.Join(", ", skOrchestrationShaped) + "  !!"));
Console.WriteLine($"   (b) par ASSEMBLAGE -- `Microsoft.SemanticKernel.Agents.Orchestration` deploye : "
    + (skOrchestrationAsm.Count == 0 ? "non  OK" : string.Join(", ", skOrchestrationAsm) + "  !!"));

// Les cinq objets d'orchestration de la couche agents de Semantic Kernel Python
// 1.41.3 (mesures en T2 et T4 de ce chantier) ne doivent PAS exister cote
// C# 1.81.0. Si l'un ressort, l'hypothese de parite est fausse.
string[] skPythonOnly =
[
    "SequentialOrchestration", "ConcurrentOrchestration", "GroupChatOrchestration",
    "MagenticOrchestration", "HandoffOrchestration",
];
Console.WriteLine("   (c) par NOM EXACT (convention Python) :");
foreach (var n in skPythonOnly)
    Console.WriteLine($"       {(sk.Contains(n) ? "PRESENT !! (hypothese fausse)" : "absent  OK")}  {n}");

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

var negativeOk = skPythonOnly.All(n => !sk.Contains(n))
              && skOrchestrationShaped.Count == 0
              && skOrchestrationAsm.Count == 0;
var positiveOk = mafBuilders.All(maf.Contains)
              && capabilities.All(maf.Contains)
              && skLegacy.All(sk.Contains);

Console.WriteLine();
Console.WriteLine($"VERDICT controles : negatif={(negativeOk ? "OK" : "ECHEC")} positif={(positiveOk ? "OK" : "ECHEC")}");
return negativeOk && positiveOk ? 0 : 1;
