// Test.exe -- harnais de mesure LLamaSharp 0.27.0 pour le bake-off GenAI/Texte 10e (#15570).
//
// Usage : Test.exe <chemin.gguf> <cap_jetons> <smoke|batch>
//   cap_jetons : plafond de jetons GENERES par requete (l'arret anticipe sur EOS reste
//                possible). Les compteurs « Tokens » ne comptent que les jetons generes.
//   smoke      : 1 invite (« Definis GGUF en deux phrases. »).
//   batch      : 4 invites identiques a la Phase 1 (#12645), executees en continuous
//                batching : toutes soumises au meme contexte avant la premiere etape,
//                chaque sequence rend son creneau au decodeur des qu'elle acheve.
//
// Sortie : banniere (date, hote .NET, assembly LLamaSharp), selection du backend natif,
// trace native llama.cpp ([native/...]) si activee par defaut, puis par requete :
// jetons, pad, duree, debit, et enfin le resume agrege. Les decimales sont formattees
// a la francaise (virgule), comme le run de reference du 2026-09-02.
//
// Ce harnais reconstruit l'original (jamais versionne, perdu avec C:/dev/_scratch,
// cf #15570) a partir du contrat d'appel et du format de sortie pinnes par les sorties
// executees commitees dans le notebook.

using System.Diagnostics;
using System.Globalization;
using System.Security.Cryptography;
using System.Text;
using LLama;
using LLama.Batched;
using LLama.Common;
using LLama.Native;
using LLama.Sampling;

if (args.Length != 3)
{
    Console.Error.WriteLine("Usage: Test.exe <chemin.gguf> <cap_jetons> <smoke|batch>");
    return 2;
}

// Le chemin est affiché TEL QUE PASSÉ (forme relative recommandée : une sortie
// commitée ne doit porter aucun chemin machine) mais résolu en absolu pour l'accès.
string ggufArg = args[0];
string gguf = Path.GetFullPath(ggufArg);
int cap = int.Parse(args[1]);
string mode = args[2].ToLowerInvariant();

string[] prompts = mode switch
{
    "smoke" => ["Definis GGUF en deux phrases."],
    "batch" =>
    [
        "Definis le cache KV en deux phrases.",
        "Definis le continuous batching en deux phrases.",
        "Definis GGUF en deux phrases.",
        "Definis une quantification Q4 en deux phrases.",
    ],
    _ => throw new ArgumentException($"mode inconnu : {mode} (attendu smoke|batch)"),
};

CultureInfo fr = CultureInfo.GetCultureInfo("fr-FR");

// Avant toute utilisation de LLamaSharp : installe le callback de logs natifs.
// C'est lui qui produit le dump de selection du backend (bloc LibraryName /
// PreferCuda / AVX2 / AutoFallback) et la trace llama.cpp prefixee [native/<niveau>],
// comme dans le run de reference.
NativeLibraryConfig.All.WithLogCallback((level, message) =>
    Console.WriteLine($"[native/{level}] {message?.TrimEnd('\r', '\n')}"));

Console.WriteLine("=== LLamaSharp 0.27.0 Bake-Off Qwen3-4B Q4_K_M ===");
Console.WriteLine($"Date UTC           : {DateTime.UtcNow:yyyy-MM-dd'T'HH:mm:ss'Z'}");
Console.WriteLine($"Host .NET          : {System.Runtime.InteropServices.RuntimeInformation.FrameworkDescription}");
Console.WriteLine($"Assembly LLamaSharp: {typeof(LLamaWeights).Assembly.FullName}");

Console.WriteLine($"llama_max_devices  : {NativeApi.llama_max_devices()}");
Console.WriteLine($"GGUF path          : {ggufArg}");
Console.WriteLine($"GGUF size          : {new FileInfo(gguf).Length / (1024 * 1024)} MiB");
Console.WriteLine($"GGUF sha256        : {Sha256Hex(gguf, 32)}... (truncated)");

var loadWatch = Stopwatch.StartNew();
var @params = new ModelParams(gguf)
{
    ContextSize = 2048,
    GpuLayerCount = 99,
};
using var model = LLamaWeights.LoadFromFile(@params);
loadWatch.Stop();
Console.WriteLine($"GGUF load elapsed   : {loadWatch.Elapsed.TotalSeconds.ToString("F2", fr)} s");
Console.WriteLine($"Context ready       : n_ctx={@params.ContextSize}, n_gpu_layers={@params.GpuLayerCount}");

// Le BatchedExecutor cree et possede son propre contexte a partir des memes parametres.
using var executor = new BatchedExecutor(model, @params);
var encoding = @params.Encoding ?? Encoding.UTF8;

// Temperature nulle : echantillonnage glouton (argmax), deterministe -- un harnais de
// mesure doit pouvoir comparer deux executions sans variance d'echantillonnage.
var pipeline = new DefaultSamplingPipeline { Temperature = 0f };

// Une file par invite, toutes soumises AVANT la premiere etape d'inference.
var rows = new List<Req>();
foreach (var prompt in prompts)
{
    var conversation = executor.Create();
    conversation.Prompt(prompt);
    rows.Add(new Req(prompt, conversation, new StreamingTokenDecoder(encoding, model)) { CanSample = true });
}

// Boucle de continuous batching : Infer() decode UNE etape pour toutes les sequences
// qui ont des jetons en attente ; chaque sequence promptee avant l'etape peut alors
// etre echantillonnee (Sample(pipeline, 0)). Rejeter le jeton via Prompt(token)
// refile la sequence pour l'etape suivante ; ne PAS le rejeter la retire du batch :
// son creneau de decodeur est libere pour les autres, sans padding. C'est ce que le
// compteur Pad (nul par construction) constate a chaque etape.
var batchWatch = Stopwatch.StartNew();
int safety = (cap + 16) * rows.Count + 64;
while (rows.Any(r => !r.Done) && safety-- > 0)
{
    await executor.Infer();

    foreach (var req in rows.Where(r => r.CanSample && !r.Done).ToList())
    {
        req.CanSample = false;
        LLamaToken token = req.Conversation.Sample(pipeline, 0);
        req.Generated++;
        req.Decoder.Add(token);

        if (req.Generated >= cap || token.IsEndOfGeneration(model.Vocab))
        {
            req.Done = true;
            req.Elapsed = batchWatch.Elapsed;
        }
        else
        {
            req.Conversation.Prompt(token);
            req.CanSample = true;
        }
    }
}

foreach (var req in rows)
    req.Text = req.Decoder.Read();

// --- Rapport par requete, puis resume agrege (formats du run de reference) ---
int totalTokens = 0;
double totalTime = 0;
for (int i = 0; i < rows.Count; i++)
{
    var req = rows[i];
    double seconds = req.Elapsed.TotalSeconds;
    totalTokens += req.Generated;
    totalTime += seconds;

    Console.WriteLine($"--- Requête {i + 1} ---");
    Console.WriteLine($"Prompt: {req.PromptText}");
    Console.WriteLine($"Tokens: {req.Generated}, Pad: {req.Pad}, Time: {seconds.ToString("F2", fr)}s, "
                      + $"Rate: {(req.Generated / seconds).ToString("F2", fr)} tok/s");
    Console.WriteLine("Output complet:");
    Console.WriteLine(req.Text);
    Console.WriteLine($"--- Fin requête {i + 1} ---");
}

int totalPad = rows.Sum(r => r.Pad);
Console.WriteLine("=== Résumé agrégé ===");
Console.WriteLine($"Requests          : {rows.Count}");
Console.WriteLine($"Total tokens brut : {totalTokens}");
Console.WriteLine($"Total <pad> jetons: {totalPad}");
Console.WriteLine($"Time total        : {totalTime.ToString("F2", fr)} s");
Console.WriteLine($"Rate agrégé brut  : {(totalTokens / totalTime).ToString("F2", fr)} tok/s");
Console.WriteLine($"Pad ratio         : {(100.0 * totalPad / Math.Max(totalTokens, 1)).ToString("F2", fr)}%");

return 0;

static string Sha256Hex(string path, int digits)
{
    // En flux : le GGUF (2,4 Go) depasse la limite int de ReadAllBytes.
    using var stream = File.OpenRead(path);
    var hash = SHA256.HashData(stream);
    return Convert.ToHexString(hash)[..digits].ToLowerInvariant();
}

internal sealed class Req(string promptText, Conversation conversation, StreamingTokenDecoder decoder)
{
    public string PromptText => promptText;
    public Conversation Conversation => conversation;
    public StreamingTokenDecoder Decoder => decoder;

    public int Generated { get; set; }
    public int Pad { get; } // continuous batching : 0 par construction (cf. boucle)
    public bool Done { get; set; }
    public bool CanSample { get; set; }
    public TimeSpan Elapsed { get; set; } = TimeSpan.Zero;
    public string Text { get; set; } = "";
}
