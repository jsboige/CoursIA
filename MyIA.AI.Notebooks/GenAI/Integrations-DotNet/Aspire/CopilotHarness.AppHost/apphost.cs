#:sdk Aspire.AppHost.Sdk@13.4.6
using Aspire.Hosting;

// AppHost Aspire orchestrant le HARNESS GitHub Copilot SDK comme une ressource --
// grain #10473, residuel declare dans le registre des axes distillables
// (`Aspire/distilled-axes-registry.md`, ligne « Copilot SDK binding C# (Part 3) » :
// « Aspire AppHost integration (cf. #10857) »).
//
// Ce que ce lab demontre, et que le carnet 09 ne pouvait pas montrer : le harness
// n'est plus un processus qu'on lance a la main dans une cellule, c'est une
// RESSOURCE du graphe. L'orchestrateur decide son port, lui injecte sa
// configuration par l'environnement, suit son etat et son flux de logs -- et le
// carnet interroge la ressource a travers HTTP.
//
// Choix mesure : AddExecutable plutot que AddProject. Le harness est un projet
// .NET (CopilotHarness.App), mais un AppHost file-based (`apphost.cs`, la forme
// de cette serie) ne porte pas de ProjectReference : AddExecutable avec le vrai
// `dotnet run` lance le VRAI projet (SOTA-OK, aucune reimplementation), au prix
// d'un re-build gere par dotnet lui-meme. Le commentaire du FrontendLab de cette
// meme serie documente le meme arbitrage pour une ressource Node/Vite.
//
// Endpoint : targetPort seul (5099), sans port hote -- meme contrainte mesuree
// que FrontendLab (une ressource non conteneur ne peut pas etre proxiee avec
// Port == TargetPort) ; le service ecoute directement et le carnet sonde
// http://127.0.0.1:5099.

var builder = DistributedApplication.CreateBuilder(args);

// Le `dotnet` du PATH est l'hote systeme, qui ne voit AUCUN SDK sur ce siege :
// les SDK vivent en local utilisateur. L'AppHost exporte donc le DOTNET_ROOT
// resolu a l'execution vers la ressource enfant -- sans quoi `dotnet run`
// echoue dans le processus orchestre alors qu'il reussit dans un shell
// (ecart mesure au premier lancement).
var localDotnet = Path.Combine(
    Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "Microsoft", "dotnet");
var dotnetRoot = Directory.Exists(localDotnet)
    ? localDotnet
    : (Environment.GetEnvironmentVariable("DOTNET_ROOT") ?? string.Empty);
var dotnetExe = Path.Combine(dotnetRoot, "dotnet.exe");

var harness = builder.AddExecutable(
        "copilot-harness", dotnetExe, ".", "run", "--project", "../CopilotHarness.App", "--", "serve")
    .WithEnvironment("DOTNET_ROOT", dotnetRoot)
    .WithEnvironment("PORT", "5099")
    .WithEnvironment("COPILOT_RESOURCE_NAME", "copilot-harness")
    // Configuration injectee par l'orchestrateur, pas lue par le service :
    // /config la renvoie telle quelle, ce qui rend l'injection observable.
    .WithEnvironment("COPILOT_MODEL_ID", "claude-sonnet-5")
    .WithHttpEndpoint(targetPort: 5099, name: "http");

builder.Build().Run();
