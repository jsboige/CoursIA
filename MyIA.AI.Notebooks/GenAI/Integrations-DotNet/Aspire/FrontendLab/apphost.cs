#:sdk Aspire.AppHost.Sdk@13.4.6
using Aspire.Hosting;

// AppHost Aspire orchestrant une RESSOURCE FRONTEND Vite/pnpm -- grain #22363,
// axe Part 2 differe par #10897 (EPIC #10473 *The Unexpected AI Stack*).
//
// Choix de l'API, MESURE NuGet + runtime a la redaction (2026-10-24) :
//
//  1. Aspire.Hosting boxed 13.4.6 (la ligne vendue au depot) n'expose AUCUNE
//     API Node/Vite/Pnpm (XML du package verifie : 0 membre) ;
//  2. la ligne renommee CommunityToolkit.Aspire.Hosting.JavaScript.Extensions
//     13.x ne couvre que les monorepos Nx / Turborepo (AddNxApp,
//     AddTurborepoApp) -- un app Vite unitaire n'est ni l'un ni l'autre ;
//  3. la ligne qui porte AddViteApp (CommunityToolkit...NodeJS.Extensions
//     9.9.0, dependances >= Aspire.Hosting 9.5.2) COMPILE sous le SDK 13.4.6
//     mais sa ressource NodeAppResource 9.x n'est JAMAIS DEMARREE par
//     l'orchestrateur 13.x : apphost vert, dashboard pret, zero processus
//     pnpm/vitespawn, zero evenement de ressource (mesure au process monitor,
//     2 lancers). Aspire.Hosting.NodeJS s'arrete a 9.5.2 : la ligne est morte.
//
// La forme native 13.x pour orchestrer un dev-server frontend est donc la
// primitive boxed AddExecutable : le VRAI dev-server Vite lance par le VRAI
// gestionnaire pnpm, orchestre par le VRAI AppHost (SOTA-OK, aucune
// reimplementation). L'ecart AddViteApp <-> AddExecutable est documente dans
// le carnet (section parite) : AddViteApp cache le script ("dev"), le
// gestionnaire et l'endpoint ; AddExecutable les rend explicites.
//
// Endpoint cible (targetPort) 5173 SANS port hote : une ressource executable
// non conteneur ne peut pas etre proxiee avec port == targetPort (erreur
// mesuree DcpModelUtilities : "Non-container resources cannot be proxied
// when both TargetPort and Port are specified with the same value") -- le
// dev-server ecoute directement son port, le carnet sonde
// http://127.0.0.1:5173, meme forme deterministe que le precedent
// Orleans/02 (gateway 30000).

var builder = DistributedApplication.CreateBuilder(args);

// Resolution du gestionnaire de paquets : pnpm installe user-scope (npm -g)
// vit dans %APPDATA%\npm\pnpm.cmd, HORS du PATH herite par l'AppHost (erreur
// mesuree DCP : exec: "pnpm.cmd": executable file not found in %PATH% --
// l'orchestrateur resout la commande sans shell). Chemin absolu calcule au
// runtime, meme forme que le precedent GenAiStack.AppHost (UserProfile +
// .cache/huggingface) : le source reste portable d'une machine a l'autre.
var pnpmCmd = Path.Combine(
    Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData), "npm", "pnpm.cmd");

builder.AddExecutable("frontend", pnpmCmd, "./frontend", "dev")
    .WithHttpEndpoint(targetPort: 5173, name: "http");

builder.Build().Run();
