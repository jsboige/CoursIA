#:sdk Aspire.AppHost.Sdk@13.4.6
using Aspire.Hosting;

// AppHost déclarant LA pile GenAI réelle du cluster — Epic #10473 *The
// Unexpected AI Stack: C#/.NET*, grain #10857 (suite du grain #10838).
//
// Deux typologies de ressources, parce que la pile réelle est exactement ça :
//
//  1. Endpoints EXTERNES — les services lourds, liés à une GPU, déjà démarrés
//     en production et volontairement SINGLETONS (on ne duplique pas 24 Go de
//     VRAM par worktree). Aspire les déclare comme chaînes de connexion : ils
//     deviennent des ressources de premier plan dans le dashboard, sans être
//     recréés.
//       - comfyui : génération d'images Qwen (po-2023, 127.0.0.1:8188)
//       - vllm    : LLM qwen3.6-35b-a3b auto-hébergé (ai-01, LAN :5002),
//                   endpoint OpenAI-compatible partagé par toute la flotte
//
//  2. Conteneur ORCHESTRABLE — le service léger de la même pile, lazy-load,
//     que `aspire run --isolated` peut dupliquer par worktree sans collision
//     de ports ni de conteneurs :
//       - whisper-api (faster-whisper large-v3-turbo, image locale buildée
//         depuis docker-configurations/services/whisper-api)
//
// Aucun secret en littéral : le service orchestré tourne avec AUTH_ENABLED=false
// (contrat auth_middleware.py), et les endpoints externes exigent leurs clés au
// moment de l'appel (notebook) — jamais dans ce fichier.

var builder = DistributedApplication.CreateBuilder(args);

var repoRoot = Path.GetFullPath(Path.Combine(Directory.GetCurrentDirectory(), "../../../../"));

// ── 1. Endpoints externes de la pile (référencés, pas recréés) ──────────
// La valeur passe par la configuration (ConnectionStrings:{nom}) : la
// surcharge à 2 arguments de AddConnectionString interprète le second comme
// un NOM de variable d'environnement, pas comme la valeur.
builder.Configuration["ConnectionStrings:comfyui"] = "http://127.0.0.1:8188";
builder.Configuration["ConnectionStrings:vllm"] = "http://192.168.0.47:5002";
builder.AddConnectionString("comfyui");
builder.AddConnectionString("vllm");

// ── 2. Conteneur orchestrable (le représentant dupliquable de la pile) ──
var whisper = builder.AddContainer("whisper-api", "whisper-api-whisper-api")
    .WithContainerRuntimeArgs("--gpus", "all")
    .WithEnvironment("WHISPER_MODEL", "large-v3-turbo")
    .WithEnvironment("WHISPER_DEVICE", "cuda")
    .WithEnvironment("WHISPER_COMPUTE_TYPE", "int8_float16")
    .WithEnvironment("PRELOAD_MODEL", "false")
    .WithEnvironment("IDLE_TIMEOUT", "1200")
    .WithEnvironment("CUDA_VISIBLE_DEVICES", "1")   // RTX 3090 externe (regle freeze GPU du depot)
    .WithEnvironment("AUTH_ENABLED", "false")
    .WithBindMount(Path.Combine(repoRoot, "docker-configurations/services/shared"), "/app/shared", isReadOnly: true)
    .WithBindMount(Path.Combine(repoRoot, "docker-configurations/services/whisper-api/models"), "/app/models")
    .WithBindMount(Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), ".cache/huggingface"), "/home/appuser/.cache/huggingface")
    .WithHttpEndpoint(targetPort: 8190, name: "http");   // port hôte éphémère (--isolated)

builder.Build().Run();
