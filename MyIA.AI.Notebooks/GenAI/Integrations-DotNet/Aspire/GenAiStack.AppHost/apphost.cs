#:sdk Aspire.AppHost.Sdk@13.4.6
using Aspire.Hosting;

// AppHost Aspire orchestrant un service RÉEL de la pile GenAI locale
// (image locale `whisper-api-whisper-api`, buildée depuis le Dockerfile de
// docker-configurations/services/whisper-api et exécutée par le compose
// manuel) — Epic #10473 *The Unexpected AI Stack*, grain #10838.
//
// L'objectif pédagogique est la ligne de parité « Isolation de ports par
// worktree : à la main  ->  aspire run --isolated » : le même AppHost peut
// être lancé en plusieurs instances simultanées (worktrees de travail), et
// `--isolated` randomise les ports ET isole les user secrets. Deux instances
// orchestrent donc chacune leur propre conteneur whisper-api, sans collision
// docker ni port.
//
// Le secret d'API (API_KEY) n'est PAS un littéral : il est généré à chaque
// démarrage de l'AppHost (Guid) et passé au conteneur — aucune valeur
// sensible dans le dépôt. La configuration non-secrète (modèle, device,
// compute type) suit les valeurs de docker-configurations/services/whisper-api.
//
// Note tooling : SDK file-based `#:sdk Aspire.AppHost.Sdk` (modèle canonique
// SDK-10, cf. aspire-otel/SkOtel.AppHost d'#10498) — pas de csproj.

var builder = DistributedApplication.CreateBuilder(args);

// Resource réelle : whisper-api (faster-whisper, OpenAI-compatible ASR).
// Image locale pré-buildée (docker-configurations/services/whisper-api,
// Dockerfile) = SOTA réel de notre pile, aucune réimplémentation.
//
// Le conteneur dépend de deux binds définis par le compose manuel :
//   - ../shared  -> /app/shared  (module lazy_model, requis à l'import)
//   - ./models   -> /app/models  (cache de modèles local)
// Les chemins sont résolus RELATIVEMENT à l'AppHost (racine du dépôt), pour
// que le même source fonctionne depuis n'importe quel worktree.
var repoRoot = Path.GetFullPath(Path.Combine(Directory.GetCurrentDirectory(), "../../../../"));

var whisper = builder.AddContainer("whisper-api", "whisper-api-whisper-api")
    .WithContainerRuntimeArgs("--gpus", "all")           // RTX 3090 (24 GB)
    .WithEnvironment("WHISPER_MODEL", "large-v3-turbo")  // config non-secrète
    .WithEnvironment("WHISPER_DEVICE", "cuda")
    .WithEnvironment("WHISPER_COMPUTE_TYPE", "int8_float16")
    .WithEnvironment("PRELOAD_MODEL", "false")           // lazy load : démarrage rapide
    .WithEnvironment("IDLE_TIMEOUT", "1200")
    .WithEnvironment("CUDA_VISIBLE_DEVICES", "0")
    .WithEnvironment("AUTH_ENABLED", "false")            // dev local : auth explicitement
                                                         // désactivée (auth_middleware), aucun secret
    .WithBindMount(Path.Combine(repoRoot, "docker-configurations/services/shared"), "/app/shared", isReadOnly: true)
    .WithBindMount(Path.Combine(repoRoot, "docker-configurations/services/whisper-api/models"), "/app/models")
    // Cache HuggingFace HÔTE partagé : le modèle large-v3-turbo téléchargé par le
    // conteneur manuel est réutilisé par le conteneur orchestré (et persiste
    // entre recréations). Même pattern que le volume nommé whisper-cache du compose.
    .WithBindMount(Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), ".cache/huggingface"), "/home/appuser/.cache/huggingface")
    .WithHttpEndpoint(targetPort: 8190, name: "http");   // port hôte éphémère (--isolated)

builder.Build().Run();
