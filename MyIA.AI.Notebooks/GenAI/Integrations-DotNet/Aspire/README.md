# Aspire — orchestrer notre pile GenAI en C#

Dossier des grains **#10838** et **#10857** de l'Epic **#10473** — *The Unexpected AI Stack: C#/.NET*,
et des grains 1-3 de la digestion **#11516** (Parts 3-5 de la même série).
Ligne de parité #10838 : « **Isolation de ports par worktree** : à la main →
**`aspire run --isolated`** ». Ligne de parité #10857 : « **Modéliser la pile
réelle multi-machines dans un AppHost unique** : endpoints externes référencés
(ComfyUI, vLLM) + conteneurs orchestrables (whisper-api) ». Grain 2 #11516 :
« **Tests d'intégration modernes** : Testcontainers + TUnit + rollback — le
paradigme de test absent du dépôt, démontré réel ».

Le résiduel déclaré de l'axe **Copilot SDK** (« Aspire AppHost integration »,
registre [des axes distillables](distilled-axes-registry.md)) est soldé par le
grain **#22388** : le harness du notebook 09 devient une ressource d'un graphe
orchestré (notebook 11).

## Contenu

| Élément | Rôle |
|---|---|
| [`GenAiStack.AppHost/apphost.cs`](GenAiStack.AppHost/apphost.cs) | AppHost Aspire (SDK file-based `#:sdk Aspire.AppHost.Sdk@13.4.6`) orchestrant **notre** service GenAI réel — whisper-api (image locale buildée depuis `docker-configurations/services/whisper-api`) |
| [`GenAiStack.AppHost-wt2/apphost.cs`](GenAiStack.AppHost-wt2/apphost.cs) | **Copie identique** — joue le rôle du deuxième worktree pour la démonstration d'isolation de ports |
| [`GenAiStackReel.AppHost/apphost.cs`](GenAiStackReel.AppHost/apphost.cs) | AppHost du grain **#10857** : la **pile réelle** — comfyui (po-2023:8188) et vllm (ai-01:5002) déclarés comme `ConnectionStrings` (référencés, jamais recréés), plus le conteneur whisper-api orchestrable |
| [`GenAiStackReel.AppHost-wt2/apphost.cs`](GenAiStackReel.AppHost-wt2/apphost.cs) | Copie pour la 2e instance isolée |
| [`01-Aspire-Orchestration-GenAi.ipynb`](01-Aspire-Orchestration-GenAi.ipynb) | Notebook .NET Interactive : lancement `--isolated` de **deux instances simultanées**, `aspire describe`/`logs`, transcription réelle par le service orchestré, 3 exercices |
| [`02-Aspire-GenAiStack-Reel.ipynb`](02-Aspire-GenAiStack-Reel.ipynb) | Notebook #10857 : deux instances isolées de la pile réelle, `describe`/`logs`, **appels traversants authentifiés** (complétion vLLM `qwen3.6-35b-a3b`, `system_stats` ComfyUI), 3 exercices |
| [`03-Aspire-Observabilite.ipynb`](03-Aspire-Observabilite.ipynb) | Notebook #11516 (Part 5) : **observabilité .NET** sur la librairie, sans AppHost — **Serilog** (logs structurés, template `{Propriété}`), **OpenTelemetry** (`ActivitySource`, spans, `TracerProvider` avec exporteur console), instrumentation **call-site** (`CallerMemberName` / `CallerFilePath` / `CallerLineNumber` posés en tags `code.*`), corrélation log ↔ trace (`@tr` / `@sp`), puis boucle fermée OTLP + dashboard Aspire — 3 exercices |
| [`04-Aspire-Streaming-Agent.ipynb`](04-Aspire-Streaming-Agent.ipynb) | Notebook #11516 (A1+A2) : le pattern **agent streaming** en .NET — `System.Threading.Channels` (canaux inbound/outbound, backpressure), `BackgroundService` (cycle de vie), minimal API typée `TypedResults` — 3 exercices |
| [`StreamingAgent.App/`](StreamingAgent.App/) | Projet .NET 10 du notebook 04 : un service d'agent réel (BackgroundService + Channels) exposé par des endpoints typés `/health`, `/greet`, `/stream` |
| [`05-Aspire-Tests-Integration.ipynb`](05-Aspire-Tests-Integration.ipynb) | Notebook #11516 Grain 2 (axes A5/A6/A7) : **tests d'intégration modernes** — TUnit + Microsoft Testing Platform, Testcontainers Postgres 18 jetable à port aléatoire, isolation par rollback transactionnel, filtres `--treenode-filter`, 3 exercices |
| [`IntegrationTests/`](IntegrationTests/) | Projet de tests auto-contenu (TUnit 1.65 + Testcontainers.PostgreSql 4.14 + EF Core 10 sur `net10.0`) : `dotnet test` démarre un vrai Postgres 18, 5/5 tests verts, conteneur auto-purgé |
| [`06-Aspire-GardeFous-Roslyn.ipynb`](06-Aspire-GardeFous-Roslyn.ipynb) | Notebook #10473 (axe Roslyn) : **analyseurs Roslyn comme garde-fous du code d'agent** — `DiagnosticAnalyzer` AGENTGUARD001 (blocage synchrone `.Result`/`.Wait()` d'une Task), verdict rendu par `dotnet build` lui-même + canal API (Verifier par compilation Roslyn en mémoire), contraste Python (ruff hors compilation) |
| [`AgentGuard.Analyzers/`](AgentGuard.Analyzers/) · [`AgentGuard.Demo/`](AgentGuard.Demo/) · [`AgentGuard.Verifier/`](AgentGuard.Verifier/) | Projets du notebook 06 : l'analyseur (netstandard2.0, chargé par `OutputItemType="Analyzer"`), le terrain fautif (copie de démo du motif notebook 04 avec `.Result` injecté — 2 avertissements au build), et le vérificateur de verdicts (compilation `CSharpCompilation` + `WithAnalyzers` sur les ref packs du SDK) |
| [`07-Aspire-SemanticFleet-MultiConnector.ipynb`](07-Aspire-SemanticFleet-MultiConnector.ipynb) | Notebook de l'**axe 6** de l'Epic **#1210** (semantic-fleet) : rejoue dans le notebook le POC arithmétique du **MultiConnector** de 2023 (sous-module `semantic-fleet`, lu en référence, non importé) et le ré-instrumente sous **OpenTelemetry** — vetting en ligne (primaire et secondaires, offload par signature), double file à coalescence accumulation / remplacement, debounce ancré sur l'horodatage, pool de sockets et serveur de test — 3 exercices. Kernel .NET 9+, sans service externe ni Docker |
| [`08-Aspire-AsyncFFI-Dotnet.ipynb`](08-Aspire-AsyncFFI-Dotnet.ipynb) | **Asynchrone aux frontières natives** : P/Invoke (types blittables, piège du `bool`), reverse P/Invoke (`UnmanagedCallersOnly`, callbacks), pont `TaskCompletionSource` + `GCHandle`, durées de vie (`SafeHandle`, `GC.KeepAlive`). La famine est **observée qualitativement** (un thread étranger simule un runtime natif de type Tokio), pas mesurée ; l'exemple natif `EnumWindows` de `user32.dll` ne tourne que sous **Windows** — 3 exercices |
| [`09-Aspire-Harness-CopilotSdk.ipynb`](09-Aspire-Harness-CopilotSdk.ipynb) | Notebook #10473 (axe Copilot SDK, veille #10475) : **le harness des Copilot coding agents en C#** — `GitHub.Copilot.SDK` 1.0.13 (runtime agent embarqué, aucune CLI externe), `CopilotClient` avec auth héritée de `gh` (aucune clé dans le code), catalogue des 15 modèles servis (`ListModelsAsync`), tour complet `SendAndWaitAsync` (réponse réelle), cycle de vie `SessionEvent` observé (histogramme du tour + contenu ré-assemblé), 3 exercices |
| [`10-Aspire-AppHost-Frontend.ipynb`](10-Aspire-AppHost-Frontend.ipynb) | Notebook #22363 (axe *AppHost frontend*, différé par #10897) : **orchestrer un dev-server Vite/pnpm comme ressource de l'AppHost**. Le paysage NuGet mesuré (Aspire.Hosting 13.4.6 sans API Node ; `AddViteApp` réduit aux monorepos Nx/Turborepo ; la ligne 9.x qui le portait compile sous le SDK 13 mais sa ressource n'est jamais démarrée), la primitive native `AddExecutable`, le piège de résolution de commande (l'orchestrateur n'ouvre aucun shell : chemin absolu de `pnpm.cmd`), la règle d'endpoint d'une ressource non conteneur, sondes HTTP réelles sur le dev-server, table de parité avec `docker-compose`/frontend Python, 3 exercices |
| [`11-Aspire-Copilot-Harness-AppHost.ipynb`](11-Aspire-Copilot-Harness-AppHost.ipynb) | Notebook #22388 (résiduel « Aspire AppHost integration » de l'axe Copilot SDK) : le harness du notebook 09 devient **une ressource d'un graphe Aspire** — mode `serve` (`/health`, `/config`, `/models`, `/ask`), AppHost file-based `AddExecutable` + `WithHttpEndpoint(targetPort)`, port **proxy dynamique** devant le port fixe, `/config` qui rend **observable ce que l'orchestrateur injecte** (environnement, répertoire de travail : `CopilotHarness.AppHost` contre `CopilotHarness.App` en lancement direct), arrêt `aspire stop` et comparaison avec `docker-compose` — 3 exercices |
| [`CopilotHarness.App/`](CopilotHarness.App/) | Projet .NET 10 des notebooks 09 et 11 : console à quatre modes (`auth`/`models`/`ask`/`events`) pilotant le harness réel — dépendance unique `GitHub.Copilot.SDK` 1.0.13 — plus le mode `serve` du notebook 11, qui expose les mêmes capacités en HTTP sans changer de binaire |
| [`CopilotHarness.AppHost/`](CopilotHarness.AppHost/) | AppHost du notebook 11 : `apphost.cs` (`#:sdk Aspire.AppHost.Sdk@13.4.6`) + `aspire.config.json`, déclarant le harness comme ressource `Executable` et lui injectant `PORT`, `COPILOT_RESOURCE_NAME` et `COPILOT_MODEL_ID` |
| [`FrontendLab/`](FrontendLab/) | Lab du notebook 10 : AppHost file-based (`apphost.cs` + `aspire.config.json`) déclarant la ressource `frontend`, et `frontend/` (Vite 7 ; `pnpm-workspace.yaml` porte la table `allowBuilds` exigée par pnpm 11+ ; lockfile versionné). **Aucun Docker requis** |
| [`assets/echantillon-test-fr.wav`](assets/echantillon-test-fr.wav) | Échantillon audio FR de test (synthèse SAPI Windows) envoyé au service orchestré |

## Prérequis

- SDK **.NET 10** (`dotnet --version` ≥ 10.0.110) et **CLI Aspire** 13.4.6 (`dotnet tool install -g Aspire.Cli`)
- **Docker** démarré + image locale `whisper-api-whisper-api:latest` (buildée depuis le Dockerfile de `docker-configurations/services/whisper-api`)
- GPU NVIDIA (le conteneur exige `--gpus all` ; la config est dans l'AppHost, `CUDA_VISIBLE_DEVICES=1` = RTX 3090 externe)
- Cache HuggingFace hôte contenant le modèle `faster-whisper-large-v3-turbo` (sinon, premier appel = téléchargement ~1.6 Go, une seule fois)
- Pour le notebook 02 (#10857) : la **pile réelle** joignable — conteneur `comfyui-qwen` démarré (8188) et `VLLM_API_KEY` rendu dans `GenAI/.env` (modèle : [`.env.example`](../../.env.example)) via `scripts/secrets/render_envs.py` depuis `master.env`
- Pour le notebook 04 (#11516) : **aucun Docker requis** — `StreamingAgent.App` compile avec le SDK .NET 10 seul (`dotnet build`), puis le notebook le lance et l'interroge (port local 5128)
- Pour le notebook 05 / `IntegrationTests/` (#11516 Grain 2) : Docker suffit — l'image `postgres:18` est tirée au premier `dotnet test` (~30 s), les conteneurs de test s'auto-purgent
- Pour le notebook 09 / `CopilotHarness.App/` (#10473) : **aucune installation** — le package embarque son runtime ; l'authentification passe par la session `gh` locale (abonnement Copilot requis) ; compter ~2 requêtes premium par passage complet du notebook
- Pour le notebook 11 / `CopilotHarness.AppHost/` (#22388) : **aucun Docker requis**, mais le CLI `aspire` doit voir un SDK .NET 10. Sur un siège où le SDK est en portée utilisateur (`%LOCALAPPDATA%\Microsoft\dotnet`) et où l'hôte `Program Files` ne porte que des runtimes, `aspire run` sort en **code 11** (« requires .NET SDK version 10.0.100 or later. Detected: (not found) ») tant que ce dossier n'est pas dans le `PATH` — `DOTNET_ROOT` seul ne suffit pas. Les modes `auth`/`models`/`ask`/`events` du harness, eux, ne dépendent pas du CLI.
- Pour le notebook 08 : **Windows** requis — l'exemple natif appelle `EnumWindows` de `user32.dll`
- Pour le notebook 10 / `FrontendLab/` (#22363) : **aucun Docker requis** — Node.js et pnpm (`npm install -g pnpm`) suffisent, la cellule d'installation du carnet lance `pnpm install`. L'AppHost résout `pnpm.cmd` par un **chemin absolu** calculé à l'exécution (`%APPDATA%\npm`), parce que l'orchestrateur n'hérite pas du PATH de l'utilisateur

## Démarrage rapide

```bash
cd MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/GenAiStack.AppHost
aspire run --detach --isolated      # instance A (ports randomisés)
aspire describe whisper-api         # état + URL du service
aspire logs whisper-api             # journaux unifiés
aspire stop                         # arrêt + suppression des conteneurs
```

Deux instances simultanées : lancer la même commande depuis
`GenAiStack.AppHost-wt2/` (le « deuxième worktree »). Les deux coexistent
sans collision — ports randomisés, noms de conteneurs suffixés.

## Points d'attention

- **Aucun secret dans l'AppHost** : `AUTH_ENABLED=false` désactive l'auth du
  service (contrat `auth_middleware.py`), les variables d'environnement sont
  non-secrètes, le token d'API n'est jamais un littéral.
- **Bind mounts** : le conteneur dépend de `docker-configurations/services/shared`
  (module `lazy_model`) et du cache HuggingFace hôte — chemins résolus
  relativement à l'AppHost pour fonctionner depuis n'importe quel worktree.
- **`--detach` même répertoire** : deux instances `--isolated` du **même**
  répertoire ne coexistent pas (le CLI remplace l'instance précédente) — la
  forme authentique est **deux répertoires** (deux worktrees), démontrée dans
  le notebook §4.
- **`aspire stop` est scopé au worktree** : lancé depuis un autre répertoire, il
  répond « No running AppHost found in the current worktree » alors que
  `aspire ps` liste l'AppHost. Il se lance donc depuis le dossier de l'AppHost —
  et tuer le seul processus enfant laisse l'orchestrateur vivant (c'est lui qui
  possède le cycle de vie de la ressource, cf. notebook 11 §5).

## Voir aussi

- Issue [#10838](https://github.com/jsboige/CoursIA/issues/10838) · Issue [#10857](https://github.com/jsboige/CoursIA/issues/10857) · Epic [#10473](https://github.com/jsboige/CoursIA/issues/10473) · Issue [#22388](https://github.com/jsboige/CoursIA/issues/22388) (harness Copilot SDK orchestré)
- Digestion [#11516](https://github.com/jsboige/CoursIA/issues/11516) (Parts 3-5 : streaming agent, tests d'intégration, observabilité) — série source [chrlschn.dev](https://chrlschn.dev/blog/2026/08/the-unexpected-ai-stack-csharp-dotnet-part-4/)
- Grain #10474 : backend d'observabilité OTLP [`aspire-otel/`](../../SemanticKernel/aspire-otel/) (même pattern SDK file-based)
- Observabilité de la série SemanticKernel : [`04-Filters-Observability.ipynb`](../../SemanticKernel/04-SemanticKernel-Filters-Observability.ipynb) (même famille A9, application directe au service streaming)
- Pile GenAI : [`docker-configurations/`](../../../../docker-configurations/)
