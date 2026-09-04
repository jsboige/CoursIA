# Aspire — orchestrer notre pile GenAI en C#

Dossier des grains **#10838** et **#10857** de l'Epic **#10473** — *The Unexpected AI Stack: C#/.NET*,
et des grains 1-3 de la digestion **#11516** (Parts 3-5 de la même série).
Ligne de parité #10838 : « **Isolation de ports par worktree** : à la main →
**`aspire run --isolated`** ». Ligne de parité #10857 : « **Modéliser la pile
réelle multi-machines dans un AppHost unique** : endpoints externes référencés
(ComfyUI, vLLM) + conteneurs orchestrables (whisper-api) ». Grain 2 #11516 :
« **Tests d'intégration modernes** : Testcontainers + TUnit + rollback — le
paradigme de test absent du dépôt, démontré réel ».

## Contenu

| Élément | Rôle |
|---|---|
| [`GenAiStack.AppHost/apphost.cs`](GenAiStack.AppHost/apphost.cs) | AppHost Aspire (SDK file-based `#:sdk Aspire.AppHost.Sdk@13.4.6`) orchestrant **notre** service GenAI réel — whisper-api (image locale buildée depuis `docker-configurations/services/whisper-api`) |
| [`GenAiStack.AppHost-wt2/apphost.cs`](GenAiStack.AppHost-wt2/apphost.cs) | **Copie identique** — joue le rôle du deuxième worktree pour la démonstration d'isolation de ports |
| [`GenAiStackReel.AppHost/apphost.cs`](GenAiStackReel.AppHost/apphost.cs) | AppHost du grain **#10857** : la **pile réelle** — comfyui (po-2023:8188) et vllm (ai-01:5002) déclarés comme `ConnectionStrings` (référencés, jamais recréés), plus le conteneur whisper-api orchestrable |
| [`GenAiStackReel.AppHost-wt2/apphost.cs`](GenAiStackReel.AppHost-wt2/apphost.cs) | Copie pour la 2e instance isolée |
| [`01-Aspire-Orchestration-GenAi.ipynb`](01-Aspire-Orchestration-GenAi.ipynb) | Notebook .NET Interactive : lancement `--isolated` de **deux instances simultanées**, `aspire describe`/`logs`, transcription réelle par le service orchestré, 3 exercices |
| [`02-Aspire-GenAiStack-Reel.ipynb`](02-Aspire-GenAiStack-Reel.ipynb) | Notebook #10857 : deux instances isolées de la pile réelle, `describe`/`logs`, **appels traversants authentifiés** (complétion vLLM `qwen3.6-35b-a3b`, `system_stats` ComfyUI), 3 exercices |
| [`04-Aspire-Streaming-Agent.ipynb`](04-Aspire-Streaming-Agent.ipynb) | Notebook #11516 (A1+A2) : le pattern **agent streaming** en .NET — `System.Threading.Channels` (canaux inbound/outbound, backpressure), `BackgroundService` (cycle de vie), minimal API typée `TypedResults` — 3 exercices |
| [`StreamingAgent.App/`](StreamingAgent.App/) | Projet .NET 10 du notebook 04 : un service d'agent réel (BackgroundService + Channels) exposé par des endpoints typés `/health`, `/greet`, `/stream` |
| [`05-Aspire-Tests-Integration.ipynb`](05-Aspire-Tests-Integration.ipynb) | Notebook #11516 Grain 2 (axes A5/A6/A7) : **tests d'intégration modernes** — TUnit + Microsoft Testing Platform, Testcontainers Postgres 18 jetable à port aléatoire, isolation par rollback transactionnel, filtres `--treenode-filter`, 3 exercices |
| [`IntegrationTests/`](IntegrationTests/) | Projet de tests auto-contenu (TUnit 1.65 + Testcontainers.PostgreSql 4.14 + EF Core 10 sur `net10.0`) : `dotnet test` démarre un vrai Postgres 18, 5/5 tests verts, conteneur auto-purgé |
| [`06-Aspire-GardeFous-Roslyn.ipynb`](06-Aspire-GardeFous-Roslyn.ipynb) | Notebook #10473 (axe Roslyn) : **analyseurs Roslyn comme garde-fous du code d'agent** — `DiagnosticAnalyzer` AGENTGUARD001 (blocage synchrone `.Result`/`.Wait()` d'une Task), verdict rendu par `dotnet build` lui-même + canal API (Verifier par compilation Roslyn en mémoire), contraste Python (ruff hors compilation), 3 exercices |
| [`AgentGuard.Analyzers/`](AgentGuard.Analyzers/) · [`AgentGuard.Demo/`](AgentGuard.Demo/) · [`AgentGuard.Verifier/`](AgentGuard.Verifier/) | Projets du notebook 06 : l'analyseur (netstandard2.0, chargé par `OutputItemType="Analyzer"`), le terrain fautif (copie de démo du motif notebook 04 avec `.Result` injecté — 2 avertissements au build), et le vérificateur de verdicts (compilation `CSharpCompilation` + `WithAnalyzers` sur les ref packs du SDK) |
| [`assets/echantillon-test-fr.wav`](assets/echantillon-test-fr.wav) | Échantillon audio FR de test (synthèse SAPI Windows) envoyé au service orchestré |

## Prérequis

- SDK **.NET 10** (`dotnet --version` ≥ 10.0.110) et **CLI Aspire** 13.4.6 (`dotnet tool install -g Aspire.Cli`)
- **Docker** démarré + image locale `whisper-api-whisper-api:latest` (buildée depuis le Dockerfile de `docker-configurations/services/whisper-api`)
- GPU NVIDIA (le conteneur exige `--gpus all` ; la config est dans l'AppHost, `CUDA_VISIBLE_DEVICES=1` = RTX 3090 externe)
- Cache HuggingFace hôte contenant le modèle `faster-whisper-large-v3-turbo` (sinon, premier appel = téléchargement ~1.6 Go, une seule fois)
- Pour le notebook 02 (#10857) : la **pile réelle** joignable — conteneur `comfyui-qwen` démarré (8188) et `VLLM_API_KEY` rendu dans `GenAI/.env` (modèle : [`.env.example`](../.env.example)) via `scripts/secrets/render_envs.py` depuis `master.env`
- Pour le notebook 04 (#11516) : **aucun Docker requis** — `StreamingAgent.App` compile avec le SDK .NET 10 seul (`dotnet build`), puis le notebook le lance et l'interroge (port local 5128)
- Pour le notebook 05 / `IntegrationTests/` (#11516 Grain 2) : Docker suffit — l'image `postgres:18` est tirée au premier `dotnet test` (~30 s), les conteneurs de test s'auto-purgent

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

## Voir aussi

- Issue [#10838](https://github.com/jsboige/CoursIA/issues/10838) · Issue [#10857](https://github.com/jsboige/CoursIA/issues/10857) · Epic [#10473](https://github.com/jsboige/CoursIA/issues/10473)
- Digestion [#11516](https://github.com/jsboige/CoursIA/issues/11516) (Parts 3-5 : streaming agent, tests d'intégration, observabilité) — série source [chrlschn.dev](https://chrlschn.dev/blog/2026/08/the-unexpected-ai-stack-csharp-dotnet-part-4/)
- Grain #10474 : backend d'observabilité OTLP [`aspire-otel/`](../SemanticKernel/aspire-otel/) (même pattern SDK file-based)
- Observabilité de la série SemanticKernel : [`04-Filters-Observability.ipynb`](../SemanticKernel/04-SemanticKernel-Filters-Observability.ipynb) (même famille A9, application directe au service streaming)
- Pile GenAI : [`docker-configurations/`](../../../docker-configurations/)
