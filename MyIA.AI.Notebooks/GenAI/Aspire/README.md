# Aspire — orchestrer notre pile GenAI en C#

Dossier des grains **#10838** et **#10857** de l'Epic **#10473** — *The Unexpected AI Stack: C#/.NET*.
Ligne de parité #10838 : « **Isolation de ports par worktree** : à la main →
**`aspire run --isolated`** ». Ligne de parité #10857 : « **Modéliser la pile
réelle multi-machines dans un AppHost unique** : endpoints externes référencés
(ComfyUI, vLLM) + conteneurs orchestrables (whisper-api) ».

## Contenu

| Élément | Rôle |
|---|---|
| [`GenAiStack.AppHost/apphost.cs`](GenAiStack.AppHost/apphost.cs) | AppHost Aspire (SDK file-based `#:sdk Aspire.AppHost.Sdk@13.4.6`) orchestrant **notre** service GenAI réel — whisper-api (image locale buildée depuis `docker-configurations/services/whisper-api`) |
| [`GenAiStack.AppHost-wt2/apphost.cs`](GenAiStack.AppHost-wt2/apphost.cs) | **Copie identique** — joue le rôle du deuxième worktree pour la démonstration d'isolation de ports |
| [`GenAiStackReel.AppHost/apphost.cs`](GenAiStackReel.AppHost/apphost.cs) | AppHost du grain **#10857** : la **pile réelle** — comfyui (po-2023:8188) et vllm (ai-01:5002) déclarés comme `ConnectionStrings` (référencés, jamais recréés), plus le conteneur whisper-api orchestrable |
| [`GenAiStackReel.AppHost-wt2/apphost.cs`](GenAiStackReel.AppHost-wt2/apphost.cs) | Copie pour la 2e instance isolée |
| [`01-Aspire-Orchestration-GenAi.ipynb`](01-Aspire-Orchestration-GenAi.ipynb) | Notebook .NET Interactive : lancement `--isolated` de **deux instances simultanées**, `aspire describe`/`logs`, transcription réelle par le service orchestré, 3 exercices |
| [`02-Aspire-GenAiStack-Reel.ipynb`](02-Aspire-GenAiStack-Reel.ipynb) | Notebook #10857 : deux instances isolées de la pile réelle, `describe`/`logs`, **appels traversants authentifiés** (complétion vLLM `qwen3.6-35b-a3b`, `system_stats` ComfyUI), 3 exercices |
| [`assets/echantillon-test-fr.wav`](assets/echantillon-test-fr.wav) | Échantillon audio FR de test (synthèse SAPI Windows) envoyé au service orchestré |

## Prérequis

- SDK **.NET 10** (`dotnet --version` ≥ 10.0.110) et **CLI Aspire** 13.4.6 (`dotnet tool install -g Aspire.Cli`)
- **Docker** démarré + image locale `whisper-api-whisper-api:latest` (buildée depuis le Dockerfile de `docker-configurations/services/whisper-api`)
- GPU NVIDIA (le conteneur exige `--gpus all` ; la config est dans l'AppHost, `CUDA_VISIBLE_DEVICES=1` = RTX 3090 externe)
- Cache HuggingFace hôte contenant le modèle `faster-whisper-large-v3-turbo` (sinon, premier appel = téléchargement ~1.6 Go, une seule fois)
- Pour le notebook 02 (#10857) : la **pile réelle** joignable — conteneur `comfyui-qwen` démarré (8188) et `VLLM_API_KEY` rendu dans `GenAI/.env` (modèle : [`.env.example`](../.env.example)) via `scripts/secrets/render_envs.py` depuis `master.env`

## Démarrage rapide

```bash
cd MyIA.AI.Notebooks/GenAI/Aspire/GenAiStack.AppHost
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
- Grain #10474 : backend d'observabilité OTLP [`aspire-otel/`](../SemanticKernel/aspire-otel/) (même pattern SDK file-based)
- Pile GenAI : [`docker-configurations/`](../../../docker-configurations/)
