# Aspire — orchestrer notre pile GenAI en C#

Dossier du grain **#10838** de l'Epic **#10473** — *The Unexpected AI Stack: C#/.NET*.
La ligne de parité livrée : « **Isolation de ports par worktree** : à la main →
**`aspire run --isolated`** », avec du code exécuté (voir le notebook).

## Contenu

| Élément | Rôle |
|---|---|
| [`GenAiStack.AppHost/apphost.cs`](GenAiStack.AppHost/apphost.cs) | AppHost Aspire (SDK file-based `#:sdk Aspire.AppHost.Sdk@13.4.6`) orchestrant **notre** service GenAI réel — whisper-api (image locale buildée depuis `docker-configurations/services/whisper-api`) |
| [`GenAiStack.AppHost-wt2/apphost.cs`](GenAiStack.AppHost-wt2/apphost.cs) | **Copie identique** — joue le rôle du deuxième worktree pour la démonstration d'isolation de ports |
| [`01-Aspire-Orchestration-GenAi.ipynb`](01-Aspire-Orchestration-GenAi.ipynb) | Notebook .NET Interactive : lancement `--isolated` de **deux instances simultanées**, `aspire describe`/`logs`, transcription réelle par le service orchestré, 3 exercices |
| [`assets/echantillon-test-fr.wav`](assets/echantillon-test-fr.wav) | Échantillon audio FR de test (synthèse SAPI Windows) envoyé au service orchestré |

## Prérequis

- SDK **.NET 10** (`dotnet --version` ≥ 10.0.110) et **CLI Aspire** 13.4.6 (`dotnet tool install -g Aspire.Cli`)
- **Docker** démarré + image locale `whisper-api-whisper-api:latest` (buildée depuis le Dockerfile de `docker-configurations/services/whisper-api`)
- GPU NVIDIA (le conteneur exige `--gpus all` ; la config est dans l'AppHost)
- Cache HuggingFace hôte contenant le modèle `faster-whisper-large-v3-turbo` (sinon, premier appel = téléchargement ~1.6 Go, une seule fois)

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

- Issue [#10838](https://github.com/jsboige/CoursIA/issues/10838) · Epic [#10473](https://github.com/jsboige/CoursIA/issues/10473)
- Grain #10474 : backend d'observabilité OTLP [`aspire-otel/`](../SemanticKernel/aspire-otel/) (même pattern SDK file-based)
- Pile GenAI : [`docker-configurations/`](../../../docker-configurations/)
