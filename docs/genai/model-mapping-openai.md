# Mapping des modèles OpenAI — génération courante (tranche 1, #14755)

> **Grain : DEEP/genai — lane `myia-po-2023:CoursIA-2` — tranche 1 de #14755.**
> Date de vérification API : **2026-09-05**. **Aucune substitution de modèle dans cette tranche** — l'inventaire et la table ci-dessous précèdent les tranches 2-5 (substitution + re-exécution).

## Objet

#14755 demande de remplacer les références datées (`gpt-4o-mini` 2024, `gpt-3.5-turbo`, …) par la génération courante, plutôt que de continuer à ré-exécuter sur des modèles qui n'ont plus de sens. La cible nommée par le user : **« OpenAI 5.6 »** pour le modèle principal, **« Luna »** pour la taille *mini*.

Le mandat insiste : **« les identifiants exacts d'API sont à vérifier firsthand contre le fournisseur — ne pas déduire un nom d'API d'un nom commercial. »** Ce document est le produit de cette vérification : c'est la table de correspondance `ancien -> nouveau`, par famille d'usage, adossée à la réponse des endpoints.

## Table de correspondance (vérifiée contre l'API)

| Famille d'usage | Ancien modèle (obsolète) | Occurrences | Nouveau modèle (vérifié) | Rôle |
|---|---|---|---|---|
| **chat — principal** | `gpt-4` · `gpt-4-turbo` · `gpt-4o` · `gpt-4o-2024-08-06` · `gpt-4.1` | 128 + 33 + 152 + 2 + 10 = **325** | **`gpt-5.6-sol`** | flagship de la série 5.6 |
| **chat — héritage** | `gpt-3.5` · `gpt-3.5-turbo` | 15 + 35 = **50** | **`gpt-5.6-sol`** (ou `gpt-5.6-terra`) | dernier remplacement du 3.5 |
| **chat — mini** | `gpt-4o-mini` · `gpt-4o-mini.` | 235 + 1 = **236** | **`gpt-5.6-luna`** | taille *mini* (le « Luna » du user) |
| **chat — nano** | `gpt-4.1-nano` | **2** | **`gpt-5.6-luna`** | taille fine → même cible mini |
| **transcribe** | `gpt-4o-transcribe` · `gpt-4o-mini-transcribe` | **28** | **`gpt-transcribe`** | transcription audio (aussi `gpt-live-transcribe`) |
| **tts** | `gpt-4o-mini-tts` · `gpt-4o-mini-tts-2025-03-20` · `gpt-4o-mini-tts-2025-12-15` | 12 + 1 + 1 = **14** | **`gpt-audio-mini`** | synthèse vocale (aussi `gpt-audio-1.5`) |
| **realtime** | `gpt-4o-realtime-preview` | **10** | **`gpt-realtime-2.1`** | conversation temps réel (aussi `gpt-realtime-2.1-mini`) |
| **embeddings** | *(aucun obsolète dans le corpus)* | 0 | `text-embedding-3-small` / `-large` | inchangé |
| **divers (prose)** | `gpt-4o.` | **6** | `gpt-5.6-sol` | occurrences en prose avec ponctuation |

**Sélectivité de la cible *principale*.** Dans la série 5.6, il n'existe **pas** d'identifiant nu `gpt-5.6` : la famille se décline en trois variantes nommées, confirmées par `GET /v1/models` et caractérisées par OpenRouter :

| Variante | Rôle (description OpenRouter) | Prix prompt (OpenRouter) |
|---|---|---|
| **`gpt-5.6-sol`** | **flagship** — raisonnement complexe, codage, workflows agentiques | $0.000002/1M |
| **`gpt-5.6-terra`** | équilibré — entre le flagship et le économique ; codage/raisonnement au quotidien | $0.000002/1M |
| **`gpt-5.6-luna`** | **rapide et économe** — haut volume, tâches sensibles à la latence (chat, classification) | $0.0000002/1M (10× moins cher) |

Le « 5.6 principal » se traduit donc par **`gpt-5.6-sol`** (flagship), et le « Luna mini » par **`gpt-5.6-luna`** (confirmé économique/mini par son prix et sa description). `gpt-5.6-terra` est l'alternative équilibrée si l'on veut un modèle principal moins coûteux en latence.

## Preuve de vérification (firsthand, 2026-09-05)

- **OpenAI `GET /v1/models`** : la série `gpt-5` courante contient `gpt-5.6-sol`, `gpt-5.6-terra`, `gpt-5.6-luna` (et les versions antérieures `gpt-5.5`, `gpt-5.4`, `gpt-5.4-mini/nano`, `gpt-5.2`). La lignée `4.x` (`gpt-4`, `gpt-4o`, `gpt-4.1`, `gpt-4-turbo`, `gpt-3.5-turbo`, `gpt-4o-transcribe`, `gpt-4o-mini-tts`, `gpt-4o-realtime-preview`) est **toujours listée** (compatibilité) mais n'est **plus** la génération courante.
- **OpenRouter `GET /api/v1/models`** : les variantes 5.6 portent des descriptions qui fixent le rôle (flagship `sol` / équilibrée `terra` / économique `luna`) et un prix qui identifie `luna` comme la taille mini (10× moins chère).
- **Familles non-chat confirmées** (OpenAI `/v1/models`) : `gpt-transcribe`, `gpt-live-transcribe` (transcription) ; `gpt-audio-mini`, `gpt-audio-1.5` (synthèse) ; `gpt-realtime-2.1`, `gpt-realtime-2.1-mini` (temps réel) ; `text-embedding-3-small`, `text-embedding-3-large` (embeddings).

## Inventaire (état `main`, 2026-09-05)

| Modèle inscrit | Occurrences |
|---|---:|
| `gpt-4o-mini` | 235 |
| `gpt-4o` | 152 |
| `gpt-4` | 128 |
| `gpt-3.5-turbo` | 35 |
| `gpt-4-turbo` | 33 |
| `gpt-4o-transcribe` | 28 |
| `gpt-3.5` | 15 |
| `gpt-4.1-mini` | 14 |
| `gpt-4o-mini-tts` | 12 |
| `gpt-4o-realtime-preview` | 10 |
| `gpt-4.1` | 10 |
| `gpt-4o.` (prose) | 6 |
| `gpt-4.1-nano` | 2 |
| `gpt-4o-2024-08-06` | 2 |
| `gpt-4o-mini-tts-2025-03-20` | 1 |
| `gpt-4o-mini-tts-2025-12-15` | 1 |
| `gpt-4o-mini.` (prose) | 1 |
| **Total** | **685** |

**Fichiers touchés : 162** — GenAI **96**, SymbolicAI **18**, ML **16**, hors-notebooks (scripts/docs/.github/GradeBookApp) **22**, QuantConnect **5**, Config **2**, GameTheory **2**, Sudoku **1**.

> L'issue #14755, mesurée au commit `cfc6f8e1e`, donnait 124 fichiers / ~657 refs. L'écart (162/685) vient de l'avancée de `main` entre les deux mesures, pas d'une correction de mesure — le périmètre GenAI reste dominant.

## Notes pour les tranches 2-5

- **Snapshots datés** (`gpt-4o-2024-08-06`, `gpt-4o-mini-tts-2025-03-20`, `gpt-4o-mini-tts-2025-12-15`) : ce sont des épingles de date de la même famille — elles suivent la même cible que leur base (`gpt-4o` → `gpt-5.6-sol` ; `gpt-4o-mini-tts` → `gpt-audio-mini`).
- **Config** : `MyIA.AI.Notebooks/GenAI/.env` porte `OPENAI_CHAT_MODEL_ID="gpt-5.2"`. Comme il n'existe pas de `gpt-5.6` nu, la migration config (tranche 5) visera `gpt-5.2` → `gpt-5.6-sol` (ou `gpt-5.6-terra`), à confirmer avec le coordinateur.
- **Conservations délibérées** : les notebooks qui **enseignent explicitement un modèle historique** (comparatif d'époques, exercice sur les limites de GPT-3.5) se conservent tels quels et se **déclarent** dans leur PR de tranche — la substitution n'y est pas mécanique (contrainte de l'issue).
- **Budget provider** : les re-exécutions (tranches 2-4) consomment un budget ; annoncer chaque tranche sur le dashboard avant de lancer (contrainte de l'issue). Trois clés étaient invalides/épuisées au 2026-09-05 (Mistral 402, Qwen 401, OpenRouter ~0,2 %) — vérifier l'état des clés avant chaque tranche.

## Voir aussi

- Issue **#14755** — mandat user + découpage en 5 tranches.
- [genai-services.md](genai-services.md) — architectures Qwen/Lumina et mappings GenAI.
