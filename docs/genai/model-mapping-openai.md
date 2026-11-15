> REFERENCE — vivante — dernière révision 2026-11-13

# Mapping des modèles OpenAI — génération courante (tranche 1, #14755)

> **Grain : DEEP/genai — lane `myia-po-2023:CoursIA-2` — tranche 1 de #14755.**
> Date de vérification API : **2026-09-05**. **Aucune substitution de modèle dans cette tranche** — l'inventaire et la table ci-dessous précèdent les tranches 2-5 (substitution + re-exécution).

## Politique d'exécution du chat

La consigne du mainteneur du 26 octobre 2026, suivie dans **#22783**, s'applique aux appels de chat, pas au nettoyage de toutes les chaînes de caractères. **Aucune exécution ne doit cibler un modèle de chat obsolète.** La cible par défaut est **Swift via notre service vLLM**, avec le même contrat d'API que le client OpenAI.

### Classer avant de modifier

| Classe | Critère | Traitement |
|---|---|---|
| **EXECUTION** | Identifiant envoyé à un appel de chat, ou configuration réellement consommée par cet appel, même derrière un wrapper | Migrer la cible puis réexécuter complètement le carnet ; les sorties réelles nomment le modèle utilisé. |
| **DOCUMENTATION** | Citation historique, tableau pédagogique ou exemple non appelé | Conserver si utile, en indiquant explicitement l'obsolescence et la cible recommandée. Une recommandation de nouvel appel ne doit pas proposer le modèle obsolète. |
| **SPECIFIQUE** | Modèle de synthèse vocale, transcription ou embeddings | Hors de cette migration de chat : ne pas changer sa cible par analogie de préfixe. |

Le dossier ne décide pas de la classe : `Audio/04-Applications/04-5-LiveCoding-LLM-Music.ipynb` appelle `chat.completions.create` pour produire du code musical ; ce n'est pas un appel TTS. Inversement, `gpt-4o-mini-tts` ne devient pas un modèle de chat parce que son nom commence par `gpt-4o`. Lire la configuration **et son consommateur** ; un nom seulement imprimé ou une sonde de catalogue `/models` ne prouve pas une exécution de chat. Pour un wrapper, vérifier l'organe source au commit épinglé avant de conclure depuis ses commentaires.

### Route, alias et repli

- Sur **le siège ai-01**, le service local expose `http://127.0.0.1:5002/v1`. Sur une autre machine, cette adresse désignerait la machine appelante : utiliser la route distante documentée, pas un `localhost` copié.
- La façade OpenAI-compatible documentée est `https://models.myia.io/v1` ; le microbenchmark [10b — mécanique d'inférence](../../MyIA.AI.Notebooks/GenAI/Texte/10b_Inference_Mechanics.ipynb) montre également la route LAN du siège sur le port 5002. Vérifier la disponibilité avant l'exécution ; cette documentation n'est pas une sonde live.
- L'identifiant servi documenté est `qwen3.6-35b-a3b`. Il s'agit d'un **alias**, pas d'une preuve du poids physique. La [référence du cluster](../reference/cluster-agents.md) documente Swift derrière cet alias et la vérification par la configuration du serveur. Ne pas inventer un identifiant API à partir du nom commercial Swift et ne pas prétendre qu'un `/models` révèle les poids chargés.
- Si la cible locale est injoignable, choisir le modèle de chat courant du mapping pour le rôle demandé, **vérifier son identifiant et son accès**, et annoncer explicitement la raison du repli ainsi que l'endpoint et le modèle effectivement utilisés, sans afficher de clé. La table datée ci-dessous n'est pas une preuve de disponibilité actuelle.
- Si ni la cible locale ni le repli vérifié ne sont utilisables, réparer la cause ou signaler le blocage ; ne pas substituer des réponses fabriquées ou un ancien modèle en silence.

Changer le modèle ou l'endpoint exige une réexécution complète du carnet et la vérification de ses interprétations, conformément à C.2 et à la règle de préservation des sorties. On ne renomme jamais une sortie ancienne pour la faire passer pour une exécution Swift. Les familles spécialisées et les mesures historiques ci-dessous restent conservées comme état daté ; leurs anciennes recommandations ne remplacent pas cette politique de chat.

## Objet

#14755 demande de remplacer les références datées (`gpt-4o-mini` 2024, `gpt-3.5-turbo`, …) par la génération courante, plutôt que de continuer à ré-exécuter sur des modèles qui n'ont plus de sens. La cible nommée par le user : **« OpenAI 5.6 »** pour le modèle principal, **« Luna »** pour la taille *mini*.

Le mandat insiste : **« les identifiants exacts d'API sont à vérifier firsthand contre le fournisseur — ne pas déduire un nom d'API d'un nom commercial. »** Ce document est le produit de cette vérification : c'est la table de correspondance `ancien -> nouveau`, par famille d'usage, adossée à la réponse des endpoints.

## Table de correspondance (vérifiée contre l'API)

| Famille d'usage | Ancien modèle (obsolète) | Occurrences | Nouveau modèle (vérifié) | Rôle |
|---|---|---|---|---|
| **chat — principal** | `gpt-4` · `gpt-4-turbo` · `gpt-4o` · `gpt-4o-2024-08-06` · `gpt-4.1` | 128 + 33 + 152 + 2 + 10 = **325** | **`gpt-5.6-sol`** | flagship de la série 5.6 |
| **chat — héritage** | `gpt-3.5` · `gpt-3.5-turbo` | 15 + 35 = **50** | **`gpt-5.6-sol`** (ou `gpt-5.6-terra`) | dernier remplacement du 3.5 |
| **chat — mini** | `gpt-4o-mini` · `gpt-4o-mini.` · `gpt-4.1-mini` | 235 + 1 + 14 = **250** | **`gpt-5.6-luna`** | taille *mini* (le « Luna » du user) |
| **chat — nano** | `gpt-4.1-nano` | **2** | **`gpt-5.6-luna`** | taille fine → même cible mini |
| **transcribe** | `gpt-4o-transcribe` · `gpt-4o-mini-transcribe` | **28** | **`gpt-transcribe`** | transcription audio (aussi `gpt-live-transcribe`) |
| **tts** | `gpt-4o-mini-tts` · `gpt-4o-mini-tts-2025-03-20` · `gpt-4o-mini-tts-2025-12-15` | 12 + 1 + 1 = **14** | **`gpt-audio-mini`** | synthèse vocale (aussi `gpt-audio-1.5`) |
| **realtime** | `gpt-4o-realtime-preview` | **10** | **`gpt-realtime-2.1`** | conversation temps réel (aussi `gpt-realtime-2.1-mini`) |
| **embeddings** | *(aucun obsolète dans le corpus)* | 0 | `text-embedding-3-small` / `-large` | inchangé |
| **divers (prose)** | `gpt-4o.` | **6** | `gpt-5.6-sol` | occurrences en prose avec ponctuation |

**Sélectivité de la cible *principale*.** Dans la série 5.6, il n'existe **pas** d'identifiant nu `gpt-5.6` : la famille se décline en trois variantes nommées, confirmées par `GET /v1/models` et caractérisées par OpenRouter :

| Variante | Rôle (description OpenRouter) | Prix prompt (OpenRouter, $/1M tokens) |
|---|---|---|
| **`gpt-5.6-sol`** | **flagship** — raisonnement complexe, codage, workflows agentiques | $2.00 |
| **`gpt-5.6-terra`** | équilibré — entre le flagship et le économique ; codage/raisonnement au quotidien | $2.00 |
| **`gpt-5.6-luna`** | **rapide et économe** — haut volume, tâches sensibles à la latence (chat, classification) | $0.20 (10× moins cher) |

> **Unité** : le champ brut `pricing.prompt` d'OpenRouter est exprimé en **dollars par token** (`0.000002`) ; la colonne ci-dessus est convertie en **$ / 1M tokens** (× 10⁶ → `$2.00` / `$0.20`), l'unité de tout budget de re-exécution établi depuis cette table.

Le « 5.6 principal » se traduit donc par **`gpt-5.6-sol`** (flagship), et le « Luna mini » par **`gpt-5.6-luna`** (confirmé économique/mini par son prix et sa description). `gpt-5.6-terra` est l'alternative équilibrée si l'on veut un modèle principal moins coûteux en latence.

## Preuve de vérification (firsthand, 2026-09-05)

- **OpenAI `GET /v1/models`** : la série `gpt-5` courante contient `gpt-5.6-sol`, `gpt-5.6-terra`, `gpt-5.6-luna` (et les versions antérieures `gpt-5.5`, `gpt-5.4`, `gpt-5.4-mini/nano`, `gpt-5.2`). La lignée `4.x` (`gpt-4`, `gpt-4o`, `gpt-4.1`, `gpt-4-turbo`, `gpt-3.5-turbo`, `gpt-4o-transcribe`, `gpt-4o-mini-tts`, `gpt-4o-realtime-preview`) est **toujours listée** (compatibilité) mais n'est **plus** la génération courante.
- **OpenRouter `GET /api/v1/models`** : les variantes 5.6 portent des descriptions qui fixent le rôle (flagship `sol` / équilibrée `terra` / économique `luna`) et un prix qui identifie `luna` comme la taille mini (10× moins chère).
- **`gpt-4.1-mini` vérifié firsthand (2026-09-06, ré-run API live)** : `openai/gpt-4.1-mini` est listé — description « *mid-sized model delivering performance competitive with GPT-4o at substantially lower latency and cost* », prix prompt **$0.40/1M**, positionné entre `gpt-4.1-nano` ($0.10/1M, « *fastest and cheapest* ») et `gpt-4.1` ($2.00/1M, flagship). Dans la série 5.6, `luna` ($0.20/1M) est la **seule** strate sous le prix flagship (sol/terra = $2.00) et sa description (« *high-volume, latency-sensitive tasks such as chat* ») est celle de la taille mini — la cible `gpt-4.1-mini → gpt-5.6-luna` est donc établie par rôle **et** par positionnement de prix, cohérente avec `gpt-4o-mini` et `gpt-4.1-nano`.
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

## Conservations délibérées — inventaire (état main, 2026-11-13)

Le périmètre **exécuté** de la migration est **complet au sens de l'organe** : l'organe `scripts/notebook_tools/check_obsolete_chat_model.py`, passé sur l'arbre suivi (hors `.tmp/`), ne signale **aucun appel de chat live** ciblant un modèle obsolète — le seul `finding` d'exécution est dans `_archive/` (gelé, non live). Le résidu (citations résiduelles classées DOCUMENTATION par l'organe) est constitué de **conservations délibérées** : chaque nom ancien cité ci-dessous est volontaire, pas un défaut en attente de migration. C'est la liste que l'issue #14755 demande (« les conservations délibérées sont listées avec leur raison »).

> **Borne de la mesure.** « Complet » signifie **complet au sens de l'organe** : carnets + **formes d'appel reconnues** par `classify_chat_call` — les six formes SDK (`chat.completions.create`, `chat.completions.parse`, `responses.create`, `ChatCompletion.create`, `ChatOpenAI`, `dspy.LM`) **et** la forme HTTP brut ajoutée par #25072 (2026-11-08/09) : `requests.post` / `httpx.post` / `urllib.request.urlopen` dont l'URL cible `*/chat/completions`. Un appel chat live passant par une **forme hors de cette liste** n'est pas vu par l'organe — la classe A compte **trois pilotes, par deux formes wrappers** (`ChatCompletionAgent` / `ProviderConfig`), qui n'y figurent pas. La mesure ne dit donc pas « aucun appel chat live ne cible un modèle obsolète » ; elle dit « aucune forme reconnue ne le fait ».
>
> **Portée du garde en CI.** Le câblage `fast_lane_registry.py` (TRANCHE 30) borne le garde à `iterate_paths=["**.ipynb"]` et le déclare **advisory** (`blocking=False`) ; les fichiers `.py` du dépôt ne sont donc jamais ouverts par le garde, et le « 0 » ci-dessus provient d'une **exécution manuelle** de l'organe, pas du garde.

> Chemins : les carnets sont relatifs à `MyIA.AI.Notebooks/` ; les scripts, à la racine du dépôt.

| Classe | Raison | Fichiers |
|---|---|---|
| **A. Expérience épinglée** | `MODEL_ID = "gpt-4o-mini"` est la **variable de contrôle** du pilote d'évaluation (docstring « modèle EPINGLE … aucune sonde ne bascule ») : changer le modèle changerait l'expérience, ce n'est pas un défaut. **Trois de ces pilotes font un appel chat live** que l'organe ne voit pas (forme hors liste blanche) : `sk_agents_handoff_pilot.py` (`CountingOpenAI` → `ChatCompletionAgent`), `adk_distillation_pilot.py` (`ProviderConfig` → sonde) et `adk_handoff_pilot.py` (`ProviderConfig`, `model="gpt-4o-mini"` l.181, déplacé par #25008 vers `ML/DataScienceWithAgents/07-Agent-Orchestration/eval-pilots/`) — l'épinglage y est **délibéré et documenté**, c'est ce qui justifie la conservation | `GenAI/SemanticKernel/eval-pilots/` (**la plupart** des fichiers `.py` ; `sk_process_pilot.py` ne porte pas le littéral) · `ML/DataScienceWithAgents/07-Agent-Orchestration/eval-pilots/adk_handoff_pilot.py` |
| **B. Panneau de vetting** | **jeu de comparaison délibéré** de modèles à vérifier (`gpt-4o`, `gpt-4o-mini`, `gpt-3.5-turbo`, `o3`, `o4-mini`, `gpt-4`) : retirer des noms réduirait la couverture du panneau. **Les fichiers cités sont hors dépôt** : `semantic-fleet` est un **gitlink** (mode `160000`, sha `6e642aeb`) — les chemins cités sont inatteignables depuis ce dépôt (404 mesurés). Ils ne sont vus par l'organe que si le sous-module est **check out** : mesurés au sha épinglé `6e642aeb`, ils donnent les mêmes mentions de documentation, sans finding d'exécution. Le checkout CI n'initialisant pas les sous-modules, la CI ne les voit pas | `GenAI/SemanticKernel/semantic-fleet/` (hors dépôt) : `model_tester/api_utils.py`, `model_tester/transparent_model_test.py`, `tools/verification/vetting/multi_connector_vetting_test_fixed.py`, `tools/verification/vetting/run_vetting_tests.py` |
| **C. Catalogue / routing** | documentation du **paysage de modèles** (catalogue + table d'état des endpoints, dict modèle→route), pas « le modèle utilisé » | `GenAI/00-GenAI-Environment/00-3-API-Endpoints-Configuration.ipynb` · `GenAI/Security/Oversight/oversight_llm_cachegen.py` |
| **D. Recherche comparative** | les noms anciens sont **le sujet** de l'étude (scaling laws, comparaison de tailles) | `GenAI/Security/Oversight/Oversight-Scaling-Laws-Nim.ipynb` |
| **E. Pédagogie / exemple d'atelier** | matériel d'enseignement citant un modèle historique **à titre d'exemple** (contrainte de l'issue : se conserve et se déclare) | `GenAI/Audio/04-Applications/04-Audiobook/04-13-Audiobook-FishAudio-S2Pro.ipynb` · `GenAI/Vibe-Coding/Roo-Code/Corrections/corriges-ateliers-roo/ateliers-avances/03-generation-dc/generation_dc.py` |
| **F. Documentation (advisory)** | mention documentaire ; le modèle réel est résolu par `os.getenv` (classe H) | `SymbolicAI/ArgumentAnalysis/Argumentation-08b-Executor-Python.ipynb` |
| **G. Fixture de test** | chaîne de modèle **arbitraire** servant de fixture (le test porte sur la logique de parsing, pas sur le modèle) : la changer serait du churn sans valeur | `SymbolicAI/ArgumentAnalysis/tests/test_argumentation_state.py` · `scripts/secrets/tests/test_render_settings_json.py` |
| **H. Classifieur / config par env** | classifieur de **familles** de modèles, ou valeur résolue par `.env` | `scripts/audit/extract_claims_vs_outputs.py` · `SymbolicAI/ArgumentAnalysis/argumentation_lib/budget_variance_study.py` |

**Lecture de la mesure.** Les sites `unresolved` de l'organe sont de même nature : l'argument `model` y est une **variable résolue au point d'appel** (env, config, catalogue) — aucun ne porte un littéral obsolète. Ils sortent du périmètre de substitution par construction. `llm_client.py` (ex-classe H) et `retouche_image.py` (ex-classe E) ne figurent plus à cette tête : #25995 les a **migrés**. Une **exécution manuelle** de l'organe classe **`llm_client.py` non résolu** (résolution dynamique, plus de littéral obsolète en source) ; **`retouche_image.py` ne sort dans aucun seau** — ni finding, ni site non résolu.

**Ce qui reste ouvert pour #14755** : le **périmètre config (tranche 5)** — `.env` → `gpt-5.6-sol` (cf. note ci-dessus, à confirmer avec le coordinateur) — et la **réexécution** des carnets dont la source a migré (C.2), à router vers une machine où le MCP Jupyter est vivant (RECOVERABLE-MACHINE ; mort sur po-2028 depuis le 02/11).

## Voir aussi

- Issue **#14755** — mandat user + découpage en 5 tranches.
- [genai-services.md](genai-services.md) — architectures Qwen/Lumina et mappings GenAI.
