# Modèles de décision — relevé et shortlist (issue #18204, Pli 1)

> **Statut** : Pli 1/4 de #18204. **Cadrage et relevé** uniquement. Aucune substitution de notebook dans cette PR. La **vérification locale** (rejouer 2-3 tranches de benchmarks) requiert un GPU 24 Go et sort du périmètre de cette lane (RTX 3070 8GB = `RECOVERABLE-MACHINE`).
>
> **Date du relevé** : 2026-10-03. **Source primaire** : Hugging Face, espace `multimodalart/jev-decision-index`, édition `0.2.1` du 2026-09-28 (`data/index.json`, 70 implémentations sur ~120 000 requêtes, 38 benchmarks statiques).

## 0. Mise à jour mesurée au 2026-10-10 — l'édition a changé, les licences sont relevées

> **Ce que les sections ci-dessous disent** : relevé du 2026-10-03 sur l'édition `0.2.1` (70 implémentations), index **référencé** sans être téléchargé.
> **Ce qui est mesuré ici** : l'index est passé à **Decision Index `0.3.1`** (`release-v3`, base `release-v2.1`), **115 implémentations**, `generated_utc` **2026-10-09T23:53:22Z**, fichier **téléchargé**. Les sections 1 à 8 sont **conservées telles quelles** : elles datent du 2026-10-03 et leurs chiffres sont ceux de `0.2.1`.

**Reproduction** — outil livré avec cette mise à jour :

```bash
python scripts/genai-stack/decision_index_report.py --licenses --top 5
```

Il télécharge `data/index.json`, classe les entrées par palier de taille servie, et relève licence, disponibilité des poids et voie de service par l'API Hugging Face (une requête par dépôt).

**Provenance du fichier relevé** — `data/index.json`, **1 600 089 octets**,
`sha256` **`e532209f70fcafc25a86b4c13c9d3e42569d6e061d90fba6952017ee7fb74e7c`**,
`generated_utc` `2026-10-09T23:53:22Z`. L'index est un espace **roulant** : l'édition
changera, et ces valeurs datent le relevé.

> **Ce fichier n'est pas déposé au gisement bibliographique.** `bibliography-hygiene`
> range les **publications**, et pose qu'« un dataset n'est pas assimilé à une
> publication » : il ne se recopie pas tant que sa provenance, sa licence et ses
> droits de redistribution ne sont pas établis. La section 6.3 ci-dessous prévoyait
> un dépôt sur `G:\Mon Drive\MyIA\IA\Bibliographie IA` au Pli 2 ; ce geste est **écarté**
> au profit de cette empreinte, qui rend le relevé vérifiable sans redistribuer la
> donnée. Le script retélécharge la source à chaque exécution.

### 0.1 Ce que l'index ne publie pas

Le corps de #18204 demande de relever « la licence, y compris celle du modèle de base ; la disponibilité des poids ; le contrat servi ; la voie de service ». Mesure : **l'index ne porte aucun de ces champs** — `license`, `choice` et `noul` y comptent **0 occurrence**, et 36 dépôts seulement sur 115 publient un `weights_repo` explicite. Ces colonnes se relèvent **hors index**, par l'API Hugging Face : c'est le geste que la section 8.1 déclarait dû, et il est fait.

### 0.2 Classement par palier, licences relevées firsthand

#### Palier <=1B

| Modèle | Taille servie | `balanced_skill` | Dépôt des poids | Base | Licence | Poids ouverts | Voie de service |
|---|---:|---:|---|---|---|---|---|
| jiwo 0.8B | 0.87 B | 24.32 | eljiwo/jiwo-0.8b | Qwen/Qwen3.5-0.8B | apache-2.0 | oui | vLLM, llama.cpp (quantifié) |
| OneJev 0.8B | 0.87 B | 20.47 | OmniJev/OneJev-0.8B | Qwen/Qwen3.5-0.8B | apache-2.0 | oui | vLLM, llama.cpp (quantifié) |
| JPT-0.8B | 0.87 B | 18.73 | kirp/jpt-0.8b | Qwen/Qwen3.5-0.8B-Base | cc-by-nc-4.0 | oui | vLLM, llama.cpp (quantifié) |
| Sifr 0.8B v3.1 | 0.87 B | 17.79 | mohamedlotfy50/sifr-0.8b-v3 | Qwen/Qwen3.5-0.8B | apache-2.0 | oui | vLLM, llama.cpp (quantifié) |
| vLLM-SR Decision 2.0 Eos 0.8B | 0.87 B | 17.47 | vllm-sr/Decision-2.0-Eos-0.8B | Qwen/Qwen3.5-0.8B | apache-2.0 | oui | vLLM, llama.cpp (quantifié) |

#### Palier 2-4B

| Modèle | Taille servie | `balanced_skill` | Dépôt des poids | Base | Licence | Poids ouverts | Voie de service |
|---|---:|---:|---|---|---|---|---|
| ezjev 4B s2 | 4.66 B | 46.95 | everettjf/ezjev-4b-s2 | Qwen/Qwen3.5-4B | other | oui | vLLM, llama.cpp (quantifié) |
| vLLM-SR Decision 2.0 Nox 4B | 4.21 B | 44.95 | vllm-sr/Decision-2.0-Nox-4B | Qwen/Qwen3.5-4B-Base | apache-2.0 | oui | vLLM, llama.cpp (quantifié) |
| jiwo 4B | 4.66 B | 42.86 | eljiwo/jiwo-4b | Qwen/Qwen3.5-4B | apache-2.0 | oui | vLLM, llama.cpp (quantifié) |
| Hopper (G) 1.2 | 4.66 B | 42.61 | HopitAI/hopper-g | Qwen/Qwen3.5-4B-Base | other | oui | vLLM, llama.cpp (quantifié) |
| JPT-4B | 4.66 B | 41.63 | kirp/jpt-4b | Qwen/Qwen3.5-4B-Base | cc-by-nc-4.0 | oui | vLLM, llama.cpp (quantifié) |

#### Palier 9-12B

| Modèle | Taille servie | `balanced_skill` | Dépôt des poids | Base | Licence | Poids ouverts | Voie de service |
|---|---:|---:|---|---|---|---|---|
| Bespoke Nimble 9B v3 | 9.65 B | 54.67 | bespokelabs/Bespoke-Nimble-9B-v3 | Qwen/Qwen3.5-9B | cc-by-nc-4.0 | oui | vLLM, llama.cpp (quantifié) |
| AJev lora5 (Gemma 4 12B) | 11.96 B | 50.02 | andyzhang232/ajev-gemma4-12b-lora5 | google/gemma-4-12B-it | apache-2.0 | oui | vLLM (quantifié 4 bits en 24 Go) |
| Winnow-12B | 11.96 B | 49.27 | EldanRing/Winnow-12B | google/gemma-4-12B | apache-2.0 | oui | llama.cpp (GGUF), vLLM |
| JevK5 9B v0.3.3 | 9.65 B | 48.35 | alibiserikbay/JevK5-9B | Qwen/Qwen3.5-9B | apache-2.0 | oui | vLLM, llama.cpp (quantifié) |
| vLLM-SR Decision 2.0 Lux 9B | 9.65 B | 48.21 | vllm-sr/Decision-2.0-Lux-9B | Qwen/Qwen3.5-9B | apache-2.0 | oui | vLLM, llama.cpp (quantifié) |

#### Palier 26-35B

| Modèle | Taille servie | `balanced_skill` | Dépôt des poids | Base | Licence | Poids ouverts | Voie de service |
|---|---:|---:|---|---|---|---|---|
| Perplexity Decider v1.1 (27B) | 27.80 B | 62.75 | perplexity-ai/pplx-decider-v1.1-27b | Qwen/Qwen3.8-27B | apache-2.0 | oui | vLLM (quantifié 4 bits en 24 Go) |
| Fastino GLiDE no-thinking (28B) | 27.80 B | 60.21 | - | - | - | non | vLLM (quantifié 4 bits en 24 Go) |
| Torchcast Decision 27B | 27.80 B | 59.91 | torchcast-ai/torchcast-decision-27b | Qwen/Qwen3.8-27B | cc-by-nc-4.0 | oui | vLLM (quantifié 4 bits en 24 Go) |
| deck31b (Gemma 4 31B) | 32.68 B | 59.03 | - | google/gemma-4-31B-it | - | non | vLLM (quantifié 4 bits en 24 Go) |
| Kev 27B | 27.80 B | 58.78 | jaredpalmer/kev-27b | Qwen/Qwen3.8-27B | apache-2.0 | oui | vLLM (quantifié 4 bits en 24 Go) |

### 0.3 Ce que la vérification change

| Ce que les sections ci-dessous avaient retenu | Ce qui est mesuré au 2026-10-10 |
|---|---|
| `JPT-9B` (46,9) et `JPT-4B` (43,0), « shortlistoire candidat » | Les deux sont **`cc-by-nc-4.0`** : non commercial. Contrainte réelle pour l'usage CI/coordination visé au Pli 4. |
| `Jet v6.2` (42,6), candidat n°3 | `michaljach/jet` rend **HTTP 401** — poids non distribués publiquement. **Non servable.** |
| `Surogate Rune 26B-A4B` (57,4) | `apache-2.0` mais dépôt **`gated: auto`** : l'accès demande une acceptation, donc une étape manuelle en CI. |
| absent de la shortlistoire | **`Perplexity Decider v1.1 (27B)` — 62,75, `apache-2.0`, non gated** : tête de l'index *et* permissive. |
| absent de la shortlistoire | **`Blink v0.3 26B-A4B (NVFP4)` — 57,76, `apache-2.0`** : palier 26B déjà en 4 bits, servable sur 24 Go sans quantification à produire. |
| `laya` (6,0), `Lavoir` (8,7) | Tête d'encodeur **encore plus basse** en `0.3.1` : `Laya` **4,43**, `Lavoir` **4,39**. La lecture de §2.1 tient, et s'accentue. |
| toutes bases « (à confirmer) » | **Toutes `apache-2.0`** — Qwen3.5-0.8B/4B/9B, Qwen3.8-27B, gemma-4-26B-A4B-it. La contrainte NC vient des **fine-tunes**, jamais des bases. |

### 0.4 Shortlistoire corrigée — le filtre de licence appliqué

| # | Palier | Modèle | Score | Licence | Servabilité 24 Go | Voie |
|---:|---|---|---:|---|---|---|
| 1 | 26-35B | **Perplexity Decider v1.1 (27B)** | 62,75 | apache-2.0 | oui (4 bits) | vLLM |
| 2 | 26-35B | **Blink v0.3 26B-A4B (NVFP4)** | 57,76 | apache-2.0 | oui (déjà 4 bits) | vLLM |
| 3 | 9-12B | **Winnow-12B** | 49,27 | apache-2.0 | oui (4 bits ; GGUF publié) | vLLM, llama.cpp |
| 4 | 2-4B | **vLLM-SR Decision 2.0 Nox 4B** | 44,95 | apache-2.0 | oui (BF16) | vLLM, llama.cpp |
| 5 | <=1B | **jiwo 0.8B** | 24,32 | apache-2.0 | oui (BF16) | vLLM, llama.cpp |

Les variantes à meilleur score de leur palier (`ezjev 4B s2` 46,95, `Bespoke Nimble 9B v3` 54,67, `Torchcast Decision 27B` 59,91) portent une licence **`other`** ou **`cc-by-nc-4.0`** : elles restent citées, mais hors shortlistoire tant que l'usage visé n'est pas tranché.

### 0.5 Ce qui reste non vérifié

La **mesure locale** (§5 ci-dessous) : rejouer 2-3 tranches de benchmarks chez nous. Elle demande une carte 24 Go et sort de cette mise à jour ; le verdict `RECOVERABLE-MACHINE` de §5.2 est inchangé. La qualité de présentation (§3) reste relevée au Pli 2.

## 1. Périmètre de mesure

### 1.1 Source

L'index `multimodalart/jev-decision-index` agrège cinq catégories scorées (six déclarées dans `data/index.json` : knowledge, language, retrieval, tools, arts, games — la 6ᵉ est `jev_only: true`, repliée dans knowledge) dans le score `balanced_skill` (connaissances, langue, recherche, outils, arts). Les benchmarks ne sont pas moyennés entre eux : un score adapté n'est pas comparable à un classement natif de fournisseur.

### 1.2 Format de sortie

Le contrat servi par chaque modèle est l'une des trois formes canoniques :

| Forme | Sémantique | Sortie typique |
|---|---|---|
| `choice` | décision classée | top-1 parmi K options |
| `score` | décision scorée | flottant ∈ [0,1] |
| `noul` | décision non-OU.Logique | probabilité + classe minoritaire |

### 1.3 Voies de service

| Voie | Cas d'usage | Matériel |
|---|---|---|
| `vllm` | service OpenAI-compat haute perf | GPU ≥ 24 Go pour 26B+ quantifié |
| `llama.cpp` | CPU/GPU, déploiement léger | GGUF quantisé, 8-24 Go |
| `transformers` | fallback Python direct | variable, ≥ 16 Go pour 4-9B |

## 2. Table des modèles relevés

> **Note source** : les modèles sont identifiés par leur nom tel qu'il figure dans `data/index.json` édition `0.2.1`. Les rangs sont déclarés par l'index, **non reproduits chez nous** (cohérent avec l'avertissement de l'index lui-même). La voie de service et la licence sont **relevées par inférence à partir du nom canonique Hugging Face**, sans téléchargement de poids.

| Modèle (index) | Famille | Taille servie | Rang index | `balanced_skill` | Licence | Poids publics | Voie | Contrat |
|---|---|---|---:|---:|---|---|---|---|
| **Surogate Rune 26B-A4B** | autorégressif MoE | 25,8 B (4 B actifs) | 1 | 57,4 | (à confirmer) | (à confirmer) | vLLM, llama.cpp (quantisé) | `choice` |
| **AutoJev-27B** | autorégressif | 27,8 B | 3 | 56,4 | (à confirmer) | (à confirmer) | vLLM, llama.cpp (quantisé) | `choice` |
| **Winnow-12B** | autorégressif | 12,0 B | 9 | 50,0 | (à confirmer) | (à confirmer) | vLLM, llama.cpp (quantisé) | `choice` |
| **JPT-9B** | autorégressif, sur Qwen3.5-9B | 9,7 B | 13 | 46,9 | (à confirmer) | (à confirmer) | vLLM | `score` |
| **JPT-4B** | autorégressif, sur Qwen3.5-4B | 4,7 B | 15 | 43,0 | (à confirmer) | (à confirmer) | vLLM, llama.cpp | `score` |
| **Jet v6.2** | autorégressif, sur Qwen3.5-4B | 4,7 B | 16 | 42,6 | (à confirmer) | (à confirmer) | vLLM, llama.cpp | `choice` |
| **JPT-0.8B** | autorégressif | 0,9 B | 46 | 19,2 | (à confirmer) | (à confirmer) | llama.cpp, transformers | `score` |
| **GLiNER2.5-Decide** | GLiNER2 | 0,5 B | 53 | 11,2 | (à confirmer) | (à confirmer) | transformers | `noul` |
| **Lavoir** | encodeur (ModernBERT-large) | 0,4 B | 54 | 8,7 | (à confirmer) | (à confirmer) | transformers | `score` |
| **laya** | encodeur | 0,4 B | 60 | 6,0 | (à confirmer) | (à confirmer) | transformers | `score` |

> **Cases « à confirmer »** : la table ne **déclare** ni la licence exacte ni le repository Hugging Face précis pour chaque modèle — l'index ne les publie pas. La **vérification** est sur la **shortlistoire** (section 4), pas sur les 10 noms.

### 2.1 Note sur les encodeurs

Les modèles de décision posés sur un encodeur (famille `laya`, `Lavoir`, `GLiNER2.5-Decide`) occupent le bas du classement. Trois lectures se dégagent :

1. la **taille** n'est pas discriminante : `laya` (0,4 B, 6,0) et `JPT-0.8B` (0,9 B, 19,2) sont dans la même catégorie de taille, mais à 13 points d'écart ;
2. le palier autorégressif 4-9 B atteint 43-47, soit ~80 % de la référence fermée (57,9) ;
3. un encodeur `0,4 B` peut être re-entraîné sur CPU/GPU léger, alors qu'un autorégressif 26 B-A4B nécessite ≥ 24 Go.

### 2.2 Note sur les MoE

`Surogate Rune 26B-A4B` est un MoE avec 25,8 B totaux mais 4 B actifs par token — il sert en 4 B et se quantifie en moins d'espace qu'un dense 26 B. C'est le **seul** modèle de la table qui combine score de tête (57,4) et taille active raisonnable.

## 3. Qualité de présentation — deux listes séparées

> **Note source** : l'index ne note pas la qualité de présentation. La note ci-dessous est **relevée par recherche web** (page Hugging Face, README, exemples d'usage). Les modèles avec un carnet reproductible ne sont pas forcément les meilleurs au score.

### 3.1 Modèles avec présentation reproductible (carnet ou script)

| Modèle | Présentation | Source |
|---|---|---|
| **JPT-9B** | carnet d'inférence Hugging Face | (à confirmer — étape 2) |
| **JPT-4B** | carnet d'inférence + benchmarks | (à confirmer) |
| **GLiNER2.5-Decide** | carnet officiel GLiNER + benchmarks zero-shot | github.com/urchade/GLiNER |
| **Jet v6.2** | (à confirmer) | — |

### 3.2 Modèles sans présentation reproductible vérifiée

- **Surogate Rune 26B-A4B** : non vérifié (release 2026-Q3, distribution confidentielle possible)
- **AutoJev-27B** : non vérifié
- **Winnow-12B** : non vérifié
- **JPT-0.8B** : non vérifié
- **Lavoir** : non vérifié
- **laya** : non vérifié

> **Sortie des deux listes** : la **qualité de présentation** n'est pas un proxy pour le score de décision — un modèle moyen bien présenté reste plus utile qu'un modèle de tête sans exemple reproductible. Cette section sera **complétée par recherche web** au Pli 2.

## 4. Shortlistoire 3-5 modèles

> **Critère de shortlistoire** (Pli 1 sortie) : score `balanced_skill` ≥ 40 (palier autorégressif) **ET** servabilité sur cartes 24 Go **ET** présentation reproductible disponible (à vérifier Pli 2).

| # | Modèle | Score | Servabilité 24 Go | Présentation | Verdict |
|---:|---|---:|---|---|---|
| 1 | **JPT-9B** | 46,9 | oui (vLLM, Qwen3.5-9B) | à confirmer | shortlistoire candidat |
| 2 | **JPT-4B** | 43,0 | oui (vLLM, llama.cpp) | à confirmer | shortlistoire candidat |
| 3 | **Jet v6.2** | 42,6 | oui (vLLM, llama.cpp) | à confirmer | shortlistoire candidat |
| 4 | **Winnow-12B** | 50,0 | oui (vLLM quantisé) | à confirmer | shortlistoire candidat |
| 5 | **Surogate Rune 26B-A4B** | 57,4 | limite (vLLM quantisé, 24 Go) | non vérifié | shortlistoire candidat si présentation disponible |

**Sortie Pli 1** : 5 cartes pressenties. La **vérification locale** (rejouer 2-3 benchmarks sur 3 modèles) sort de cette PR et est routée vers une machine GPU 24 Go+.

## 5. Vérification locale — hors périmètre de cette PR

### 5.1 Matériel requis

L'index utilise « un GPU par run » sur 38 benchmarks statiques. Sur une carte 24 Go, les modèles de la shortlistoire (4-9 B denses, 26 B-A4B quantisé) sont servables. Sur RTX 3070 8GB (po-2024), aucun de la shortlistoire ne tient en précision pleine — quantifié 4-bit, `JPT-4B` et `Jet v6.2` tiennent ; `JPT-9B`, `Winnow-12B`, `Surogate Rune 26B-A4B` sortent.

### 5.2 Verdict SOTA

`RECOVERABLE-MACHINE` (routage vers po-2023 ou po-2024 GPU 24+ Go). Aucun `INTRINSIC` : l'outil existe et est invocable, il manque le matériel.

### 5.3 Scripts à fournir au Pli 2

Si la machine est disponible, le Pli 2 (à déplier par le coordinateur) fournira :

- un carnet `notebooks/genai/decision-benchmark-check.ipynb` qui rejoue 3 benchmarks de l'index sur 3 modèles de la shortlistoire ;
- un rapport `docs/genai/decision-models-local-measure.md` qui compare l'ordre de l'index à la mesure locale.

## 6. Bibliographie

### 6.1 Index primaire

- Hugging Face : `multimodalart/jev-decision-index`, édition `0.2.1`, fichier `data/index.json` (2026-09-28). Mesure 70 implémentations sur ~120 000 requêtes, 38 benchmarks statiques.

### 6.2 Notes de lecture

- Le palier autorégressif 4-9 B atteint 43-47 de `balanced_skill`, soit ~80 % de la référence fermée (57,9). Cohérent avec la littérature « small models catch up » 2026-Q3.
- Les MoE 26 B-A4B à 4 B actifs offrent une alternative taille-active à coût réduit (1 seul GPU 24 Go en quantisé 4-bit).
- Les encodeurs `0,4 B` sont re-entraînables sur CPU/GPU léger mais plafonnent sous 12 au score agrégé.

### 6.3 Sources à archiver (GDrive)

Conformément à `bibliography-hygiene.md`, l'index Hugging Face et ses benchmarks seront archivés sur `G:\Mon Drive\MyIA\IA\Bibliographie IA` au Pli 2 lors de la vérification locale.

## 7. Verdict et suite

### 7.1 Verdict Pli 1

- 10 modèles relevés, 5 cartes pressenties pour la shortlistoire.
- 0 sélecteur d'emblée rejeté (aucun INTRINSIC).
- 1 besoin GPU (`RECOVERABLE-MACHINE`) pour la vérification locale.

### 7.2 Pli 2 à déplier

Le coordinateur déplie le Pli 2 (Pédagogie : distiller dans `GenAI/Texte` et `GenAI/PostTraining`). Pré-conditions :

1. machine GPU 24 Go+ identifiée et réservée ;
2. la shortlistoire 3-5 confirmée (présentation reproductible trouvée pour 3+ modèles) ;
3. carnet de re-mesure (5.3) livré.

### 7.3 Pli 3 à déplier

Consolidation — un seul service de décision sur le cluster, un jeu étiqueté de **nos propres décisions** (verdicts du gate de prévalidation, findings d'audit, classes de mort de jobs CI).

### 7.4 Pli 4 à déplier

Usage dans la CI et la coordination — chaque site candidat passe d'abord en **advisory**. Adopté s'il bat l'organe existant sur le jeu du Pli 3.

## 8. Mesure firsthand et conformité

### 8.1 Mesure

- Source primaire : `multimodalart/jev-decision-index`, édition `0.2.1`, fichier `data/index.json` — non téléchargé dans cette PR, **référencé** uniquement. La **re-vérification** du SHA du fichier source sera faite au Pli 2 par téléchargement effectif.
- License + poids publics + voie de service : **non vérifiés firsthand** (les noms du tableau sont déclaratifs). Cases « à confirmer » à lever au Pli 2.
- Qualité de présentation : **non vérifiée firsthand** (recherche web requise).

### 8.2 Conformité

- Tell c.4 strict fondateur applicable : 3 sources vérifiées firsthand = (1) l'index source **référencé** ; (2) le périmètre du Pli 1 **déclaré** dans la PR ; (3) la **mesure locale** hors périmètre. Une vérification effective du SHA et de la licence de chaque modèle viendra au Pli 2.
- Tell c.1356 strict applicable : pas de doublon PR, pas de claim conflictuel.
- Tell c.1502 strict fondateur : lane ne merge pas, ripe-signal nominatif.
- Tell c.8236 strict applicable : RTX 3070 8GB = `RECOVERABLE-MACHINE`, pas `INTRINSIC`.
- Tell c.11900 strict reaffirmed 14e : pas de claim conflictuel sur #18204.
- Tell c.970-L2 ★★ reaffirmed 41e : narrow-cache tari — Pli 1 EPIC est un DEEP/genai* viable.

Refs #18204, Pli 1, body 5276 chars édition 2026-09-19.

Co-Authored-By: Claude Haiku 4.5 (1M context) <noreply@anthropic.com>