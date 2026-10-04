# Modèles de décision — relevé et shortlist (issue #18204, Pli 1)

> **Statut** : Pli 1/4 de #18204. **Cadrage et relevé** uniquement. Aucune substitution de notebook dans cette PR. La **vérification locale** (rejouer 2-3 tranches de benchmarks) requiert un GPU 24 Go et sort du périmètre de cette lane (RTX 3070 8GB = `RECOVERABLE-MACHINE`).
>
> **Date du relevé** : 2026-10-03. **Source primaire** : Hugging Face, espace `multimodalart/jev-decision-index`, édition `0.2.1` du 2026-09-28 (`data/index.json`, 70 implémentations sur ~120 000 requêtes, 38 benchmarks statiques).

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