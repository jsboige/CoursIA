# FallacyDetection — détection de sophismes par Qwen FT + PT (EPIC #10355)

Série de notebooks pour la **détection et classification de sophismes** (fallacies) via Qwen 3.5/3.6, en distinguant **fine-tuning** (mémorisation du motif de raisonnement « général → particulier ») et **post-training** (utilisation de ce workflow sur des cas nouveaux). L'interprétabilité de la décision est apportée par des **sparse autoencoders (SAE)** entraînés sur le modèle — c'est le **gate de succès déclaré** de l'EPIC : si < 3 tailles de Qwen 3.5/3.6 disposent d'un SAE, le pivot interprétabilité n'est pas tenu (escalade owner).

- **EPIC parent** : [#10355](https://github.com/jsboige/CoursIA/issues/10355)
- **Phase 1 (sous-issue opérationnelle)** : [#10356](https://github.com/jsboige/CoursIA/issues/10356)
- **Survey SOTA fondateur** : [docs/research/fallacy-detection-survey.md](../../../docs/research/fallacy-detection-survey.md) (livrable 1, 10 sources primaires)

## Notebooks de la série

| # | Notebook | Rôle |
|---|---|---|
| 01 | [01_taxonomy_intro.ipynb](01_taxonomy_intro.ipynb) | Introduction : sophismes formels/informels, taxonomie Argumentum vs taxonomies académiques (≥ 3 exercices) |
| 02 | [02_fallacy_datasets_landscape.ipynb](02_fallacy_datasets_landscape.ipynb) | Paysage des datasets annotés en accès réel (≥ 3 exercices) |
| 03 | [03_taxonomy_coverage_gap.ipynb](03_taxonomy_coverage_gap.ipynb) | Écart de couverture taxonomique académique vs Argumentum (≥ 3 exercices) |
| 04 | [04_coverage_matrix.ipynb](04_coverage_matrix.ipynb) | Matrice de couverture cross-notebooks N×M (sophismes, formalismes, domaines, preuve) + heatmap (≥ 3 exercices) |
| 05 | [05_dataset_builder.ipynb](05_dataset_builder.ipynb) | Phase 2, tranche A : produit cartésien Scénarii × taxonomies, équilibrage par exposant $lpha$, splits déterministes sans fuite de scénario, prompts sans circularité (3 exercices) |

## Chaîne des phases

| Phase | Livrable | Statut |
|---|---|---|
| 1 — Survey SOTA | [docs/research/fallacy-detection-survey.md](../../../docs/research/fallacy-detection-survey.md) | livré |
| 1 — Extraction Jessynoo | [data/jessynoo_rfallacy_anonymized.csv](data/jessynoo_rfallacy_anonymized.csv) + [scripts/fallacy_detection/extract_jessynoo_fallacy.py](../../../scripts/fallacy_detection/extract_jessynoo_fallacy.py) | livré |
| 1 — Paysage datasets | [02_fallacy_datasets_landscape.ipynb](02_fallacy_datasets_landscape.ipynb) — 7 datasets testés en accès réel | livré |
| 1 — Inventaire SAE Qwen | ≥ 3 tailles (gate de faisabilité) | à livrer |
| 2 — Dataset builder | tranche A : [05_dataset_builder.ipynb](05_dataset_builder.ipynb) + [scripts/fallacy_detection/cartesian_dataset_builder.py](../../../scripts/fallacy_detection/cartesian_dataset_builder.py) — couples (scénario, nœud) sur **167 × (1407 + 222)**, splits dans [data/phase2/](data/phase2/) ; tranches B (génération des textes par LLM auto-hébergé) et C (test humain externe) à venir ([#17578](https://github.com/jsboige/CoursIA/issues/17578)) | tranche A livrée |
| 3 — Fine-tuning (série FT) | mémorisation du motif général→particulier | Phase 3 |
| 4 — Post-training (série PT) | utilisation du workflow | Phase 4 |
| 5 — Analyse SAE (strate 6 ICT) | features « motif » FT vs PT | gate de succès, Phase 5 |

## Corpus `data/jessynoo_rfallacy_anonymized.csv`

Corpus r/fallacy extrait et anonymisé depuis le Data Export Reddit du compte `u/Jessynoo` (le handle Reddit du propriétaire du dépôt — self-attribution pédagogique assumée). **69 items** (67 commentaires + 2 posts), corps de 30 à 4263 caractères (moyenne 691).

### Provenance et politique PII

- **Source** : Data Export Reddit (`.zip`) déposé par l'owner sur GDrive. Le `.zip` brut **n'est jamais committé** (PII par construction — il contient l'historique complet du compte). Le path du dump est personnel et ne se consigne pas dans le repo ; il se passe via la variable d'environnement `JESSYNOO_DUMP_PATH` au moment de l'exécution du script d'extraction.
- **Extraction reproductible** : `scripts/fallacy_detection/extract_jessynoo_fallacy.py` (stdlib only). Lit le `.zip`, filtre `subreddit == "fallacy"`, anonymise, écrit le CSV.
- **Anonymisation** : chaque mention `u/<tiers>` dans les corps est remplacée par un token stable `u/[USER_N]` (indexation déterministe par tri du nom). 5 usernames tiers cités ont été anonymisés. Les mentions `r/...` (subreddits publics) et les URLs de référence (Wikipedia, RationalWiki) sont conservées — ce sont des contenus publics, pas des PII.
- **Colonnes PII supprimées** : `ip` (PII par nature, même si vide dans le sous-ensemble), `permalink`/`link` (l'URL Reddit est réversible vers l'original et déferait l'anonymatisation `u/` des tiers cités dans le corps). Schéma retenu : `id` (opaque, base36, non réversible sans l'API Reddit), `date`, `subreddit`, `kind` (comment/post), `title`, `url`, `body`.

### Constat important pour les phases aval

Le corpus Jessynoo r/fallacy est en **anglais** (0 mot-clé français sur 69 items), mais ce corpus n'est **pas** un jeu d'entraînement — c'est un **bootstrap de câblage** du pipeline (extraction reproductible, anonymisation PII, format CSV stable). Il a toujours eu cette vocation, et le README l'annonçait sans la nommer. Le jeu d'entraînement viendra de la Phase 2.

La **taxonomie Argumentum** (sous-module `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentum`, fichier `Cards/Fallacies/Argumentum Fallacies - Taxonomy.csv`) est **déjà traduite en 8 langues** : `fr` (4 colonnes), `en` (6), `ru` (7), `ar` (7), `fa` (7), `zh` (7), `es` (7), `pt` (7). Mesure firsthand sur `origin/main` du sous-module :

```bash
head -1 "Cards/Fallacies/Argumentum Fallacies - Taxonomy.csv" | tr ',' '\n' \
  | grep -oE '_(fr|en|ru|ar|fa|zh|es|pt)$' | sort | uniq -c
#   7 _zh   7 _ru   7 _pt   7 _fa   7 _es   7 _ar   6 _en   4 _fr
```

Huit groupes de colonnes : `text_<lang>`, `desc_<lang>`, `example_<lang>`, `link_<lang>`, `Family_<lang>`, etc. Un corpus anglophone s'étiquette donc **directement** avec les colonnes `_en` ; un corpus russe avec `_ru`, etc. Le « décalage de langue étiquettes-vs-corpus » ne se pose plus : la Phase 2 choisit la langue source du corpus, et la taxonomie fournit l'étiquetage correspondant.

### Stratégie de données pour la Phase 2

Deux voies complémentaires, pas exclusives :

1. **Corpus académiques annotés réellement obtenables** — déjà mesurés en Phase 1 dans [02_fallacy_datasets_landscape.ipynb](02_fallacy_datasets_landscape.ipynb) (Logic 13 + MAFALDA L2 23 = 27 classes après déduplication de 9 doublons). Le paysage montre un écart de **plus d'un ordre de grandeur** avec la taxonomie Argumentum : couverture ~3 % des feuilles et ~2 % des nœuds (mesuré dans [03_taxonomy_coverage_gap.ipynb](03_taxonomy_coverage_gap.ipynb)). C'est utile mais structurellement limité : aucune académie n'a produit 1407 fine-grained fallacies étiquetées.

2. **Corpus synthétique par produit cartésien Scénarii × taxonomies** — Argumentum fournit aussi `Cards/Scenarii/Argumentum Scenarii - Cards.csv` (167 scénarii en 7 catégories, copie verbatim dans [data/argumentum_scenarii_cards.csv](data/argumentum_scenarii_cards.csv), licence dans [data/NOTICE-SCENARII](data/NOTICE-SCENARII)). Le produit cartésien avec les deux taxonomies hors racine, `167 × (1407 sophismes + 222 vertus) = 272 043` couples (scénario, nœud), fournit, par construction, **un exemple annoté pour chaque nœud**, et les vertus donnent au classifieur la classe « argument sain » sans laquelle il ne verrait que des sophismes. La génération du label est triviale (c'est le second facteur du couple) ; la production du `body` est le travail de la Phase 2 — typiquement via un LLM conditionné à l'étiquette (template par sophisme, paraphrase, validation humaine sur un échantillon). Cette voie est **la seule** qui porte la couverture uniforme de la taxonomie qu'aucun corpus naturel ne donne, et c'est ce qui justifie l'échelle des phases 3-5.

Les deux voies sont complémentaires : le corpus académique **valide** que les features apprises par fine-tuning discrimininent vraiment (évaluation OOS sur données humaines), et le corpus synthétique **porte l'échelle** (Phase 3 fine-tuning sur la couverture complète de la taxonomie).

### Format des splits de la Phase 2 (`data/phase2/`)

Produits par [05_dataset_builder.ipynb](05_dataset_builder.ipynb) (ou `python scripts/fallacy_detection/cartesian_dataset_builder.py`) avec les paramètres par défaut ($lpha = 0{,}5$, budgets 12 000 sophismes + 2 000 vertus, graine 0). Une ligne par couple, en UTF-8 et fins de ligne LF :

| Colonne | Contenu |
|---|---|
| `pair_id` | `<split>-F<pk>-<scenario_path>` pour un sophisme, `V<pk>` pour une vertu (ex. `test-F798-2.2.8`), unique |
| `split` | `train`, `val` ou `test` |
| `polarity` | `fallacy` ou `virtue` |
| `node_pk` | clé du nœud dans sa taxonomie |
| `family` | famille de premier niveau du nœud (7 par taxonomie) |
| `depth` | profondeur du nœud (1 = famille) |
| `is_leaf` | 1 si le nœud n'a pas d'enfant |
| `scenario_path` | chemin décimal du scénario (`catégorie.sous-catégorie.rang`) |

Les textes ne sont pas dans les splits : ils se relisent dans les trois sources au moment du rendu du prompt, ce qui garde les CSV petits et fait porter toute la traçabilité par les SHA1 de blob épinglés dans `manifest.json`. `val.csv` (1 629 lignes, un couple par nœud) et `test.csv` (3 258 lignes, deux par nœud) sont committés ; `train.csv` (14 000 lignes) se régénère à l'identique et n'est épinglé que par son SHA-256 dans le manifeste. Les trois splits utilisent des scénarii disjoints (117 / 25 / 25).
