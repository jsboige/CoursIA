# FallacyDetection — détection de sophismes par Qwen FT + PT (EPIC #10355)

Série de notebooks pour la **détection et classification de sophismes** (fallacies) via Qwen 3.5/3.6, en distinguant **fine-tuning** (mémorisation du motif de raisonnement « général → particulier ») et **post-training** (utilisation de ce workflow sur des cas nouveaux). L'interprétabilité de la décision est apportée par des **sparse autoencoders (SAE)** entraînés sur le modèle — c'est le **gate de succès déclaré** de l'EPIC : si < 3 tailles de Qwen 3.5/3.6 disposent d'un SAE, le pivot interprétabilité n'est pas tenu (escalade owner).

- **EPIC parent** : [#10355](https://github.com/jsboige/CoursIA/issues/10355)
- **Phase 1 (sous-issue opérationnelle)** : [#10356](https://github.com/jsboige/CoursIA/issues/10356)
- **Survey SOTA fondateur** : [docs/research/fallacy-detection-survey.md](../../../docs/research/fallacy-detection-survey.md) (livrable 1, 11 sources primaires)

## Notebooks de la série

| # | Notebook | Rôle |
|---|---|---|
| 01 | [01_taxonomy_intro.ipynb](01_taxonomy_intro.ipynb) | Introduction : sophismes formels/informels, taxonomie Argumentum vs taxonomies académiques (≥ 3 exercices) |
| 02 | [02_fallacy_datasets_landscape.ipynb](02_fallacy_datasets_landscape.ipynb) | Paysage des datasets annotés en accès réel (≥ 3 exercices) |
| 03 | [03_taxonomy_coverage_gap.ipynb](03_taxonomy_coverage_gap.ipynb) | Écart de couverture taxonomique académique vs Argumentum (≥ 3 exercices) |
| 04 | [04_coverage_matrix.ipynb](04_coverage_matrix.ipynb) | Matrice de couverture cross-notebooks N×M (sophismes, formalismes, domaines, preuve) + heatmap (≥ 3 exercices) |
| 05 | [05_dataset_builder.ipynb](05_dataset_builder.ipynb) | Phase 2, tranche A : produit cartésien Scénarii × taxonomies, équilibrage par exposant $\alpha$, splits déterministes sans fuite de scénario, prompts sans circularité (3 exercices) |

## Chaîne des phases

| Phase | Livrable | Statut |
|---|---|---|
| 1 — Survey SOTA | [docs/research/fallacy-detection-survey.md](../../../docs/research/fallacy-detection-survey.md) | livré |
| 1 — Extraction Jessynoo | [data/jessynoo_rfallacy_anonymized.csv](data/jessynoo_rfallacy_anonymized.csv) + [scripts/fallacy_detection/extract_jessynoo_fallacy.py](../../../scripts/fallacy_detection/extract_jessynoo_fallacy.py) | livré |
| 1 — Paysage datasets | [02_fallacy_datasets_landscape.ipynb](02_fallacy_datasets_landscape.ipynb) — 7 datasets testés en accès réel | livré |
| 1 — Inventaire SAE Qwen | ≥ 3 tailles (gate de faisabilité) : [_research/qwen_sae_inventory.md](../_research/qwen_sae_inventory.md) — verdict **OK, 3 bases Qwen3.5** couvertes (9B en usage dans le harnais ICT) | livré |
| 2 — Dataset builder | tranche A : [05_dataset_builder.ipynb](05_dataset_builder.ipynb) + [scripts/fallacy_detection/cartesian_dataset_builder.py](../../../scripts/fallacy_detection/cartesian_dataset_builder.py) — couples (scénario, nœud) sur **167 × (1407 + 222)**, splits dans [data/phase2/](data/phase2/) ; tranches B (génération des textes par LLM auto-hébergé) et C (test humain externe) à venir ([#17578](https://github.com/jsboige/CoursIA/issues/17578)) | tranche A livrée |
| 2 — Lot apparié avec/sans sophisme | section 2(b) de la revue EPITA : [paired_scenario_corpus.py](../../../scripts/fallacy_detection/paired_scenario_corpus.py) + lot mesuré 110 bras (55 paires, rôle constant, polarité variable — le raccourci rôle→polarité tombe à 0,500) dans [data/teacher/](data/teacher/) (`paired_scenario_*.{jsonl,json,md}`, empreintes SHA-256 au rapport, rejeu sans clé via `--report-only`) | pilote livré |
| 3 — Fine-tuning (série FT) | mémorisation du motif général→particulier | Phase 3 |
| 4 — Post-training (série PT) | utilisation du workflow | Phase 4 |
| 5 — Analyse SAE (strate 6 ICT) | features « motif » FT vs PT | gate de succès, Phase 5 |

## Corpus `data/jessynoo_rfallacy_anonymized.csv`

Corpus r/fallacy extrait et anonymisé depuis le Data Export Reddit du compte `u/Jessynoo` (le handle Reddit du propriétaire du dépôt — self-attribution pédagogique assumée). **69 items** (67 commentaires + 2 posts), corps de 30 à 4263 caractères (moyenne 702, mesurée sur 68 corps non vides).

### Provenance et politique PII

- **Source** : Data Export Reddit (`.zip`) déposé par l'owner sur GDrive. Le `.zip` brut **n'est jamais committé** (PII par construction — il contient l'historique complet du compte). Le path du dump est personnel et ne se consigne pas dans le repo ; il se passe via la variable d'environnement `JESSYNOO_DUMP_PATH` au moment de l'exécution du script d'extraction.
- **Extraction reproductible** : `scripts/fallacy_detection/extract_jessynoo_fallacy.py` (stdlib only). Lit le `.zip`, filtre `subreddit == "fallacy"`, anonymise, écrit le CSV.
- **Anonymisation** : chaque mention `u/<tiers>` dans les corps est remplacée par un token stable `u/[USER_N]` (indexation déterministe par tri du nom). 5 usernames tiers cités ont été anonymisés. Les mentions `r/...` (subreddits publics) et les URLs de référence (Wikipedia, RationalWiki) sont conservées — ce sont des contenus publics, pas des PII.
- **Colonnes PII supprimées** : `ip` (PII par nature, même si vide dans le sous-ensemble), `permalink`/`link` (l'URL Reddit est réversible vers l'original et déferait l'anonymatisation `u/` des tiers cités dans le corps). Schéma retenu : `id` (opaque, base36, non réversible sans l'API Reddit), `date`, `subreddit`, `kind` (comment/post), `title`, `url`, `body`.

### Constat important pour les phases aval

Le corpus Jessynoo r/fallacy est en **anglais** (0 mot-clé français sur 69 items), mais ce corpus n'est **pas** un jeu d'entraînement — c'est un **bootstrap de câblage** du pipeline (extraction reproductible, anonymisation PII, format CSV stable). Il a toujours eu cette vocation, et le README l'annonçait sans la nommer. Le jeu d'entraînement viendra de la Phase 2.

La **taxonomie Argumentum** (sous-module `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentum`, fichier `Cards/Fallacies/Argumentum Fallacies - Taxonomy.csv`) est **déjà traduite en 8 langues** : `fr` (4 colonnes), `en` (6), `ru` (7), `ar` (7), `fa` (7), `zh` (7), `es` (7), `pt` (7). Mesure firsthand sur `origin/main` du sous-module :

```bash
head -1 "Cards/Fallacies/Argumentum Fallacies - Taxonomy.csv" | tr ',' '\n' \
  | grep -oE '_(fr|en|ru|ar|fa|zh|es|pt)$' | sort | uniq -c
#   7 _zh   7 _ru   7 _pt   7 _fa   7 _es   7 _ar   6 _en   4 _fr
```

Huit groupes de colonnes : `text_<lang>`, `desc_<lang>`, `example_<lang>`, `link_<lang>`, `Family_<lang>`, etc. Un corpus anglophone s'étiquette donc **directement** avec les colonnes `_en` ; un corpus russe avec `_ru`, etc. Le « décalage de langue étiquettes-vs-corpus » ne se pose plus : la Phase 2 choisit la langue source du corpus, et la taxonomie fournit l'étiquetage correspondant.

### Stratégie de données pour la Phase 2

Deux voies complémentaires, pas exclusives :

1. **Corpus académiques annotés réellement obtenables** — déjà mesurés en Phase 1 dans [02_fallacy_datasets_landscape.ipynb](02_fallacy_datasets_landscape.ipynb) (Logic 13 + MAFALDA L2 23 = 27 classes après déduplication de 9 doublons). Le paysage montre un écart de **plus d'un ordre de grandeur** avec la taxonomie Argumentum : couverture ~3 % des feuilles et ~2 % des nœuds (mesuré dans [03_taxonomy_coverage_gap.ipynb](03_taxonomy_coverage_gap.ipynb)). C'est utile mais structurellement limité : aucune académie n'a produit 1407 fine-grained fallacies étiquetées.

2. **Corpus synthétique par produit cartésien Scénarii × taxonomies** — Argumentum fournit aussi `Cards/Scenarii/Argumentum Scenarii - Cards.csv` (167 scénarii en 7 catégories, copie verbatim dans [data/argumentum_scenarii_cards.csv](data/argumentum_scenarii_cards.csv), licence dans [data/NOTICE-SCENARII](data/NOTICE-SCENARII)). Le produit cartésien avec les deux taxonomies hors racine, `167 × (1407 sophismes + 222 vertus) = 272 043` couples (scénario, nœud), fournit, par construction, **un couple étiqueté par construction pour chaque nœud** — une consigne, pas une annotation validée (état des trois briques ci-dessous) — et les vertus donnent au classifieur la classe « argument sain » sans laquelle il ne verrait que des sophismes. La génération du label est triviale (c'est le second facteur du couple) ; la production du `body` est le travail de la Phase 2 — typiquement via un LLM conditionné à l'étiquette (template par sophisme, paraphrase, validation humaine sur un échantillon). Cette voie est **la seule** qui porte la couverture uniforme de la taxonomie qu'aucun corpus naturel ne donne, et c'est ce qui justifie l'échelle des phases 3-5.

Les deux voies sont complémentaires : le corpus académique **porte le protocole d'évaluation** (OOS sur données humaines) et le corpus synthétique **porte l'échelle** (Phase 3 fine-tuning sur la couverture complète de la taxonomie). Le résultat mesuré à ce jour sur ce protocole est négatif (fine-tuning pilote, [#25419](https://github.com/jsboige/CoursIA/issues/25419)) — il est spécifique au protocole évalué et ne préjuge ni des variantes à venir ni des phases 3-5.

État vérifié des trois briques (les liens suivent le travail déjà fait, sans le rouvrir) :

| Brique | État vérifié | Suivi |
|---|---|---|
| Couples (scénario, nœud) des splits [`data/phase2/`](data/phase2/) | reproductibles à graine fixée (paramètres par défaut) — rejeu hors ligne byte-identique, empreintes SHA-256 épinglées au [manifeste](data/phase2/manifest.json) | tranche A livrée |
| Textes des couples — génération par LLM auto-hébergé, puis annotation | aucun texte généré ni annotation validée dans le dépôt à ce jour | [#17578](https://github.com/jsboige/CoursIA/issues/17578) (génération, tranche B) · [#20222](https://github.com/jsboige/CoursIA/issues/20222) (validation humaine) |
| Résultats d'évaluation (fine-tuning, OOS sur corpus académique) | protocole défini ; résultat du pilote négatif, propre au protocole évalué | [#25419](https://github.com/jsboige/CoursIA/issues/25419) |

### Format des splits de la Phase 2 (`data/phase2/`)

Produits par [05_dataset_builder.ipynb](05_dataset_builder.ipynb) ou par la CLI ci-dessous, avec les paramètres par défaut ($\alpha = 0{,}5$, budgets 12 000 sophismes + 2 000 vertus, graine 0). Le rejeu lit uniquement les **copies versionnées** des sources (taxonomies et scénarii sous `data/`, pas le sous-module vivant) et tourne **hors ligne** ; l'option `--out` est obligatoire et désigne un dossier jetable :

```bash
python scripts/fallacy_detection/cartesian_dataset_builder.py --out /tmp/fd_replay
```

Vérification des empreintes contre le manifeste committé — les trois SHA-256 doivent correspondre (rejeu mesuré byte-identique ; `train.csv`, non committé, n'est épinglé que par son empreinte au manifeste) :

```bash
python - /tmp/fd_replay <<'PY'
import json, hashlib, pathlib, sys
replay = pathlib.Path(sys.argv[1])
man = json.load(open("MyIA.AI.Notebooks/GenAI/FallacyDetection/data/phase2/manifest.json", encoding="utf-8"))
for name, meta in man["files"].items():
    digest = hashlib.sha256((replay / name).read_bytes()).hexdigest()
    print(f"{name}: {'OK' if digest == meta['sha256'] else 'DIFF'}")
PY
```

(Le chemin du dossier de rejeu se passe en argument — même forme que `--out` — pour rester juste sur les deux familles de shells.)

Une ligne par couple, en UTF-8 et fins de ligne LF :

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

Les textes ne sont pas dans les splits : ils se relisent dans les trois sources au moment du rendu du prompt, ce qui garde les CSV petits et fait porter toute la traçabilité par les SHA1 de blob épinglés dans `manifest.json`. `val.csv` (un couple par nœud) et `test.csv` (deux par nœud) sont committés ; `train.csv` se régénère à l'identique et n'est épinglé que par son SHA-256 dans le manifeste. Les trois splits utilisent des scénarii disjoints (117 / 25 / 25).

### Lot apparié avec/sans sophisme (`data/teacher/`)

Pilote de la **section 2(b) de la revue EPITA** : à scénario et locuteur constants, seul le statut de sophisme varie entre les deux bras d'une paire. C'est le lot qui interdit le raccourci de surface « rôle → polarité » : les deux bras d'une paire partagent le rôle du locuteur, donc un modèle qui n'apprendrait que le rôle ne peut pas deviner la polarité. Produit par [paired_scenario_corpus.py](../../../scripts/fallacy_detection/paired_scenario_corpus.py) — génération par teacher LLM avec contrôle croisé, le reste en stdlib.

| Fichier | Contenu |
|---|---|
| [paired_scenario_corpus.jsonl](data/teacher/paired_scenario_corpus.jsonl) | le lot : 110 bras = 55 paires acceptées, une ligne par bras |
| [paired_scenario_report.json](data/teacher/paired_scenario_report.json) | rapport du run : empreintes SHA-256, paramètres, verdicts, mesure du raccourci |
| [paired_scenario_report.md](data/teacher/paired_scenario_report.md) | rendu lisible du rapport |

Paramètres du run publiés (graine 42, 60 paires tentées, 5 distracteurs par bras, 2 essais max par paire, températures génération 0,8 / contrôle 0,0, teacher `qwen3.6-35b-a3b`) : **55 paires acceptées** (taux 0,917), 5 rejets au dernier essai — 4 reclassements du bras négatif vers une autre famille, 1 vertu non reclassée — dont 3 acceptations via le contrôle croisé du bras counterpart. La propriété visée est **mesurée dans le rapport**, pas seulement affirmée : `role_is_constant_within_pair: true` et `best_role_only_accuracy` = 0,5000 exactement (rôle `smoothTalker`, 55 bras avec / 55 sans sophisme).

Empreintes épinglées dans le rapport : source `val_fr.jsonl` = `d7621fffa05dc857…`, corpus produit = `112f68e26b42217b…`. **Rejeu sans clé ni réseau** : `python scripts/fallacy_detection/paired_scenario_corpus.py --report-only` reconstruit le corpus depuis le rapport publié — vérifié **byte-identique** le 2026-11-19 (l'empreinte `112f68e26b42217b` se reproduit exact). Note de vérification : ces empreintes se mesurent sur le **blob Git** (fins de ligne LF) ; un checkout de travail sous `autocrlf` CRLF fait dériver le sha256 du fichier sur disque alors que le contenu committé, lui, n'a pas changé.
