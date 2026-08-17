# FallacyDetection — détection de sophismes par Qwen FT + PT (EPIC #10355)

Série de notebooks pour la **détection et classification de sophismes** (fallacies) via Qwen 3.5/3.6, en distinguant **fine-tuning** (mémorisation du motif de raisonnement « général → particulier ») et **post-training** (utilisation de ce workflow sur des cas nouveaux). L'interprétabilité de la décision est apportée par des **sparse autoencoders (SAE)** entraînés sur le modèle — c'est le **gate de succès déclaré** de l'EPIC : si < 3 tailles de Qwen 3.5/3.6 disposent d'un SAE, le pivot interprétabilité n'est pas tenu (escalade owner).

- **EPIC parent** : [#10355](https://github.com/jsboige/CoursIA/issues/10355)
- **Phase 1 (sous-issue opérationnelle)** : [#10356](https://github.com/jsboige/CoursIA/issues/10356)
- **Survey SOTA fondateur** : [docs/research/fallacy-detection-survey.md](../../docs/research/fallacy-detection-survey.md) (livrable 1, 10 sources primaires)

## Chaîne des phases

| Phase | Livrable | Statut |
|---|---|---|
| 1 — Survey SOTA | [docs/research/fallacy-detection-survey.md](../../docs/research/fallacy-detection-survey.md) | livré |
| 1 — Extraction Jessynoo | [data/jessynoo_rfallacy_anonymized.csv](data/jessynoo_rfallacy_anonymized.csv) + [scripts/fallacy_detection/extract_jessynoo_fallacy.py](../../scripts/fallacy_detection/extract_jessynoo_fallacy.py) | livré (bootstrap de câblage — voir § Corpus) |
| 1 — Paysage datasets | ≥ 5 datasets testés en accès réel | à livrer (cible Phase 2 — corpus académiques annotés) |
| 1 — Inventaire SAE Qwen | ≥ 3 tailles (gate de faisabilité) | à livrer |
| 2 — Dataset builder | produit cartésien **Scénarii × Fallacy** (167 × 1408) + corpus académiques annotés | Phase 2 |
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

### Constat important pour les phases aval (révision 2026-08-17, cf #11451)

**Le « décalage de langue étiquettes-vs-corpus » présenté ci-dessous comme un *obstacle* de la Phase 2 n'existe pas.** La taxonomie Argumentum est déjà **multilingue** : le CSV [`Argumentum Fallacies - Taxonomy.csv`](../../SymbolicAI/Argument_Analysis/Argumentum/Cards/Fallacies/Argumentum%20Fallacies%20-%20Taxonomy.csv) porte huit groupes de colonnes — `text_*` + `desc_*` + `example_*` + `link_*` (avec `Family_*` + `Subfamily_*` + `Subsubfamily_*` quand pertinent) — suffixés `_fr`, `_en`, `_ru`, `_ar`, `_fa`, `_zh`, `_es`, `_pt`. Mesure firsthand (`head -1 ... | tr ',' '\n' | grep -oE '_(fr|en|ru|ar|fa|zh|es|pt)$' | sort | uniq -c`) :

```
   4 _fr    6 _en    7 _ru    7 _ar    7 _fa    7 _zh    7 _es    7 _pt
```

Un corpus anglophone s'étiquette directement avec les colonnes `_en` ; un corpus espagnol avec les `_es` ; etc. Aucune traduction supplémentaire n'est nécessaire pour exploiter le multilingue.

**Le corpus Jessynoo n'est pas un dataset d'entraînement** : 69 items (67 commentaires + 2 posts) en anglais, c'est trop peu pour entraîner, et il n'a jamais eu cette vocation. Son rôle est de **câbler l'extracteur** (anonymisation PII, format de sortie, intégration Phase 1 — voir `scripts/fallacy_detection/extract_jessynoo_fallacy.py`). Pour l'entraînement, deux voies se complètent :

1. **Corpus académiques annotés** — déjà mesurés par `02_fallacy_datasets_landscape.ipynb` (cible Phase 1 — Paysage datasets à livrer) ;
2. **Corpus synthétique par produit cartésien Scénarii × Fallacy** — `167 × 1408` exemples étiquetés *par construction*, couverture uniforme de la taxonomie qu'aucun corpus naturel ne donne. C'est cette seconde voie qui porte l'échelle nécessaire aux Phases 3-5.

Ancienne rédaction (avant #11451) :

> Le corpus Jessynoo r/fallacy est en **anglais** (0 mot-clé français sur 69 items). La taxonomie Argumentum (grilles d'étiquettes) est en **français** (1408 sophismes / 8 familles). La Phase 2 (dataset builder) devra traiter ce **décalage de langue étiquettes-vs-corpus** (traduction des étiquettes, ou corpus multilingue, ou restriction initiale au sous-ensemble Argumentum couvert par les datasets académiques anglophones — cf survey §5.1).

— class="affirmation propagée sans confrontation à la source" (#11450 sœur sur le README racine). Le CSV est à trois commandes de distance ; la mesure y est directe.
