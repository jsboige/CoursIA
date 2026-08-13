# FallacyDetection — détection de sophismes par Qwen FT + PT (EPIC #10355)

Série de notebooks pour la **détection et classification de sophismes** (fallacies) via Qwen 3.5/3.6, en distinguant **fine-tuning** (mémorisation du motif de raisonnement « général → particulier ») et **post-training** (utilisation de ce workflow sur des cas nouveaux). L'interprétabilité de la décision est apportée par des **sparse autoencoders (SAE)** entraînés sur le modèle — c'est le **gate de succès déclaré** de l'EPIC : si < 3 tailles de Qwen 3.5/3.6 disposent d'un SAE, le pivot interprétabilité n'est pas tenu (escalade owner).

- **EPIC parent** : [#10355](https://github.com/jsboige/CoursIA/issues/10355)
- **Phase 1 (sous-issue opérationnelle)** : [#10356](https://github.com/jsboige/CoursIA/issues/10356)
- **Survey SOTA fondateur** : [docs/research/fallacy-detection-survey.md](../../docs/research/fallacy-detection-survey.md) (livrable 1, 10 sources primaires)

## Chaîne des phases

| Phase | Livrable | Statut |
|---|---|---|
| 1 — Survey SOTA | [docs/research/fallacy-detection-survey.md](../../docs/research/fallacy-detection-survey.md) | livré |
| 1 — Extraction Jessynoo | [data/jessynoo_rfallacy_anonymized.csv](data/jessynoo_rfallacy_anonymized.csv) + [scripts/fallacy_detection/extract_jessynoo_fallacy.py](../../scripts/fallacy_detection/extract_jessynoo_fallacy.py) | livré |
| 1 — Paysage datasets | ≥ 5 datasets testés en accès réel | à livrer |
| 1 — Inventaire SAE Qwen | ≥ 3 tailles (gate de faisabilité) | à livrer |
| 2 — Dataset builder | projection de la taxonomie Argumentum | Phase 2 |
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

Le corpus Jessynoo r/fallacy est en **anglais** (0 mot-clé français sur 69 items). La taxonomie Argumentum (grilles d'étiquettes) est en **français** (1408 sophismes / 8 familles). La Phase 2 (dataset builder) devra traiter ce **décalage de langue étiquettes-vs-corpus** (traduction des étiquettes, ou corpus multilingue, ou restriction initiale au sous-ensemble Argumentum couvert par les datasets académiques anglophones — cf survey §5.1).
