# HumorDetection — détection et typologie de l'humour par annotation multi-annotateurs (#20301)

Série sœur de [FallacyDetection](../FallacyDetection/README.md) : là où FallacyDetection construit un corpus de sophismes, HumorDetection construit un **corpus d'humour annoté** — et le typant, pas seulement en binaire. La série construit l'organe ; la strate ICT (famille ICT-35) le consomme ensuite, même schéma que FallacyDetection → `scripts/fallacy_detection/` → phases 3-5.

- **Issue parent** : [#20301](https://github.com/jsboige/CoursIA/issues/20301)
- **Étape 1 (livrée)** : comparatif des datasets publics d'humour, licences vérifiées à la source, recommandation ColBERT Humor — [commentaire du 11/10](https://github.com/jsboige/CoursIA/issues/20301#issuecomment-6103567187)
- **Note de conception acceptée** ([c.6109425309](https://github.com/jsboige/CoursIA/issues/20301#issuecomment-6109425309)) et **décisions du coordinateur** : nom `HumorDetection` ; kappa plancher 0,6 en *signal* (passe de désambiguïsation documentée, jamais de rejet) ; annotateur B d'une autre famille que Qwen, via claudish, nommé et versionné au rapport ; échantillon borné + manifeste.

## Porte de succès déclarée

Le protocole d'annotation multi-annotateurs produit un corpus dont **l'accord inter-annotateurs** (kappa de Cohen et accord brut, global et par forme) et le **taux de reclassage aller-retour** sont **mesurés et committés**, par forme (pun / sociale / topical) et global.

## Notebooks de la série

| # | Notebook | Rôle | Statut |
|---|---|---|---|
| 01 | [01_humor_intro.ipynb](01_humor_intro.ipynb) | Terrain : détection binaire contre typologie mécanique ; le problème ColBERT posé sur exemples étiquetés ; exercices (binaire vs forme, compter les formes, choisir le pilote) | livré |
| 02 | `02_humor_datasets_landscape.ipynb` | Paysage en accès réel : ColBERT Humor retenu, HAHA 2021 en évaluation externe, Jester en source d'intensité ; re-vérification des licences au geste ; écart EN/FR chiffré | à venir |
| 03 | `03_typology_articulation.ipynb` | Les deux couches typologiques : table de correspondance feuille Argumentum → forme dominante, axe polarité croisé | à venir |
| 04 | `04_controlled_corpus_pairs.ipynb` | Corpus contrôlé et paires minimales du banc 18c — lecture de l'API `humor_pairs` actuelle, bascule vers `humour_banc.organ` à la livraison T7' ([#20316](https://github.com/jsboige/CoursIA/issues/20316)) | à venir |
| 05 | `05_multiannotator_protocol.ipynb` | Le protocole : deux annotateurs LLM de familles distinctes, accord mesuré, reclassage aller-retour à majorité | à venir |
| 06 | `06_teacher_dataset_builder.ipynb` | Tranche A cartésienne (Scénarii × taxonomie humour, équilibrage α, splits étanches, manifeste SHA) puis tranche B enseignant | à venir |

## Chaîne des phases

| Phase | Livrable | Statut |
|---|---|---|
| Étape 1 — Comparatif datasets | commentaire #20301 (7 candidats, licences vérifiées à la source) | livrée |
| Étape 2 — Note de conception | c.6109425309 + 4 décisions coordinateur | livrée |
| Étape 2 — Série : README + carnet 01 | ce dépôt | livrée |
| Étape 2 — Carnets 02-03 | paysage + articulation typologique | à venir |
| Étape 2 — Carnets 04-06 + `scripts/humor_detection/` | corpus contrôlé, protocole, builder | à venir |
| Étape 3 — Consommation ICT-35 | la strate ICT consomme l'organe | gate sur l'étape 2 |

## Données

- **ColBERT Humor** (200 000 textes courts EN, granularité binaire, **contrôles non-humoristiques intégrés**) : licence MIT vérifiée à la source à l'étape 1 — **re-vérifiée au geste de téléchargement**, et la publication (Moradnejad et al.) est **archivée au gisement bibliographique avant tout téléchargement**, chemin cité au manifeste ([bibliography-hygiene](../../../.claude/rules/bibliography-hygiene.md)).
- **Aucun corpus au dépôt** avant ces préconditions. Ensuite : échantillon borné + manifeste (SHA, provenance, licence, date, compteurs) ; corpus complet hors dépôt (règle 512 Ko).
- Le volet **FR** vient du protocole enseignant (scénarii Argumentum FR), pas d'un dataset externe ; l'écart EN/FR est chiffré au carnet 02.
