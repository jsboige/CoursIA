# CSV de synchro traduction — série CaseStudies

**Statut** : Phase 2 rollout (Epic #4957 / #1650). Série CaseStudies couverte par l'infrastructure i18n.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`casestudies.csv`](casestudies.csv) | `CaseStudies/` | 6 (3 études de cas × variantes solution/student : Diagnostic-Medical, Oncology-Planning, SmartGrid-Energy) | 146 (21 colonnes) |

**Note owner-lane** : l'extraction i18n est **safe owner-lane** (artefacts dérivés = CSV de cellules upstream, pas de modification de code des notebooks).

**Note cross-variant** : chaque étude de cas existe en deux variantes (`solution/` corrigée + `student/` stub exercice). Le script d'extraction prend **les deux variantes** verbatim (chaque notebook est une cellule source indépendante). La traduction future T3 (moteur Argumentum) appliquera les deux variantes.

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/CaseStudies/ \
    --src-lang fr \
    -o translations/casestudies/casestudies.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/casestudies/
```

Sortie attendue = JSON `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC). Les drifts apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles `text_en/es/ar/fa/zh/ru/pt` (les colonnes `hash_*` correspondantes seront alors remplies).

## Voir aussi

- Issue #4957 — design infrastructure
- Epic #1650 — traduction multilingue du dépôt
- `scripts/translation/README.md` — schéma détaillé
