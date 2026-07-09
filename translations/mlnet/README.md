# CSV de synchro traduction — série ML/ML.Net

**Statut** : Phase 2 rollout (Epic #4957 / #1650). 3ᵉ série couverte par l'infrastructure i18n, après `SymbolicAI/Argument_Analysis/` (PR #5799) et `Probas/Infer/` (PR #5801).

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`mlnet.csv`](mlnet.csv) | `ML/ML.Net/` | 19 (ML-1 → ML-9 + TP-prevision-ventes ; jumeaux Python `-Python.ipynb` co-localisés) | 599 (header + 599 lignes, 12 colonnes) |

**Note parité** : la série ML/ML.Net expose des **jumeaux C# ⇄ Python** co-localisés (`ML-1-Introduction.ipynb` ⇄ `ML-1-Introduction-Python.ipynb`). Le script d'extraction prend **les deux langues** verbatim (chaque notebook est une cellule source indépendante). La traduction future T3 (moteur Argumentum) appliquera les deux familles de cellules.

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/ML/ML.Net/ \
    -o translations/mlnet/mlnet.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/mlnet/
```

Sortie = JSON `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC). Les drifts apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles `text_en/es/ar/fa/zh/ru/pt` (les colonnes `hash_*` correspondantes seront alors remplies).

## Acceptance #4957 Phase 2

- [x] T1 extraction OK : 599 cellules / 19 notebooks .NET Interactive + Python jumeaux
- [x] T2 round-trip IN_SYNC : 0 anomaly
- [x] Script T1+T2 inchangés (Phase 1 INFRA #5657 réutilisée telle quelle)
- [x] Workflow CI `.github/workflows/translation-drift.yml` non touché
- [ ] T3 (run moteur Argumentum #1650 Phase 1 connecteur) : gated owner po-2025 c.371-372

## Voir aussi

- Issue #4957 — design infrastructure synchronisation traduction
- Epic #1650 — traduction multilingue du dépôt
- `translations/symbolicai/README.md` — 1ère série (Argument_Analysis)
- `translations/probas-infer/README.md` — 2ᵉ série (Probas/Infer)
- `scripts/translation/README.md` — scripts T1+T2
- `.github/workflows/translation-drift.yml` — CI non-bloquante