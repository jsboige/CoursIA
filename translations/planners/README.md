# CSV de synchro traduction — série Planners

**Statut** : Phase 2 rollout (Epic #4957 / #1650). 4ᵉ série couverte par l'infrastructure i18n, après `SymbolicAI/Argument_Analysis/` (PR #5799), `Probas/Infer/` (PR #5801) et `ML/ML.Net/` (PR #5805).

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`planners.csv`](planners.csv) | `SymbolicAI/Planners/` | 24 (Planners-0-Setup → Planners-12-LOOP ; jumeaux C# `-Csharp.ipynb` co-localisés + Planners-5b-Lean-Relaxation) | 1005 (header + 1005 lignes, 20 colonnes) |

**Note cross-owner** : la série Planners est owner-floue **po-2024** (PRs twin C# #5591, #5709 sweep figures doctrine). L'extraction i18n est **safe cross-owner** (L143 SAFE : artefacts dérivés = CSV de cellules upstream, pas de modification de code des notebooks), conforme au pattern Phase 2 validé sur 3 séries owner po-2025 (Argument_Analysis + Probas/Infer + ML/ML.Net).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/SymbolicAI/Planners/ \
    -o translations/planners/planners.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/planners/
```

Sortie = JSON `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC). Les drifts apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles `text_en/es/ar/fa/zh/ru/pt` (les colonnes `hash_*` correspondantes seront alors remplies).

## Acceptance #4957 Phase 2

- [x] T1 extraction OK : 1005 cellules / 24 notebooks (Planning PDDL/STRIPS/CP/Temporal/HTN/LLM/Unified/LOOP)
- [x] T2 round-trip IN_SYNC : 0 anomaly
- [x] Script T1+T2 inchangés (Phase 1 INFRA #5657 réutilisée telle quelle)
- [x] Workflow CI `.github/workflows/translation-drift.yml` non touché
- [ ] T3 (run moteur Argumentum #1650 Phase 1 connecteur) : gated owner po-2025 c.371-372

## Voir aussi

- Issue #4957 — design infrastructure synchronisation traduction
- Epic #1650 — traduction multilingue du dépôt
- `translations/symbolicai/README.md` — 1ère série (Argument_Analysis)
- `translations/probas-infer/README.md` — 2ᵉ série (Probas/Infer)
- `translations/mlnet/README.md` — 3ᵉ série (ML/ML.Net)
- `scripts/translation/README.md` — scripts T1+T2
- `.github/workflows/translation-drift.yml` — CI non-bloquante