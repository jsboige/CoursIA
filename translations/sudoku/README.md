# CSV de synchro traduction — série Sudoku

**Statut** : Phase 2 rollout (Epic #4957 / #1650). 6ᵉ série couverte par l'infrastructure i18n, après `SymbolicAI/Argument_Analysis/` (PR #5799), `Probas/Infer/` (PR #5801), `ML/ML.Net/` (PR #5805), `SymbolicAI/Planners/` (PR #5806) et `SymbolicAI/SmartContracts/` (PR #5808).

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`sudoku.csv`](sudoku.csv) | `Sudoku/` | 36 (Sudoku-0-Environment → Sudoku-19-Lean-Propagation, parité C#/Python via paires miroir 1-15 et 18, + 0-Environment C# only, 16-NeuralNetwork et 17-LLM Python only, 19-Lean natif) | 1 223 (header + 32 362 lignes CSV-escaped, 20 colonnes) |

**Note owner-lane strict** : la série Sudoku = **owner po-2025 strict** (toutes les PRs récentes #5473 #5404 #5406 #5407 #5454 #5639 #5769 #5778 = `Jean-Sylvain Boige`). L'extraction i18n est **safe owner-lane** (L143 SAFE : artefacts dérivés = CSV de cellules upstream, pas de modification de code des notebooks).

**Note CJK upstream** : 2 caractères Han (U+5B8C U+6574 = `完整` « complet ») dans la cellule L6077 = « une grille-témoin完整e » (SFAz3 + Z3, section 6b). Préservés verbatim par l'extracteur déterministe (le hash sha256-16 doit sinon drifter si on altérait la cellule). cf L327 « pas de scrub ».

**Note cross-language** : la série Sudoku est cross-language (C#/.NET Interactive via jumeaux `-Csharp.ipynb` + Python 3.10+ via jumeaux `-Python.ipynb` + Lean 4 via `Sudoku-19-Lean-Propagation.ipynb`). Le script d'extraction prend **les trois familles** verbatim (chaque notebook est une cellule source indépendante). La traduction future T3 (moteur Argumentum) appliquera les trois familles.

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/Sudoku/ \
    -o translations/sudoku/sudoku.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/sudoku/
```

Sortie = JSON `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC). Les drifts apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles `text_en/es/ar/fa/zh/ru/pt` (les colonnes `hash_*` correspondantes seront alors remplies).

## Acceptance #4957 Phase 2

- [x] T1 extraction OK : 1 223 cellules / 36 notebooks Sudoku (16 paires miroir C#/Python + 1 mono C# + 2 mono Python + 1 Lean)
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
- `translations/planners/README.md` — 4ᵉ série (Planners)
- `translations/smartcontracts/README.md` — 5ᵉ série (SmartContracts)
- `scripts/translation/README.md` — scripts T1+T2
- `.github/workflows/translation-drift.yml` — CI non-bloquante
