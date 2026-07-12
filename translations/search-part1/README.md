# CSV de synchro traduction — série Search/Part1-Foundations

**Statut** : Phase 2 rollout (Epic #4957 / #1650). 7ᵉ série couverte par l'infrastructure i18n, après `SymbolicAI/Argument_Analysis/` (PR #5799), `Probas/Infer/` (PR #5801), `ML/ML.Net/` (PR #5805), `SymbolicAI/Planners/` (PR #5806), `SymbolicAI/SmartContracts/` (PR #5808) et `Sudoku/` (PR #5809).

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`search-part1.csv`](search-part1.csv) | `Search/Part1-Foundations/` | 29 (Search-1-Setup → Search-29-CSP-Project, BFS/DFS/A*/UCS/Greedy/IDA*/Bidir + jumeaux C# co-localisés) | 1 077 (header + 24 592 lignes CSV-escaped, 20 colonnes) |

**Note owner-lane strict** : la série Search/Part1-Foundations = **owner po-2025 strict** (PRs récentes = `Jean-Sylvain Boige`). L'extraction i18n est **safe owner-lane** (L143 SAFE : artefacts dérivés = CSV de cellules upstream, pas de modification de code des notebooks).

**Note CJK upstream** : 2 caractères Han (U+5206 U+6521 = `分支` « branche ») dans la cellule CBC (COIN-OR Branch-and-Cut) « explore un arbre de分支 en résolvant des relaxations continues ». Préservés verbatim par l'extracteur déterministe (le hash sha256-16 doit sinon drifter si on altérait la cellule). cf L327 « pas de scrub ».

**Note cross-language** : la série Search/Part1-Foundations est cross-language (Python 3.10+ natif + jumeaux C# co-localisés sur plusieurs notebooks via `-Csharp.ipynb`). Le script d'extraction prend **les deux familles** verbatim (chaque notebook est une cellule source indépendante). La traduction future T3 (moteur Argumentum) appliquera les deux familles.

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/Search/Part1-Foundations/ \
    -o translations/search-part1/search-part1.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/search-part1/
```

Sortie = JSON `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC). Les drifts apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles `text_en/es/ar/fa/zh/ru/pt` (les colonnes `hash_*` correspondantes seront alors remplies).

## Acceptance #4957 Phase 2

- [x] T1 extraction OK : 1 077 cellules / 29 notebooks Search/Part1-Foundations (BFS/DFS/A*/UCS/Greedy/IDA*/Bidir + jumeaux C#)
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
- `translations/sudoku/README.md` — 6ᵉ série (Sudoku)
- `scripts/translation/README.md` — scripts T1+T2
- `.github/workflows/translation-drift.yml` — CI non-bloquante
