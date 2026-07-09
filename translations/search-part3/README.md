# CSV de synchro traduction — série Search/Part3-Advanced

**Statut** : Phase 2 rollout (Epic #4957 / #1650). 10ᵉ série couverte par l'infrastructure i18n, après `SymbolicAI/Argument_Analysis/` (PR #5799), `Probas/Infer/` (PR #5801), `ML/ML.Net/` (PR #5805), `SymbolicAI/Planners/` (PR #5806), `SymbolicAI/SmartContracts/` (PR #5808), `Sudoku/` (PR #5809), `Search/Part1-Foundations/` (PR #5810), `Search/Part2-CSP/` (PR #5811) et `Search/Part4-Metaheuristics/` (PR #5812).

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`search-part3.csv`](search-part3.csv) | `Search/Part3-Advanced/` | 6 (Search-11-Bridge / Search-12-PatternDatabases + jumeau C# / Search-13-LDS + jumeau C# / Search-14-WeightedAstar + jumeau C#) | 102 (header + 1 748 lignes CSV-escaped, 20 colonnes) |

**Note owner-lane strict** : la série Search/Part3-Advanced = **owner po-2025 strict** (PRs récentes #5425 #5287 #5283 #4724 #4713 #4341 #4288 = `Jean-Sylvain Boige`). L'extraction i18n est **safe owner-lane** (L143 SAFE : artefacts dérivés = CSV de cellules upstream, pas de modification de code des notebooks).

**Note CJK upstream** : pas de caractères CJK (Han/Hangul/Fullwidth) détectés dans le CSV de cette série — la série Search/Part3 est principalement en français/anglais (notebooks d'algorithmes avancés : Pattern Databases, Limited Discrepancy Search, Weighted A*, Bridge vers CSP). cf L327 « pas de scrub ».

**Note cross-language** : la série Search/Part3-Advanced est cross-language (Python 3.10+ natif + jumeaux C# co-localisés via `-Csharp.ipynb` suffix sur Search-12/13/14). Le script d'extraction prend **les deux familles** verbatim (chaque notebook est une cellule source indépendante). La traduction future T3 (moteur Argumentum) appliquera les deux familles.

**Note substance mince** : 6 notebooks / 102 cellules — substance modeste (≈17 cellules/nb en moyenne). C'est le **plus petit** des 4 sous-séries Search. Conforme à l'atomicité G.4 (1 feature, 2 fichiers CSV+README, < 3000 lignes, 1 domaine). Cohérent avec le pattern c.384/c.385/c.386 Search-rollout structuré.

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/Search/Part3-Advanced/ \
    -o translations/search-part3/search-part3.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/search-part3/
```

Sortie = JSON `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC). Les drifts apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles `text_en/es/ar/fa/zh/ru/pt` (les colonnes `hash_*` correspondantes seront alors remplies).

## Acceptance #4957 Phase 2

- [x] T1 extraction OK : 102 cellules / 6 notebooks Search/Part3-Advanced (Search-11/12/13/14 + jumeaux C#)
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
- `translations/search-part1/README.md` — 7ᵉ série (Search/Part1-Foundations)
- `translations/search-part2/README.md` — 8ᵉ série (Search/Part2-CSP)
- `translations/search-part4/README.md` — 9ᵉ série (Search/Part4-Metaheuristics)
- `scripts/translation/README.md` — scripts T1+T2
- `.github/workflows/translation-drift.yml` — CI non-bloquante
