# CSV de synchro traduction — série Search/Part4-Metaheuristics

**Statut** : Phase 2 rollout (Epic #4957 / #1650). 9ᵉ série couverte par l'infrastructure i18n, après `SymbolicAI/Argument_Analysis/` (PR #5799), `Probas/Infer/` (PR #5801), `ML/ML.Net/` (PR #5805), `SymbolicAI/Planners/` (PR #5806), `SymbolicAI/SmartContracts/` (PR #5808), `Sudoku/` (PR #5809), `Search/Part1-Foundations/` (PR #5810) et `Search/Part2-CSP/` (PR #5811).

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`search-part4.csv`](search-part4.csv) | `Search/Part4-Metaheuristics/` | 19 (MGS-1-Introduction → MGS-19-MetropolisReinsertion, métaheuristiques GenetiqueSharp : introduction/compositions/eukaryote/islands/compound/benchmarks/TSP/landscape/relief/center-bias/island-synergy/axis-alignment/debias/landscape-foundations/algorithm-selection/parameter-control/CeC-banc/recuit-simulé) | 432 (header + 7 227 lignes CSV-escaped, 20 colonnes) |

**Note owner-lane strict** : la série Search/Part4-Metaheuristics = **owner po-2025 strict** (PRs récentes #5324 #5193 #5160 #5154 #5060 #4748 #4693 #4686 #4683 #4603 = `Jean-Sylvain Boige`). L'extraction i18n est **safe owner-lane** (L143 SAFE : artefacts dérivés = CSV de cellules upstream, pas de modification de code des notebooks).

**Note CJK upstream** : pas de caractères CJK (Han/Hangul/Fullwidth) détectés dans le CSV de cette série — les notebooks MGS-* sont quasi exclusivement en français et en anglais (avec termes métaheuristiques : recuit simulé, îlot, paysage adaptatif, algorithme génétique, etc.). cf L327 « pas de scrub ».

**Note cross-language** : la série Search/Part4-Metaheuristics est principalement Python (Cec-Banc fitness, recuit simulé, algorithmes évolutionnaires). Le script d'extraction prend **toutes les cellules** verbatim (chaque notebook est une cellule source indépendante). La traduction future T3 (moteur Argumentum) appliquera ce qui est extractible.

**Note MetaGeneticSharp (submodule)** : la série repose sur le submodule `MyIA.AI.Notebooks/Search/MetaGeneticSharp` (fork de `giacomelli/GeneticSharp` v0.1.0~1). Le submodule est git-tracked séparément et **n'est pas modifié** par l'extraction i18n — le script `extract_cells_to_csv.py` ne lit que les `.ipynb` du dossier `Search/Part4-Metaheuristics/`, pas le contenu du submodule. Conformité L143 SAFE triviale respectée.

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/Search/Part4-Metaheuristics/ \
    -o translations/search-part4/search-part4.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/search-part4/
```

Sortie = JSON `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC). Les drifts apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles `text_en/es/ar/fa/zh/ru/pt` (les colonnes `hash_*` correspondantes seront alors remplies).

## Acceptance #4957 Phase 2

- [x] T1 extraction OK : 432 cellules / 19 notebooks Search/Part4-Metaheuristics (métaheuristiques GenetiqueSharp : MGS-1 → MGS-19)
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
- `scripts/translation/README.md` — scripts T1+T2
- `.github/workflows/translation-drift.yml` — CI non-bloquante
