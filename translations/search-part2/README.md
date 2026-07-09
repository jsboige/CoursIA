# CSV de synchro traduction — série Search/Part2-CSP

**Statut** : Phase 2 rollout (Epic #4957 / #1650). 8ᵉ série couverte par l'infrastructure i18n, après `SymbolicAI/Argument_Analysis/` (PR #5799), `Probas/Infer/` (PR #5801), `ML/ML.Net/` (PR #5805), `SymbolicAI/Planners/` (PR #5806), `SymbolicAI/SmartContracts/` (PR #5808), `Sudoku/` (PR #5809) et `Search/Part1-Foundations/` (PR #5810).

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`search-part2.csv`](search-part2.csv) | `Search/Part2-CSP/` | 18 (CSP-1-Fundamentals → CSP-9-Distributed, jumeaux C# co-localisés, MRV/AC-3/FC/MAC/Allens/STP/TCSP/CP-SAT/Hybridation/DisCSP ABT/AWC/Privacy) | 784 (header + 18 709 lignes CSV-escaped, 20 colonnes) |

**Note owner-lane strict** : la série Search/Part2-CSP = **owner po-2025 strict** (PRs récentes = `Jean-Sylvain Boige` per git log récent #5700 #5460 #5384 #5371 #5277 #5276 #5275 #5274 #5270). L'extraction i18n est **safe owner-lane** (L143 SAFE : artefacts dérivés = CSV de cellules upstream, pas de modification de code des notebooks).

**Note CJK upstream** : 11 caractères Han (U+51E0 U+767E U+5909 U+6570 `几百変数` « quelques centaines de variables » cellule L16721 DisCSP benchmarks ABT/AWC + U+5206 U+5E03 U+5F0F U+7EA6 U+675F U+4F18 U+5316 `分布式约束优化` « optimisation distribuée de contraintes » cellule L17057 ADOPT/DPOP DisCSP confidentiels) — terminologie recherche internationale préservée verbatim par l'extracteur déterministe (le hash sha256-16 doit sinon drifter si on altérait la cellule). cf L327 « pas de scrub ».

**Note cross-language** : la série Search/Part2-CSP est cross-language (Python 3.10+ natif via Choco + jumeaux C# co-localisés sur 8 notebooks via `-Csharp.ipynb` suffix + IKVM 8.15 pour Choco 4.10.17 .NET). Le script d'extraction prend **les deux familles** verbatim (chaque notebook est une cellule source indépendante). La traduction future T3 (moteur Argumentum) appliquera les deux familles.

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/Search/Part2-CSP/ \
    -o translations/search-part2/search-part2.csv
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/search-part2/
```

Sortie = JSON `{"csvs_checked": 1, "anomalies": [], "anomaly_count": 0}` (IN_SYNC). Les drifts apparaîtront en T3 quand le moteur Argumentum déposera les colonnes cibles `text_en/es/ar/fa/zh/ru/pt` (les colonnes `hash_*` correspondantes seront alors remplies).

## Acceptance #4957 Phase 2

- [x] T1 extraction OK : 784 cellules / 18 notebooks Search/Part2-CSP (MRV/AC-3/FC/MAC + Allen + STP + TCSP + OR-Tools CP-SAT + Hybridation + DisCSP ABT/AWC/Privacy + jumeaux C#)
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
- `scripts/translation/README.md` — scripts T1+T2
- `.github/workflows/translation-drift.yml` — CI non-bloquante
