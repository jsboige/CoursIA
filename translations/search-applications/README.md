# CSV de synchro traduction — série Search/Part3-Cas-pratiques

**Statut** : Phase 2 rollout (Epic #4957 / #1650). Les cas pratiques de recherche (ex-`Applications/`, dossier plat `Part3-Cas-pratiques/` depuis #19253 ; familles CSP, hybrides, adversariales) sont couverts par l'infrastructure i18n.

## Couvert

| Fichier | Série | Notebooks | Cellules |
|---------|-------|-----------|----------|
| [`search-applications.csv`](search-applications.csv) | `MyIA.AI.Notebooks/Search/Part3-Cas-pratiques/` | 48 (dossier plat, déplacement #19253) | 1891 (markdown + code, 20 colonnes) |

La série couvre les trois familles de cas pratiques du cours de recherche (thématiques, le dossier étant plat) :

- **CSP** (26 notebooks) — modélisation et résolution de problèmes de satisfaction de contraintes : N-Queens, graph coloring, nurse/job-shop/sports/timetabling, Picross, Wordle, Minesweeper, Crossword, WFC, MiniZinc, Sudoku benchmark.
- **Hybrid** (10 notebooks) — métaheuristiques et approches mixtes : edge detection, portfolio, TSP, VRP logistics, hyperparameter tuning.
- **Search** (4 notebooks) — applications adversariales et de jeu : Connect Four (minimax + adversarial).

**Schéma** : 20 colonnes (#4957 §1). `src_lang=fr`, `src_hash` (sha256-16) + `text_fr` remplies ; colonnes cibles (`text_en/es/ar/fa/zh/ru/pt`) vides pour le moteur T3 Argumentum (#1650 Phase 1).

## Régénération

```bash
# Depuis la racine du dépôt :
python scripts/translation/extract_cells_to_csv.py \
    MyIA.AI.Notebooks/Search/Part3-Cas-pratiques \
    -o translations/search-applications/search-applications.csv \
    --src-lang fr
```

L'extraction est **déterministe byte-identique** (même ordre de notebooks, mêmes hash sha256-16 sur texte normalisé) — re-exécuter produit le même CSV.

## Vérification de drift (T2)

```bash
python scripts/translation/check_translation_sync.py translations/search-applications/search-applications.csv
```

Résultat à l'extraction : `OK : 1 CSV vérifié(s), 0 drift` (IN_SYNC par construction).

## Pre-flight secret

Les notebooks Search/Applications sont en C# .NET (OR-Tools `Google.OrTools`, propagateurs from-scratch, solveurs CP-SAT). Risque secret faible (pas d'API externe type OpenAI/HF), mais scan systématique sur le CSV avant commit : `sk-*`, `ghp_*`, `hf_*`, `AIza*`, `os.getenv(KEY, "<literal>")` = **0 hit**.

## Note owner

`Search/Applications/` = partition native po-2024 (CPU/.NET). L'extraction i18n est **safe cross-owner** : artefact dérivé (CSV de cellules upstream en lecture seule), aucune modification des notebooks source (cf note identique dans `translations/genai/README.md` et `translations/smartcontracts/README.md`).

## Hors scope

- `Search/Part1-Foundations/`, `Search/Part2-CSP/`, `Search/Part4-Metaheuristics/` — séries foundations distinctes, déjà couvertes par `translations/search-part1`, `search-part2` et `search-part4`.
- `Search/Part3-Cas-pratiques/assets/` et `data/` — supports non pédagogiques (exclus par le glob `.ipynb` top-level récursif).
