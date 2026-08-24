# Source des données `app22-cross-paradigm`

Les trois fichiers CSV de ce répertoire (`sudoku_results.csv`, `connect_four_results.csv`,
`wordle_results.csv`) sont **copiés** depuis le dépôt suivant, sans modification :

| Champ | Valeur |
|---|---|
| **Travail original** | *« Benchmark cross-paradigme de solveurs de jeux »* — sujet **L4**, cours **Intelligence Symbolique**, EPITA SCIA |
| **Auteur** | **Théodore Deguest** |
| **Dépôt source** | `jsboigeEpita/2026-Epita-Intelligence-Symbolique` |
| **Pull request** | [#42](https://github.com/jsboigeEpita/2026-Epita-Intelligence-Symbolique/pull/42) |
| **Commit source** | `52045085c4efcab96383838d7e55b62d4774af70` (HEAD de la PR #42) |
| **Chemins d'origine** | `L4-Benchmark-Cross-Paradigm/results/{sudoku,connect_four,wordle}_results.csv` |
| **Licence** | MIT — copyright 2026, « The 2026-Epita-Intelligence-Symbolique contributors » (voir [`LICENSE`](LICENSE)) |

## Provenance et bon usage

- Ces données sont la **propriété intellectuelle de Théodore Deguest**, réutilisées ici
  dans le cadre de la **distillation** pédagogique ([App-22-AlgorithmSelection-Python](../../App-22-AlgorithmSelection-Python.ipynb)).
- Elles sont redistribuées sous **licence MIT** : le copyright et la mention de licence
  ci-dessus sont conservés (conditions MIT).
- **Aucun code de solveur** n'est recopié dans le notebook : les solveurs étudiants
  restent dans le dépôt source, référencés et testés.
- Les valeurs reproduisent les **résultats précalculés** du benchmark (collecte sous
  **Unix**, voir les limites honnêtes du notebook). Le notebook ne régénère aucun résultat.

## Contenu

- `sudoku_results.csv` — 210 lignes, 7 familles (backtracking, backtracking_mrv,
  dancing_links, cp_sat, smt, genetic, simulated_annealing), 30 instances par famille.
- `connect_four_results.csv` — 35 lignes, 4 familles (minimax, alpha_beta, mcts, baseline).
- `wordle_results.csv` — 120 lignes, 3 familles (bayesian_elimination, entropy, csp).
