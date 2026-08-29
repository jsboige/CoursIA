# Source des données `app22-cross-paradigm`

Les trois fichiers CSV historiques de ce répertoire (`sudoku_results.csv`,
`connect_four_results.csv`, `wordle_results.csv`) sont **copiés** depuis le dépôt
suivant, sans modification. Le quatrième (`wordle_repeated_results.csv`) est une
**expérience dérivée CoursIA**, décrite séparément ci-dessous :

| Champ | Valeur |
|---|---|
| **Travail original** | *« Benchmark cross-paradigme de solveurs de jeux »* — sujet **L4**, cours **Intelligence Symbolique**, EPITA SCIA |
| **Auteur** | **Théodore Deguest** |
| **Dépôt source** | `jsboigeEpita/2026-Epita-Intelligence-Symbolique` |
| **Pull request** | [#42](https://github.com/jsboigeEpita/2026-Epita-Intelligence-Symbolique/pull/42) |
| **Projet** | [L4-Benchmark-Cross-Paradigm](https://github.com/jsboigeEpita/2026-Epita-Intelligence-Symbolique/tree/main/L4-Benchmark-Cross-Paradigm) |
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
- Les trois CSV historiques reproduisent les **résultats précalculés** du benchmark
  (collecte sous **Unix**, voir les limites honnêtes du notebook).

## Expérience dérivée CoursIA (24 août 2026)

`wordle_repeated_results.csv` a été produit sous **WSL/Linux** depuis le code étudiant
inchangé au commit `52045085`, avec `uv run python` :

- 3 instances Wordle de longueur 5 issues de `sample_instances(n_per_length=3, seed=42)` ;
- 3 solveurs (`bayesian_elimination`, `entropy`, `csp`) ;
- 5 graines (`0..4`) par couple solveur × instance, soit **45 mesures** ;
- cache `_first_guess_cache` du solveur entropique vidé avant **chaque** répétition,
  afin que chaque temps mesure un départ à froid plutôt qu'un premier run froid suivi
  de quatre runs chauds ;
- toutes les mesures ont réussi. Le CSV conserve succès, temps, nœuds et nombre de coups.

Ce fichier n'est donc **pas attribué à l'étudiant comme donnée originale** : le code et
les instances sont les siens (MIT), mais le protocole multi-seed et la collecte sont une
extension CoursIA. Le script de collecte ponctuel n'est pas embarqué dans le notebook :
la procédure exacte ci-dessus suffit à la reproduire depuis le dépôt source.

## Contenu

- `sudoku_results.csv` — 210 lignes, 7 familles (backtracking, backtracking_mrv,
  dancing_links, cp_sat, smt, genetic, simulated_annealing), 30 instances par famille.
- `connect_four_results.csv` — 35 lignes, 4 familles (minimax, alpha_beta, mcts, baseline).
- `wordle_results.csv` — 120 lignes, 3 familles (bayesian_elimination, entropy, csp).
- `wordle_repeated_results.csv` — 45 lignes dérivées CoursIA : 3 instances × 3
  solveurs × 5 graines, cache entropique réinitialisé entre répétitions.
