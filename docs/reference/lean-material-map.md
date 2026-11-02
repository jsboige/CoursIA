<!-- fichier genere par scripts/lean/lean_material_map.py -- ne pas editer a la main ; relancer le generateur -->

# Carte du materiel Lean du depot

Une ligne par lac. Les colonnes sont des mesures rejouables, pas des appreciations : `Modules` compte les fichiers `.lean` propres du lac, `Miroirs` les freres `_en`, `Naissance` la date d'ajout du `lakefile`. La colonne `Gate axiomes` reprend le verdict de `scripts/lean/check_axiom_gate_coverage.py`.

Cette page est regeneree par `scripts/lean/lean_material_map.py`. Une table recopiee a la main derive au premier merge : c'est la maladie que #23097 soigne, et `--check` est le garde-fou.

`sans gate` n'est pas un defaut : la couverture est une mesure, pas un verdict de surete (#17097 critere 3). Un lac sans gate doit seulement etre **connu** comme tel.

| Lac | Modules | Miroirs | CI | Gate axiomes | Naissance |
|---|---|---|---|---|---|
| `MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean` | 99 | 97 | declare | couverte | 2026-05-31 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean` | 50 | 41 | declare | couverte | 2026-05-28 |
| `MyIA.AI.Notebooks/GameTheory/game_theory_lean` | 38 | 24 | declare | couverte | 2026-07-10 |
| `MyIA.AI.Notebooks/ML/learning_theory_lean` | 32 | 30 | declare | sans gate | 2026-06-25 |
| `MyIA.AI.Notebooks/Search/discrepancy_lean` | 31 | 23 | declare | sans gate | 2026-08-25 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/knot_lean` | 24 | 23 | declare | couverte | 2026-10-08 |
| `MyIA.AI.Notebooks/Compression/Compression_lean` | 15 | 2 | declare | couverte | 2026-10-12 |
| `MyIA.AI.Notebooks/GameTheory/lean_game_defs_ext` | 14 | 14 | declare | sans gate | 2026-06-10 |
| `MyIA.AI.Notebooks/Probas/DecisionTheory/decision_theory_lean` | 14 | 13 | declare | sans gate | 2026-10-02 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean` | 12 | 10 | declare | couverte | 2026-05-15 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/tegmark_muh_lean` | 11 | 0 | declare | sans gate | 2026-09-21 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Langlands/hecke_lean` | 9 | 8 | declare | couverte | 2026-09-06 |
| `MyIA.AI.Notebooks/Probas/Applications/Percolation/percolation_lean` | 8 | 7 | declare | couverte | 2026-09-06 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean` | 8 | 0 | declare | couverte | 2026-09-11 |
| `MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean` | 8 | 6 | declare | sans gate | 2026-06-24 |
| `MyIA.AI.Notebooks/GameTheory/assignment_lean` | 7 | 6 | declare | couverte | 2026-08-23 |
| `MyIA.AI.Notebooks/Search/search_lean` | 7 | 6 | declare | couverte | 2026-07-09 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry/geometry_lean` | 7 | 0 | declare | couverte | 2026-10-04 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/serre100_lean` | 7 | 6 | declare | couverte | 2026-09-19 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean` | 7 | 6 | declare | couverte | 2026-08-15 |
| `MyIA.AI.Notebooks/GameTheory/asymmetric_information_lean` | 6 | 6 | declare | couverte | 2026-08-26 |
| `MyIA.AI.Notebooks/GameTheory/lean_game_defs` | 6 | 6 | declare | sans gate | 2026-06-10 |
| `MyIA.AI.Notebooks/QuantConnect/kelly_lean` | 6 | 5 | declare | couverte | 2026-06-24 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/calibration_lean` | 6 | 5 | declare | sans gate | 2026-05-29 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/formal_groups_lean` | 6 | 5 | declare | couverte | 2026-09-06 |
| `MyIA.AI.Notebooks/GameTheory/minimax_lean` | 5 | 4 | declare | couverte | 2026-06-24 |
| `MyIA.AI.Notebooks/Sudoku/sudoku_lean` | 5 | 4 | declare | couverte | 2026-06-24 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/galois_lean` | 5 | 2 | declare | couverte | 2026-08-12 |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/erc20_lean` | 5 | 4 | declare | sans gate | 2026-06-24 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/ANALYSE/kls_lean` | 4 | 0 | hors CI | hors matrice | 2026-10-08 |
| `MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean` | 4 | 3 | declare | couverte | 2026-06-24 |
| `MyIA.AI.Notebooks/IIT/iit_lean` | 3 | 1 | declare | sans gate | 2026-10-24 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/riemann200_lean` | 3 | 0 | declare | couverte | 2026-10-18 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean` | 3 | 2 | hors CI | hors matrice | 2026-10-07 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/finiteness_lean` | 3 | 1 | declare | couverte | 2026-06-15 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/mathlib_examples` | 3 | 1 | declare | sans gate | 2026-01-29 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/torchlean_lean` | 3 | 0 | hors CI | hors matrice | 2026-10-22 |
| `MyIA.AI.Notebooks/GameTheory/conway_cgt_lean` | 2 | 1 | declare | sans gate | 2026-06-05 |
| `MyIA.AI.Notebooks/GameTheory/SocialChoice/social_choice_lean_peters` | 0 | 0 | declare | vendu | 2026-10-05 |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/session_state/reference_docs/stable_marriage/upstream` | 0 | 0 | hors CI | vendu | 2026-05-16 |

## Ce que la carte etablit

38 lacs propres, plus 2 dossier vendu. Les lacs hors CI sont listes ci-dessous : ce sont eux qui rendent une consolidation invisible depuis la matrice de build.

### Reconciliation

486 modules + 372 miroirs attribues a un lac + 11 fichiers hors lac + 26 fichiers ecartes (dossier vendu, ou extension `.lean` portee par un fichier qui n'est pas du Lean) = 895 fichiers `.lean` traces, soit la population entiere de `git ls-files '*.lean'`. Un fichier qui n'apparait dans aucune de ces quatre colonnes a ete perdu en route : c'est le defaut que cette reconciliation rend visible.

### Lacs hors CI

Ces lacs existent dans l'arbre et aucun workflow ne les nomme : ni `scripts/lean/ci_lakes.json`, ni un fichier de `.github/workflows/`. Aucun build de matrice ne les couvre.

- `MyIA.AI.Notebooks/SymbolicAI/Lean/ANALYSE/kls_lean` — 4 modules, ne le 2026-10-08
- `MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean` — 3 modules, ne le 2026-10-07
- `MyIA.AI.Notebooks/SymbolicAI/Lean/torchlean_lean` — 3 modules, ne le 2026-10-22

### Lacs de la matrice sans gate d'axiomes

Declares au CI, donc construits, mais le job `lean-axiom` ne les atteint pas : rien ne rougit si un axiome interdit y entre.

- `MyIA.AI.Notebooks/ML/learning_theory_lean` — 32 modules
- `MyIA.AI.Notebooks/Search/discrepancy_lean` — 31 modules
- `MyIA.AI.Notebooks/GameTheory/lean_game_defs_ext` — 14 modules
- `MyIA.AI.Notebooks/Probas/DecisionTheory/decision_theory_lean` — 14 modules
- `MyIA.AI.Notebooks/SymbolicAI/Lean/tegmark_muh_lean` — 11 modules
- `MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean` — 8 modules
- `MyIA.AI.Notebooks/GameTheory/lean_game_defs` — 6 modules
- `MyIA.AI.Notebooks/SymbolicAI/Lean/calibration_lean` — 6 modules
- `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/erc20_lean` — 5 modules
- `MyIA.AI.Notebooks/IIT/iit_lean` — 3 modules
- `MyIA.AI.Notebooks/SymbolicAI/Lean/mathlib_examples` — 3 modules
- `MyIA.AI.Notebooks/GameTheory/conway_cgt_lean` — 2 modules

### Fichiers `.lean` hors lac

Traces par git, mais dans aucun dossier portant un `lakefile` : ils ne sont construits par aucun lac, et aucune matrice ne les voit.

- `MyIA.AI.Notebooks/GameTheory/examples/arrow_simple.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/basic_logic.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/basic_logic_en.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/llm_assisted_proof.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/llm_assisted_proof_en.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/mathlib_examples.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/mathlib_examples_en.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/quantifiers.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/quantifiers_en.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/tactics_demo.lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/examples/tactics_demo_en.lean`

## Regle d'accretion d'un lac

Un lac nouveau dans une serie existante est legitime si (1) sa toolchain diverge de celle du lac de la serie, (2) sa theorie est distincte au sens de la clause anti-god-lake (#4365), ou (3) a toolchain egale il est le compagnon de construction d'un arc numerote de carnets -- importe par au moins un carnet Lean de cet arc, sans import croise avec le lac de la serie, et sans lui imposer une dependance (un path dep d'un lac tiers deviendrait sinon facteur commun). A defaut, c'est un module de plus du lac de la serie.

Verdicts tranches par la mesure (T2 #23097) :

| Lac | Cas | Verdict | Mesure fondatrice |
|---|---|---|---|
| `assignment_lean` | (3) compagnon d'arc | legitime-documente | Arc 16f : `GameTheory-16f-Lean-Assignment-Lean.ipynb` importe `Assignment.KuhnMunkres`. Toolchain et pin Mathlib identiques a `game_theory_lean` (v4.33.0, db584cd6), zero import croise, theorie (affectation hongroise, Kuhn-Munkres) absente des 8 branches du lac de la serie. |
| `asymmetric_information_lean` | (3) compagnon d'arc | legitime-documente | Arc 17b-17e : `GameTheory-17c-Lean-Lemons-Certificat-Lean.ipynb` importe `AsymmetricInformation.Lemons`, `GameTheory-17d-Lean-Screening-Signaling-Lean.ipynb` en importe 4 modules. Path dep non negociable vers `lean_game_defs_ext` (#12848) : la fusion imposerait ce pont aux 38 modules de `game_theory_lean`. Zero import croise. |

Les cas (1) toolchain divergente et (2) theorie distincte sont deja tranches : `social_choice_lean_peters` pour (1) (INTRINSIC #7081), `minimax_lean` et `conway_cgt_lean` pour (2).
