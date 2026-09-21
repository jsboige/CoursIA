# Scan NTFS junctions Mathlib — myia-po-2023

**Issue** : #13962 (sous-grain de #4362, acceptance step 1 = « Scan d'abord »)
**Date** : 2026-09-07T15:00Z (c.297 phase 2)
**Lane** : myia-po-2023:CoursIA-2
**Outil** : `scripts/lean/setup_shared_mathlib.ps1 -Mode Scan` (PowerShell 7.6.3)

## TL;DR

Economie potentielle sur **myia-po-2023** : **0,64 GB** (le plus gros des 3 checkouts physiques du cluster `v4.32.1-520045ab` reste comme donneur, les 2 autres passent en jonction). **27 projets Lake avec dépendance mathlib** sur cette machine, 3 groupes mutualisables + 4 isolés.

| Mesure | Valeur |
|---|---|
| Projets Lake total avec mathlib | **27** |
| Groupes MUTUALISABLE | **2** (`v4.32.1-520045ab`, `v4.33.0-db584cd6`) |
| Groupes isolés | **4** (`v4.25.0`, `v4.31.0-rc2`, `v4.32.1` × 3) |
| Projets avec checkout physique local | **3** |
| Empreinte cumulee des checkouts physiques | **1,28 GB** |
| **Economie potentielle** | **0,64 GB** |

## Sortie verbatim du Scan

```
=== Projets Lake avec dependance mathlib (27) ===

--- Groupe leanprover_lean4_v4.32.1-520045ab [MUTUALISABLE] : toolchain=leanprover/lean4:v4.32.1 mathlib=520045ab ---
  MyIA.AI.Notebooks/GameTheory/game_theory_lean                          checkout physique (0.64 GB)
  MyIA.AI.Notebooks/GameTheory/repeated_games_lean                       pas de checkout local
  MyIA.AI.Notebooks/ML/learning_theory_lean                              checkout physique (0.55 GB)
  MyIA.AI.Notebooks/Probas/Applications/Percolation/percolation_lean     pas de checkout local
  MyIA.AI.Notebooks/Probas/decision_theory_lean                          pas de checkout local
  MyIA.AI.Notebooks/QuantConnect/kelly_lean                              pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/calibration_lean                     pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean                          checkout physique (0.09 GB)
  MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean                            pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/mathlib_examples                     pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean                    pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/SmartContracts/erc20_lean                 pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean                 pas de checkout local
  => economie potentielle : 0.64 GB (garder le plus gros comme donneur)

--- Groupe leanprover_lean4_v4.33.0-db584cd6 [MUTUALISABLE] : toolchain=leanprover/lean4:v4.33.0 mathlib=db584cd6 ---
  MyIA.AI.Notebooks/GameTheory/assignment_lean                           pas de checkout local
  MyIA.AI.Notebooks/GameTheory/minimax_lean                              pas de checkout local
  MyIA.AI.Notebooks/Search/search_lean                                   pas de checkout local
  MyIA.AI.Notebooks/Sudoku/sudoku_lean                                   pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/formal_groups_lean                   pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/galois_lean                          pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean                    pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/hecke_lean                           pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean                     pas de checkout local

--- Groupe leanprover_lean4_v4.25.0-1ccd71f8 [isole] : toolchain=leanprover/lean4:v4.25.0 mathlib=1ccd71f8 ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/session_state/reference_docs/stable_marriage/upstream pas de checkout local

--- Groupe leanprover_lean4_v4.31.0-rc2-acbd8f07 [isole] : toolchain=leanprover/lean4:v4.31.0-rc2 mathlib=acbd8f07 ---
  MyIA.AI.Notebooks/GameTheory/conway_cgt_lean                           pas de checkout local

--- Groupe leanprover_lean4_v4.32.1-520045ab [isole] : toolchain=leanprover/lean4:v4.32.1 mathlib=520045ab ---
  MyIA.AI.Notebooks/Search/discrepancy_lean                              pas de checkout local

--- Groupe leanprover_lean4_v4.32.1-520045ab [isole] : toolchain=leanprover/lean4:v4.32.1 mathlib=520045ab ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean                            pas de checkout local

--- Groupe leanprover_lean4_v4.32.1-520045ab [isole] : toolchain=leanprover/lean4:v4.32.1 mathlib=520045ab ---
  MyIA.AI.Notebooks/GameTheory/social_choice_lean_peters                 pas de checkout local

=== Economie totale potentielle (groupes en l'etat) : 0.64 GB ===
```

## Lecture (rapportee au verdict de l'EPIC)

**Cluster `v4.32.1-520045ab`** : 13 projets pinnes sur la meme rev Mathlib, dont 3 avec checkout physique (game_theory_lean 0,64 GB / learning_theory_lean 0,55 GB / conway_lean 0,09 GB) et 10 qui ont deja consomme via `lake exe cache get` (pas de checkout local). L'economie de 0,64 GB reflete la strategie "garder le plus gros comme donneur, jonctionner les 2 autres vers lui".

**Cluster `v4.33.0-db584cd6`** : 9 projets pinnes sur v4.33.0, **0 avec checkout physique**. L'alignement de manifests est plus avance ici (les 9 sont sur la meme rev transitive), mais aucun n'a de `.lake/packages/mathlib` reel — donc l'economie est nulle **en l'etat**. L'effet prospectif de la mesure de ai-01 (8 lakes pinnes mais pas encore construits) ne s'applique pas a cette machine : aucun n'est encore dans l'etat "checkout physique" qui serait jonctionnable.

**4 groupes isoles** : 4 projets avec rev Mathlib uniques :
- `agent_tests/prover/session_state/reference_docs/stable_marriage/upstream` : v4.25.0 (fixture tierce, hors scope body).
- `conway_cgt_lean` : v4.31.0-rc2 transitif via vihdzp/combinatorial-games (pin non choisi par nous, exclusion explicite du body #13962 — #6116/#6432).
- `discrepancy_lean` : v4.32.1 isole (1 seul membre, pas de mutualisation possible).
- `mimo_lean` : v4.32.1 isole (1 seul membre).
- `social_choice_lean_peters` : v4.32.1 isole (1 seul membre, _peters).

## Differences vs mesure ai-01 (2026-09-01)

La mesure ai-01 rapportait 17 checkouts reels, ~110 Go empreinte totale, ~90 Go recuperables. Sur **myia-po-2023**, ces chiffres sont radicalement differents :

| | ai-01 (2026-09-01) | po-2023 (2026-09-07) |
|---|---:|---:|
| Projets avec checkout physique | 17 | **3** |
| Empreinte cumulee | ~110 GB | **1,28 GB** |
| Recuperable | ~90 GB | **0,64 GB** |

**Explication mesuree** : po-2023 est une machine de developpement Lean leger (CI-host), pas une machine de build avec cache chaud. Les 24 projets "pas de checkout local" ont deja consomme leur Mathlib via `lake exe cache get` (cache oleans precompile, pas le source) — la jonction n'a rien a y recuperer. **L'economie reelle sur cette machine est 0,64 GB**, marginale.

**Implication pour l'EPIC** : l'application des junctions sur po-2023 est **peu rentable** mais **non-nulle**. La rentabilite reelle est sur les machines type ai-01 (cache chaud, plusieurs builds successifs, oleans accumules). **Cette mesure first-hand permet a l'EPIC d'evaluer l'effort par machine plutot que par total**.

## Decision prise (Scan uniquement, PAS d'Apply)

Acceptance #13962 step 1 (Scan) est **accomplie pour myia-po-2023**. Steps 2-3-4 (Apply + anti-regression + mesure effectif) sont **gated par accord explicite dans le fil** (la prudence anti-irreversible du body tient : remplacer un checkout physique par une jonction **supprime** ~6,5 Go dont la reconstitution coute un `lake exe cache get` + build complet).

**Position de la lane** : **Apply sur po-2023 NON recommande en l'etat** — l'economie de 0,64 GB ne justifie pas le risque irreversible sur cette machine legere. **Recommandation** : appliquer les junctions sur ai-01 et machines de build lourd d'abord, re-mesurer sur po-2023 quand le cluster v4.32.1 prendra du volume (par exemple apres l'ajout d'un nouveau lake pinne sur 520045ab).

## Pas dans cette PR

- Aucune jonction creee, aucun `.lake/packages/mathlib` modifie.
- Aucun appel `lake update` / `lake build`.
- Aucune modification du script (`setup_shared_mathlib.ps1` reste en `Scan` only — l'Apply etait deja ferme depuis #2611).

## References croisees

- Issue #13962 — body, acceptance step 1 « Scan d'abord ».
- Issue #4362 — EPIC parent (3 phases historiques CLOSED : #4363 junctions, #4364 convergence, #4365 regroupements).
- Issue #2611 — outillage `setup_shared_mathlib.ps1`, ferme 2026-07-03.
- Issue #4365 — phase « regroupements », derniere convergence manifest.
- PR #14038 — scan po-2026 (0 GB, 19 lakes sans checkout).
- PR #14296 — scan po-2024 (mesure a verifier, autre machine).
- PR #15057 — c.297 phase 1 (REPAIR P0 followup GT-29, lane myia-po-2023).

## L898 / L1356 / G.9

- L898 : `gh pr list --state all --search '13962 in:body'` = 2 PRs MERGED (po-2026 #14038, po-2024 #14296). Aucune PR OUVERTE.
- L1356 : aucune PR merged sur ce numero n'a couvert myia-po-2023 (machine distincte de po-2026/po-2024/ai-01). Grain pas livre pour cette machine.
- G.9 : scan execute localement, sortie verbatim citee, mesures premieres (taille checkouts via script, pas d'estimation). Position ecrite avant Apply — prudence anti-irreversible honoree.

— myia-po-2023:CoursIA-2, c.297 phase 2 (post REPAIR P0 #15057).
