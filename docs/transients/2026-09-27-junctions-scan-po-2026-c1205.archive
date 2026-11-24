# Mathlib NTFS junctions scan — `myia-po-2026` (2026-09-01)

**Issue** : #13962 (enfant de #4362)
**Machine** : `myia-po-2026` (worker Lean/QC/SymbolicLearning)
**Script** : `scripts/lean/setup_shared_mathlib.ps1 -Mode Scan` (#2611)
**Mode** : Scan (lecture seule, aucune modification)

## TL;DR

**Économie potentielle sur po-2026 : 0 GB.** Aucun des 19 lakes mutualisables
n'a de checkout local Mathlib. La machine n'a jamais fait de
`lake exe cache get` ni de `lake build` initial. L'outillage existe
(`setup_shared_mathlib.ps1` ferme depuis le 2026-07-03) mais l'application
n'a jamais eu lieu **et n'a pas de sens ici** : il n'y a rien à mutualiser.

Ce rapport documente la **mesure po-2026** en contraste avec la mesure
ai-01 (17 checkouts réels / ~110 Go / économie ~90 Go) rapportée par
l'auteur de #13962 le 2026-09-01.

## Sortie verbatim du Scan (2026-09-01)

```
=== Projets Lake avec dependance mathlib (24) ===

--- Groupe leanprover_lean4_v4.32.1-520045ab [MUTUALISABLE] : toolchain=leanprover/lean4:v4.32.1 mathlib=520045ab ---
  MyIA.AI.Notebooks/GameTheory/assignment_lean                           pas de checkout local
  MyIA.AI.Notebooks/GameTheory/game_theory_lean                          pas de checkout local
  MyIA.AI.Notebooks/GameTheory/minimax_lean                              pas de checkout local
  MyIA.AI.Notebooks/GameTheory/repeated_games_lean                       pas de checkout local
  MyIA.AI.Notebooks/ML/learning_theory_lean                              pas de checkout local
  MyIA.AI.Notebooks/Probas/decision_theory_lean                          pas de checkout local
  MyIA.AI.Notebooks/QuantConnect/kelly_lean                              pas de checkout local
  MyIA.AI.Notebooks/Search/search_lean                                   pas de checkout local
  MyIA.AI.Notebooks/Sudoku/sudoku_lean                                   pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/calibration_lean                     pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean                          pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/galois_lean                          pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean                    pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean                            pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/mathlib_examples                     pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean                     pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean                    pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/SmartContracts/erc20_lean                 pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean                 pas de checkout local

--- Groupe leanprover_lean4_v4.25.0-1ccd71f8 [isole] : toolchain=leanprover/lean4:v4.25.0 mathlib=1ccd71f8 ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/session_state/reference_docs/stable_marriage/upstream pas de checkout local

--- Groupe leanprover_lean4_v4.31.0-rc2-acbd8f07 [isole] : toolchain=leanprover/lean4:v4.31.0-rc2 mathlib=acbd8f07 ---
  MyIA.AI.Notebooks/GameTheory/conway_cgt_lean                           pas de checkout local

--- Groupe leanprover_lean4_v4.32.1-520045ab [isole] : toolchain=leanprover/lean4:v4.32.1 mathlib=520045ab ---
  MyIA.AI.Notebooks/Search/discrepancy_lean                              pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean                            pas de checkout local
  MyIA.AI.Notebooks/GameTheory/social_choice_lean_peters                 pas de checkout local

=== Economie totale potentielle (groupes en l'etat) : 0 GB ===
Note : l'alignement des manifests (#2611 etape 2) peut elargir les groupes.
```

## Première vérification (cycle 90, po-2026)

| Mesure | ai-01 (rapport #13962) | po-2026 (mesure cycle 90) |
|---|---|---|
| Checkouts Mathlib réels | **17** | **0** |
| Jonctions NTFS actives | 0 | 0 |
| Taille échantillon checkout | 6,46 Go | N/A |
| Empreinte totale | ~110 Go | 0 Go |
| Clusters homogène rev `520045ab` | 15 | 19 manifest-only, 0 réels |
| Économie jonction-cluster | ~90 Go | **0 Go** |

## Conclusion opérationelle

Le périmètre po-2026 du grain #13962 est **vide** : aucun checkout à
mutualiser, aucun espace à récupérer. C'est exactement le cas que
l'issue mentionne (« Une lane qui trouve 0 checkout réel n'a rien à
faire et le dit »).

## Causes probables (à confirmer)

1. **po-2026 = worker QC/Lean execution, pas cluster de build**. Les
   notebooks Lean s'exécutent via le kernel `lean4-wsl` (lui-même
   résident sur la VM WSL `machine-2026`), pas en checkouts natifs
   `lake build` sur po-2026.
2. **Le WSL est l'env de build canonique** (cf. CLAUDE.md section F +
   memory `wsl-kernel-execution`). Le cycle 87 `lean4-wsl notebook exec`
   recipe confirme ce pattern.
3. **ai-01 porte le cluster de jonction** : c'est la mesure mentionnée
   par l'auteur #13962. po-2026 ne contribue pas au parc de checkouts
   et n'a rien à mutualiser localement.

## Recommandation pour ai-01 / coordinateur

L'auteur de #13962 est sur ai-01 (vérifié par la signature de la mesure).
**Le grain s'exécute sur ai-01, pas po-2026**. Le Apply doit être
décidé et lancé sur ai-01 :

1. **Scan ai-01** déjà mesuré (rapport #13962) : 17 checkouts, 110 Go,
   cluster de 15.
2. **Apply ai-01** : `pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Apply
   -Group 520045ab -Build -RemoveBackups` -- après Scan + accord
   explicite (cf. #13962 §"Prudence").
3. **Vérification anti-régression** : pour chaque lake jonctionné,
   `lake build SUCCESS` post-jonction + `grep -c sorry` inchangé.
4. **Aucune action sur po-2026**.

## Suivi machine-par-machine (à étendre si d'autres lanes pertinentes)

| Machine | Scan | Checkouts réels | Économie potentielle |
|---|---|---|---|
| ai-01 | ✅ (rapport #13962) | 17 | ~90 Go |
| po-2026 | ✅ (cycle 90, ce rapport) | 0 | 0 Go |
| po-2023 | à mesurer | ? | ? |
| po-2024 | à mesurer | ? | ? |
| po-2025 | à mesurer | ? | ? |

## Fichier source de la mesure

Le rapport verbatim ci-dessus est aussi stocké dans le scratchpad du
worker po-2026 pour traçabilité : `scratchpad/junctions_scan_po2026.txt`
(cycle 90).

## Voir aussi

- #13962 — mesure ai-01, Apply à décider par coordinateur
- #2611 — outillage `setup_shared_mathlib.ps1` (CLOSED, ferme)
- #4362 — EPIC parent (3 phases historiques CLOSED)
- #4363, #4364, #4365 — phases 1-2-3 (CLOSED sans application sur aucune machine)
- docs/lean/coordinator-workflow.md — workflow Lean PR discipline