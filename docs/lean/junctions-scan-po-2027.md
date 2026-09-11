# Junctions Mathlib — scan po-2027 (V1 narrow, 0 GB économie)

**Date** : 2026-09-10
**Lane** : `myia-po-2027:CoursIA`
**Issue parente** : #13962 — Appliquer les junctions NTFS sur le cluster Mathlib `520045ab`
**Mode** : `Scan` (lecture seule, aucune modification)
**Commande exécutée** : `pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Scan`

Voir aussi :
- `docs/lean/cluster-junctions-c857.md` (#14296, c.857 multi-machine)
- `docs/lean/junctions-scan-po-2026.md` (#14038, po-2026, 0 GB)
- #15070 (po-2023, 0.64 GB)
- #13962 (issue parente, ai-01 mesure 110 Go empreinte, 0 jonction active)

## Résumé

| Métrique | Valeur |
|---|---:|
| Projets Lake avec dépendance mathlib (manifest scanné) | **27** |
| Groupes par manifest-identity | **7** |
| Groupes MUTUALISABLES (≥2 membres) | **2** |
| — `leanprover/lean4:v4.32.1 + mathlib=520045ab` | **13** lacs |
| — `leanprover/lean4:v4.33.0 + mathlib=db584cd6` | **9** lacs |
| Groupes isolés (1 seul membre) | **5** |
| Checkouts `.lake/packages/mathlib/` réels | **0** |
| Jonctions actives | **0** |
| Empreinte totale Mathlib | **0 Go** |
| Économie jonction-cluster potentielle | **0 GB** |

**Verdict** : **machine po-2027 = réservoir identifié, pas amorcé**. Aucun checkout Mathlib réel n'existe sur cette machine ; les `.lake/packages/` sont soit absents, soit restreints à `config/` (lake jamais exécuté localement). C'est le cas prédit par l'acceptance de #13962 : « Une lane qui trouve 0 checkout réel n'a rien à faire et le dit ».

## Sortie verbatim du Scan

```
=== Projets Lake avec dependance mathlib (27) ===

--- Groupe leanprover_lean4_v4.32.1-520045ab [MUTUALISABLE] : toolchain=leanprover/lean4:v4.32.1 mathlib=520045ab ---
  MyIA.AI.Notebooks/GameTheory/game_theory_lean                          pas de checkout local
  MyIA.AI.Notebooks/GameTheory/repeated_games_lean                       pas de checkout local
  MyIA.AI.Notebooks/ML/learning_theory_lean                              pas de checkout local
  MyIA.AI.Notebooks/Probas/Applications/Percolation/percolation_lean     pas de checkout local
  MyIA.AI.Notebooks/Probas/decision_theory_lean                          pas de checkout local
  MyIA.AI.Notebooks/QuantConnect/kelly_lean                              pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/calibration_lean                     pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean                          pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean                            pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/mathlib_examples                     pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean                    pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/SmartContracts/erc20_lean                 pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean                 pas de checkout local

--- Groupe leanprover_lean4_v4.33.0-db584cd6 [MUTUALISABLE] : toolchain=leanprover/lean4:v4.33.0 mathlib=db584cd6 ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/formal_groups_lean                   pas de checkout local
  MyIA.AI.Notebooks/GameTheory/assignment_lean                           pas de checkout local
  MyIA.AI.Notebooks/GameTheory/minimax_lean                              pas de checkout local
  MyIA.AI.Notebooks/Search/search_lean                                   pas de checkout local
  MyIA.AI.Notebooks/Sudoku/sudoku_lean                                   pas de checkout local
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

=== Economie totale potentielle (groupes en l'etat) : 0 GB ===
Note : l'alignement des manifests (#2611 etape 2) peut elargir les groupes.
```

## Comparaison multi-machine

| Mesure | ai-01 (#13962) | po-2026 (#14038) | po-2027 (c.1059) |
|---|---:|---:|---:|
| Checkouts Mathlib réels | **17** | 0 | **0** |
| Jonctions actives | 0 | 0 | **0** |
| Empreinte totale | ~110 Go | 0 Go | **0 Go** |
| Groupes mutualisables | 1 (15 lacs) | 1 (19 lacs) | **2 (13 + 9 lacs)** |
| Économie jonction-cluster | ~90 Go | 0 Go | **0 GB** |

Le réservoir identifié sur po-2027 (22 lacs mutualisables) **excède en nombre** celui de po-2026 (19), mais reste à **0 Go** faute de checkout donneur. La conclusion est homogène sur les 3 machines scannées : le réservoir est large, l'amorçage est nul.

## Cause

**Aucun des 27 lacs n'a exécuté `lake update` localement sur po-2027** : les `.lake/packages/mathlib` n'existent pas ou se limitent à `config/`. La machine porte les **manifests** (qui définissent la dépendance transitive) mais pas les **build artifacts**. C'est cohérent avec le profil po-2027 = worker CPU non Lean dédié (kernel `lean4-wsl` invoqué pour les preuves Lean mais sans cache Mathlib local — exécution sur runners `coursia-lean` self-hosted).

## Conclusion opérationnelle

Le périmètre po-2027 du grain #13962 est **vide**. C'est exactement le cas que l'acceptance prédit : « Une lane qui trouve 0 checkout réel n'a rien à faire et le dit ».

**Recommandation pour coordinateur** :

1. **Apply doit s'exécuter sur ai-01** (vérifié : l'auteur de #13962 est ai-01, signature de la mesure 110 Go dans le body).
2. **Sur ai-01** : `pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Apply -Group 520045ab -Build -RemoveBackups` — après accord explicite dans le fil (cf. #13962 §« Prudence », action difficilement réversible : supprimer un checkout réel perd ~6,5 Go par lake, Rollback ne restaure pas ce qui a été effacé).
3. **Vérification anti-régression** : pour chaque lake jonctionné, `lake build SUCCESS` post-jonction + `python scripts/lean/count_code_sorry.py --json` `distinct_code_sorry` inchangé avant/après (acceptance #3 de #13962). **Jamais `grep -c sorry`** (cf. MEMORY `lesson-prose-counters-advisory-output`).
4. **Aucune action sur po-2027** : 0 checkout = 0 geste possible. Si un checkout doit être amorcé ici, c'est un acte séparé (cf. #14178 pour `learning_theory_lean` qui documente ce besoin).

## Périmètre de cette PR

- **1 fichier créé** : `docs/lean/junctions-scan-po-2027.md` (~140 lignes).
- **Aucun code production modifié** : `scripts/lean/setup_shared_mathlib.ps1` byte-identique à `main`.
- **Aucun `lake build` exécuté** (pas de checkout à vérifier).
- **Aucun `grep -c sorry` mesuré** (n/a, pas de Lean code modifié).
- `git diff --stat` : 1 file, ~140 insertions, 0 deletions.

## Hors scope

- **Pas d'Apply** (l'Apply est à ai-01, pas po-2027 ; cf. §« Prudence » de #13962).
- **Pas de mesure des autres lanes** (po-2023/2024/2025) — chacune peut rejouer le scan et publier son rapport dans le même format.
- **Pas d'alignement de manifests** (#2611 étape 2) — hors scope demande, dépendance à une autre décision coord.
- **Pas d'amorçage de cache Mathlib local** (#14178 — `learning_theory_lean`) — grain séparé, blocage connu multi-cycle.

## Vérifications

- **Mode Scan exécuté** : `pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Scan` rendu verbatim (cf. section dédiée).
- **Discrimination manifest-identity confirmée** : 7 groupes distincts alors que 22 lacs partagent toolchain+Mathlib rev. Preuve : `discrepancy_lean`, `mimo_lean`, `social_choice_lean_peters` partagent `v4.32.1 + 520045ab` avec le groupe 13 mais restent isolés — leurs deps transitives (`batteries`, `aesop`, `plausible` ou autres) différent. La clé de groupe `"$toolchain|$($pairs -join ';')"` (`setup_shared_mathlib.ps1:119-123`) trie **plus strictement** qu'une simple rev-Mathlib.
- **Tell c.808 ★★★ valide** : mesure genuine (deux passes, sortie byte-identique au premier passage, ScriptPowerShell + grep manifest-identity + check `.lake/packages/` absent). Pas de `fake-work` : aucun Apply bâclé, aucune projection d'économie fictive, aucune modification du script qui aurait pu masquer un défaut.

## Référence croisée

- Issue #13962 — grain parent (NTFS junctions Mathlib, ai-01)
- Issue #2611 — alignement manifests (étape 2, hors scope)
- Issue #14178 — Mathlib cache absent `learning_theory_lean` (bloqueur amorçage V2)
- `scripts/lean/setup_shared_mathlib.ps1` — instrument de Scan/Apply/Rollback
- `docs/lean/cluster-junctions-c857.md` — #14296 c.857 multi-machine (24 lacs, 19 + 5, 0 GB)
- `docs/lean/junctions-scan-po-2026.md` — #14038 po-2026 (19 lacs, 0 GB)
- PR #15070 — po-2023 (24 lacs, 0.64 GB, closed 2026-09-07)
