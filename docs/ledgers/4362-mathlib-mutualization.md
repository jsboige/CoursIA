# Ledger #4362 — Mathlib mutualisation, états par machine

Issue parente : [#4362](https://github.com/jsboige/CoursIA/issues/4362) — harmoniser Mathlib, mutualiser les checkouts, regrouper les lakes (anti-prolifération).

Ce ledger porte les **mesures de couverture par machine** de l'état des checkouts Mathlib. Chaque entrée cite la sortie du **scan lu-seul** (`pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Scan`) sur la machine mesurée. Le scan est **lu-seul** (aucune modification) : il inventorie les groupes mutualisables et estime les économies, sans créer de junction. L'**Apply** (junctions + `lake build` par membre + `distinct_code_sorry` avant/après, anti-régression) est le sous-grain de suite, multi-cycles.

---

## c.1783 — po-2023 (`myia-po-2023:CoursIA-2`), 2026-10-26

**Machine** : po-2023, clone `D:\Dev\CoursIA-2`. Le body de l'EPIC (état 2026-10-22) couvre po-2025 et po-2027 ; **po-2023 était hors couverture** — cette entrée l'établit.

**Mesure** (scan lu-seul) :
- **34** projets Lake avec dépendance Mathlib.
- **Économie potentielle : 3.06 GB** (groupe dominant `v4.33.0-db584cd6`, 25 membres, « garder le plus gros comme donneur »).
- **11 junctions PÉRIMÉES** — elles pointent vers l'ancien chemin `D:\Dev\CoursIA\.mathlib-cache\…` (le clone `CoursIA`, **pas** `CoursIA-2`) : liens morts dans ce clone ; un `Apply` frais les repointerait.
- **7 checkouts physiques** dans le groupe dominant (0.51 GB chacun, `kelly_lean` 0.72 GB — donneur le plus gros) — ceux qui porteraient les 3.06 GB si junctionnés (6 × 0.51 GB, le donneur restant physique).
- **2 checkouts physiques de 6.66 GB** isolés sur `v4.32.1-520045ab` (`kls_lean` + `social_choice_lean_peters`) : 13.32 GB physiques, séparés en 2 groupes par une dépendance externe divergente (`SocialChoiceLean`) ; l'alignement des manifests (#2611 étape 2) les fusionnerait 2→1.
- **Collision de groupId** : 3 groupes de manifests distincts partagent le groupId `db584cd6` (écart : dépendance locale `learning_theory_lean` + dépendance externe `slt`) ; aligner les manifests → **1 checkout au lieu de 27**.

**Verdict / portée** : **MESURE** (scan lu-seul), **non Apply**. Aucune espace disque n'est libérée par cette entrée — l'économie 3.06 GB est **potentielle**. Résidu actionnable sur po-2023 : (a) repointer les 11 junctions périmes + junctionner 6 des 7 checkouts physiques du groupe `db584cd6` (Apply + `lake build` par membre + `distinct_code_sorry` avant/après) ; (b) alignement des manifests `db584cd6` (27→1, #2611 étape 2) ; (c) fusion `520045ab` (2×6.66 GB → 1).

Sortie du scan lu-seul (2026-10-26, po-2023, clone `CoursIA-2`) :

```text
=== Projets Lake avec dependance mathlib (34) ===

--- Groupe leanprover_lean4_v4.33.0-db584cd6 [MUTUALISABLE -- revision partagee par 3 groupes] : toolchain=leanprover/lean4:v4.33.0 mathlib=db584cd6 ---
  MyIA.AI.Notebooks/Compression/Compression_lean                         JONCTION PERIMEE -> D:\Dev\CoursIA\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\mathlib
  MyIA.AI.Notebooks/GameTheory/assignment_lean                           checkout physique (0.51 GB)
  MyIA.AI.Notebooks/GameTheory/game_theory_lean                          JONCTION PERIMEE -> D:\Dev\CoursIA\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\mathlib
  MyIA.AI.Notebooks/GameTheory/minimax_lean                              checkout physique (0.51 GB)
  MyIA.AI.Notebooks/ML/learning_theory_lean                              JONCTION PERIMEE -> D:\Dev\CoursIA\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\mathlib
  MyIA.AI.Notebooks/Probas/Applications/Percolation/percolation_lean     JONCTION PERIMEE -> D:\Dev\CoursIA\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\mathlib
  MyIA.AI.Notebooks/Probas/DecisionTheory/decision_theory_lean           JONCTION PERIMEE -> D:\Dev\CoursIA\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\mathlib
  MyIA.AI.Notebooks/QuantConnect/kelly_lean                              checkout physique (0.72 GB)
  MyIA.AI.Notebooks/Search/search_lean                                   checkout physique (0.51 GB)
  MyIA.AI.Notebooks/Sudoku/sudoku_lean                                   JONCTION PERIMEE -> D:\Dev\CoursIA\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\mathlib
  MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry/geometry_lean               JONCTION PERIMEE -> D:\Dev\CoursIA\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\mathlib
  MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/knot_lean                      JONCTION PERIMEE -> D:\Dev\CoursIA\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\mathlib
  MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/riemann200_lean           pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/serre100_lean               pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/calibration_lean                     JONCTION PERIMEE -> D:\Dev\CoursIA\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\mathlib
  MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean                          JONCTION PERIMEE -> D:\Dev\CoursIA\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\mathlib
  MyIA.AI.Notebooks/SymbolicAI/Lean/formal_groups_lean                   checkout physique (0.51 GB)
  MyIA.AI.Notebooks/SymbolicAI/Lean/galois_lean                          JONCTION PERIMEE -> D:\Dev\CoursIA\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\mathlib
  MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean                    checkout physique (0.51 GB)
  MyIA.AI.Notebooks/SymbolicAI/Lean/hecke_lean                           checkout physique (0.51 GB)
  MyIA.AI.Notebooks/SymbolicAI/Lean/mathlib_examples                     pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean                     pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean                    pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/SmartContracts/erc20_lean                 pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean                 pas de checkout local
  => economie potentielle : 3.06 GB (garder le plus gros comme donneur)

--- Groupe leanprover_lean4_v4.25.0-1ccd71f8 [isole] : reference_docs/stable_marriage/upstream pas de checkout local
--- Groupe leanprover_lean4_v4.32.1-520045ab [isole -- revision partagee par 2 groupes] : kls_lean checkout physique (6.66 GB)
--- Groupe leanprover_lean4_v4.32.1-520045ab [isole -- revision partagee par 2 groupes] : social_choice_lean_peters checkout physique (6.66 GB)
--- Groupe leanprover_lean4_v4.33.0-rc1-5eec30bc [isole] : conway_cgt_lean pas de checkout local
--- Groupe leanprover_lean4_v4.33.0-db584cd6 [isole -- revision partagee par 3 groupes] : discrepancy_lean checkout physique (0.51 GB)
--- Groupe leanprover_lean4_v4.33.0-db584cd6 [isole -- revision partagee par 3 groupes] : mimo_lean pas de checkout local
--- Groupe leanprover_lean4_v4.33.1-0df444a3 [isole -- revision partagee par 2 groupes] : formal_logic_lean pas de checkout local
--- Groupe leanprover_lean4_v4.33.1-0df444a3 [isole -- revision partagee par 2 groupes] : differential_lean pas de checkout local
--- Groupe leanprover_lean4_v4.35.0-56a00585 [isole] : torchlean_lean pas de checkout local

=== Economie totale potentielle (groupes en l'etat) : 3.06 GB ===

=== Diagnostic : revision mathlib partagee par plusieurs groupes de manifests ===
  v4.33.0 db584cd6 : 3 groupes de manifests distincts (27 projets) — ecart par dependance locale `learning_theory_lean` (path) + externe `slt [0b1020a4]` ; => 1 checkout au lieu de 27 si les manifests sont alignes (#2611 etape 2)
  v4.32.1 520045ab : 2 groupes de manifests distincts (2 projets) — ecart par dependance externe `SocialChoiceLean [94a4c650]` ; => 1 checkout au lieu de 2
  v4.33.1 0df444a3 : 2 groupes de manifests distincts (2 projets) — ecart par dependances externes divergentes ; => 1 checkout au lieu de 2
AVERTISSEMENT : Collision de groupId : les groupes de manifests distincts d'une meme revision partagent le groupId (cache et share-state.json communs).
Note : l'alignement des manifests (#2611 etape 2) peut elargir les groupes.
```

See #4362
