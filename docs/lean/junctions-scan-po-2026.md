# Mathlib NTFS junctions scan — `myia-po-2026` (2026-09-27, c.1221)

**Issue** : #13962 (enfant de #4362)
**Machine** : `myia-po-2026` (worker Lean/QC/SymbolicLearning)
**Script** : `scripts/lean/setup_shared_mathlib.ps1 -Mode Scan` (#2611, ferme depuis 2026-07-03)
**Mode** : Scan (lecture seule, aucune modification)

## TL;DR

**Économie potentielle sur po-2026 : 4,09 GB** (cluster v4.33.0-db584cd6,
23 lacs mutualisables, donneur candidat = `game_theory_lean` à 11,14 GB).
Un lac est déjà JUNCTIONED (`sensitivity_lean`), validant le principe sur cette
machine.

**Mise à jour majeure vs cycle 90 (2026-09-01)** : l'ancien rapport
annonçait **0 GB économie** (aucun checkout local). La situation a
fondamentalement évolué : **14 lacs du cluster `db584cd6` ont depuis acquis un checkout physique** (probablement via `lake exe cache get` durant l'exécution des notebooks en kernel `lean4-wsl` sur WSL `machine-2026`), dont **4 avec Mathlib réellement téléchargé** (GB > 0) — `game_theory_lean` 11,14, `conway_lean` 0,58, `grothendieck_lean` 2,93, `knot_lean` 0,58. Le cluster mutualisable po-2026 existe désormais et l'Apply devient actionnable.

> **Convention de comptage (c.1223, post-relecture Hermes #18020)** : « checkout physique » = `lake-manifest` présent dans `.lake/packages/mathlib/` (peut être 0 GB si seul le manifest est acquis, sans les oleans). « Avec Mathlib téléchargé » = checkout dont la taille dépasse 0 GB (manifest + oleans). Le verbatim liste **14 `checkout physique` dans le cluster `db584cd6`** (4 avec Mathlib téléchargé, 10 à 0 GB) + **1 `JUNCTIONED`** (`sensitivity_lean`) + **1 `checkout physique` hors cluster** (`formal_logic_lean`, 6,69 GB, isolé `v4.33.1-0df444a3`) + **8 `pas de checkout local`**. **Total acquis depuis c.90 = 15 lacs avec checkout, dont 5 avec Mathlib téléchargé.** Le compte « 11 » utilisé dans une première rédaction (cf. cid 5853418531 et version antérieure de cette page) ne dérive pas du verbatim et a été remplacé.

## Sortie verbatim du Scan (2026-09-27, c.1221)

```
=== Projets Lake avec dependance mathlib (29) ===

--- Groupe leanprover_lean4_v4.33.0-db584cd6 [MUTUALISABLE] : toolchain=leanprover/lean4:v4.33.0 mathlib=db584cd6 ---
  MyIA.AI.Notebooks/GameTheory/assignment_lean                           pas de checkout local
  MyIA.AI.Notebooks/GameTheory/game_theory_lean                          checkout physique (11.14 GB)
  MyIA.AI.Notebooks/GameTheory/minimax_lean                              checkout physique (0 GB)
  MyIA.AI.Notebooks/GameTheory/repeated_games_lean                       checkout physique (0 GB)
  MyIA.AI.Notebooks/ML/learning_theory_lean                              checkout physique (0 GB)
  MyIA.AI.Notebooks/Probas/Applications/Percolation/percolation_lean     pas de checkout local
  MyIA.AI.Notebooks/Probas/decision_theory_lean                          checkout physique (0 GB)
  MyIA.AI.Notebooks/QuantConnect/kelly_lean                              checkout physique (0 GB)
  MyIA.AI.Notebooks/Search/search_lean                                   pas de checkout local
  MyIA.AI.Notebooks/Sudoku/sudoku_lean                                   checkout physique (0 GB)
  MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/serre100_lean               pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/calibration_lean                     pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean                          checkout physique (0.58 GB)
  MyIA.AI.Notebooks/SymbolicAI/Lean/formal_groups_lean                   pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/galois_lean                          pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean                    checkout physique (2.93 GB)
  MyIA.AI.Notebooks/SymbolicAI/Lean/hecke_lean                           pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean                            checkout physique (0.58 GB)
  MyIA.AI.Notebooks/SymbolicAI/Lean/mathlib_examples                     checkout physique (0 GB)
  MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean                     JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean                    checkout physique (0 GB)
  MyIA.AI.Notebooks/SymbolicAI/SmartContracts/erc20_lean                 checkout physique (0 GB)
  MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean                 checkout physique (0 GB)
  => economie potentielle : 4.09 GB (garder le plus gros comme donneur)

--- Groupe leanprover_lean4_v4.25.0-1ccd71f8 [isole] : toolchain=leanprover/lean4:v4.25.0 mathlib=1ccd71f8 ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/session_state/reference_docs/stable_marriage/upstream pas de checkout local

--- Groupe leanprover_lean4_v4.31.0-rc2-acbd8f07 [isole] : toolchain=leanprover/lean4:v4.31.0-rc2 mathlib=acbd8f07 ---
  MyIA.AI.Notebooks/GameTheory/conway_cgt_lean                           pas de checkout local

--- Groupe leanprover_lean4_v4.32.1-520045ab [isole] : toolchain=leanprover/lean4:v4.32.1 mathlib=520045ab ---
  MyIA.AI.Notebooks/GameTheory/social_choice_lean_peters                 pas de checkout local

--- Groupe leanprover_lean4_v4.33.0-db584cd6 [isole] : toolchain=leanprover/lean4:v4.33.0 mathlib=db584cd6 ---
  MyIA.AI.Notebooks/Search/discrepancy_lean                              pas de checkout local

--- Groupe leanprover_lean4_v4.33.0-db584cd6 [isole] : toolchain=leanprover/lean4:v4.33.0 mathlib=db584cd6 ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean                            pas de checkout local

--- Groupe leanprover_lean4_v4.33.1-0df444a3 [isole] : toolchain=leanprover/lean4:v4.33.1 mathlib=0df444a3 ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean                    checkout physique (6.69 GB)

=== Economie totale potentielle (groupes en l'etat) : 4.09 GB ===
Note : l'alignement des manifests (#2611 etape 2) peut elargir les groupes.
```

## Première vérification (c.1221, po-2026)

| Mesure | ai-01 (rapport #13962, 2026-09-01) | po-2026 cycle 90 (2026-09-01) | po-2026 c.1221 (2026-09-27) |
|---|---|---|---|
| Checkouts Mathlib réels | 17 | 0 | **15** (+ 1 JUNCTIONED préexistant) — dont 5 avec Mathlib téléchargé |
| Jonctions NTFS actives | 0 | 0 | 1 (`sensitivity_lean`) |
| Taille échantillon checkout | 6,46 Go | N/A | 11,14 GB (donneur = `game_theory_lean`) |
| Empreinte totale checkouts | ~110 Go | 0 Go | ~21,9 GB |
| Cluster homogène `db584cd6` (v4.33.0) | non listé (rev `520045ab` citée) | 19 manifest-only | **23 lacs mutualisables** |
| Économie jonction-cluster | ~90 Go | 0 Go | **4,09 GB** |

## Évolution entre c.90 et c.1221

L'écart entre les deux mesures po-2026 (0 → 15 checkouts physiques, dont 5 avec Mathlib téléchargé) reflète :

1. **Exécution de notebooks** sur po-2026 avec kernel `lean4-wsl` au cours des
   cycles intermédiaires. Plusieurs notebooks Lean (notamment dans
   `SymbolicAI/Lean/`) déclenchent `lake exe cache get` en arrière-plan, ce qui
   popule progressivement les checkouts locaux même sans `lake build` explicite.
2. **Pinnage convergent** : la majorité des lacs se sont alignés sur
   `leanprover/lean4:v4.33.0` + `mathlib=db584cd6`, qui devient le cluster
   majoritaire po-2026.
3. **Premier JUNCTIONED** : `sensitivity_lean` est déjà passé en jonction (cf.
   `docs/lean/junctions-scan-po-2027.md` cycle 1205 qui rapportait aussi
   cette tendance côté po-2027). Le mécanisme fonctionne sur po-2026.

## Conclusion opérationnelle

**L'Apply est désormais actionnable sur po-2026** :

1. **Cluster cible** : `leanprover/lean4:v4.33.0` + `mathlib=db584cd6`,
   23 lacs, donneur candidat = `game_theory_lean` (11,14 GB).
2. **Économie attendue** : 4,09 GB en posant les jonctions sur les
   `checkout physique > 0` (conway_lean 0,58 + grothendieck_lean 2,93 +
   knot_lean 0,58 = ~4,09 GB).
3. **Préconditions respectées** (cf. #13962 § Acceptance) :
   - lake-manifest identique sur tous les membres (cluster MUTUALISABLE) ;
   - toolchain identique (`v4.33.0`) ;
   - `sensitivity_lean` déjà JUNCTIONED valide la procédure.
4. **8 lacs sans checkout local** (`assignment_lean`, `percolation_lean`,
   `search_lean`, `serre100_lean`, `formal_groups_lean`, `galois_lean`,
   `hecke_lean`, `calibration_lean`) — leur premier `lake build` ira chercher
   dans le cache central une fois les jonctions posées, **plafonnant la
   croissance** au lieu d'ajouter +6,46 Go chacun (cf. effet prospectif
   ai-01 #13962 §Mesure).

## Recommandation pour ai-01 / coordinateur

L'auteur de #13962 est sur ai-01. **Décision Apply** :

1. **Scan ai-01** (déjà mesuré #13962) : 17 checkouts / 110 Go / cluster `520045ab`.
2. **Scan po-2026** (ce rapport, c.1223) : **15 checkouts physiques** (5 avec Mathlib téléchargé, 10 à 0 GB manifest-only) / ~22 Go / cluster `db584cd6`, + 1 JUNCTIONED préexistant.
3. **Apply po-2026** : `pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Apply -Group db584cd6 -Build` (sans `-RemoveBackups` au premier essai pour conserver la sécurité anti-régression).
4. **Vérification anti-régression (HARD bloquant)** : pour chaque lake jonctionné, `lake build SUCCESS` post-jonction + `python scripts/lean/count_code_sorry.py --json` `distinct_code_sorry` inchangé avant/après.
5. **Apply ai-01** : décision séparée du coordinateur, scan distinct.

**Aucun Apply n'est lancé par ce rapport.** Le worker po-2026 documente et
rend la main. La décision Apply reste coordinateur (Tell c.1502 strict ★★
fondateur respect).

## Suivi machine-par-machine

| Machine | Scan | Checkouts réels | Jonctions | Économie potentielle |
|---|---|---|---|---|
| ai-01 | ✅ (#13962) | 17 | 0 | ~90 Go (rev `520045ab`) |
| po-2023 | ✅ (#17178) | mesuré | mesuré | mesuré |
| po-2024 | ✅ (#15938) | mesuré | mesuré | mesuré |
| po-2026 | ✅ (c.1221, ce rapport) | **15** | **1** | **4,09 Go** (rev `db584cd6`) |
| po-2027 | ✅ (#16375, c.1205) | mesuré | mesuré | mesuré |

## Fichier source de la mesure

Rapport verbatim aussi stocké dans le scratchpad du worker po-2026 pour
traçabilité : `scratchpad/junctions_scan_po2026_c1221.out`.

## Voir aussi

- #13962 — mesure ai-01, Apply à décider par coordinateur
- #2611 — outillage `setup_shared_mathlib.ps1` (CLOSED, ferme)
- #4362 — EPIC parent (3 phases historiques CLOSED)
- #4363, #4364, #4365 — phases 1-2-3 (CLOSED sans application sur aucune machine)
- docs/lean/cluster-junctions-c857.md — référence cluster
- docs/lean/junctions-scan-po-2023.md — pair machine po-2023
- docs/lean/junctions-scan-po-2024.md — pair machine po-2024
- docs/lean/junctions-scan-po-2027.md — pair machine po-2027
- docs/lean/coordinator-workflow.md — workflow Lean PR discipline
- `docs/lean/junctions-scan-po-2026.md.c1205.archive` — version archive du rapport cycle 90 (preuve de préservation, Tell « Consolider != Archiver »)
