# Mathlib NTFS Junctions — V5 Apply po-2027 (CoursIA-2, c.1731)

Issue : [#16034](https://github.com/jsboige/CoursIA/issues/16034) — Jonction NTFS de search_lean (6,9 Go) sur po-2027 — re-scope 27/09.
EPIC parente : [#4362](https://github.com/jsboige/CoursIA/issues/4362) — Lean : harmoniser Mathlib, mutualiser les checkouts, regrouper les lakes (anti-prolifération).

**Lane** : `myia-po-2027:CoursIA-2`.
**Date** : 2026-10-18 (c.1731).
**Outil** : `scripts/lean/setup_shared_mathlib.ps1 -Mode {Scan,Apply,Apply -Build}`.
**Worktree d'operation** : `D:/dev/CoursIA-2` (clone principal de po-2027, workspace CoursIA-2 — les jonctions NTFS operent au niveau filesystem, pas au niveau git).
**Statut** : **Apply execute, build verification en cours** (BG byfrzf36p, ~600s+ prevu, pool auto-heberge sollicite).

> **Distinction importante** — ce rapport detruit partiellement les hypotheses du precedent doc `docs/lean/junctions-scan-po-2027-CoursIA2.md` (c.1470, 2026-10-07). En 11 jours : (1) la situation a change sur po-2027, (2) le cluster dominant est passe de v4.32.1/520045ab a v4.33.0/db584cd6, (3) 2 jonctions PERIMEE (repeated_games_lean, decision_theory_lean) ont ete re-routees et ne sont plus en conflit, (4) 1 checkout physique (mathlib_examples 0.54 Go) est apparu dans le nouveau groupe dominant. C'est le **drift de portee** que le precedent rapport predisait (« un checkout present dans un autre worktree resterait invisible »).

## Mesure first-hand po-2027 AVANT Apply (c.1731, Scan)

| Mesure | Valeur |
|---|---|
| Projets Lake avec dependance mathlib (git-tracked) | **32** |
| Groupe principal | `leanprover_lean4_v4.33.0-db584cd6` MUTUALISABLE, 24 membres |
| Jonctions PERIMEE (v4.32.1/520045ab) | **7** : game_theory_lean, learning_theory_lean, percolation_lean, kelly_lean, search_lean, conway_lean, argumentation_lean |
| Jonctions fraiches a creer (donneur a designer) | 17 (16 sans checkout + 1 mathlib_examples) |
| Donneur candidat dans groupe db584cd6 | `knot_lean` (10.02 Go, physique) > `mathlib_examples` (0.54 Go, physique) |
| Cache deja pose sur po-2027 | `.mathlib-cache/leanprover_lean4_v4.32.1-520045ab/` (orphelin apres Apply) |
| Total **physique** dans groupe db584cd6 | 10.56 Go (knot_lean + mathlib_examples) |
| Total `.mathlib-cache` AVANT Apply | **11.79 Go** (1 cible : v4.32.1-520045ab) |
| Source de verite | `git ls-files --cached --others --exclude-standard -- '*lake-manifest.json'`, mesure directe via `Get-DirSizeGB` |

## Apply execute (c.1731, `setup_shared_mathlib.ps1 -Mode Apply -Group 'db584cd6'`)

```
=== Apply groupe leanprover_lean4_v4.33.0-db584cd6 (17 a traiter, 7 deja junctionne(s)) ===
Donneur : MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/knot_lean -> D:\dev\CoursIA-2\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\mathlib
  junction : MyIA.AI.Notebooks/Compression/Compression_lean -> leanprover_lean4_v4.33.0-db584cd6 
  junction : MyIA.AI.Notebooks/GameTheory/assignment_lean -> leanprover_lean4_v4.33.0-db584cd6 
  junction REPOINTEE : MyIA.AI.Notebooks/GameTheory/game_theory_lean
     ancienne cible : D:\dev\CoursIA-2\.mathlib-cache\leanprover_lean4_v4.32.1-520045ab\mathlib
     nouvelle cible : D:\dev\CoursIA-2\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\mathlib
  junction : MyIA.AI.Notebooks/GameTheory/minimax_lean -> leanprover_lean4_v4.33.0-db584cd6 
  junction REPOINTEE : MyIA.AI.Notebooks/ML/learning_theory_lean
     ancienne cible : D:\dev\CoursIA-2\.mathlib-cache\leanprover_lean4_v4.32.1-520045ab\mathlib
     nouvelle cible : D:\dev\CoursIA-2\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\mathlib
  junction REPOINTEE : MyIA.AI.Notebooks/Probas/Applications/Percolation/percolation_lean
  junction REPOINTEE : MyIA.AI.Notebooks/QuantConnect/kelly_lean
  junction REPOINTEE : MyIA.AI.Notebooks/Search/search_lean
  junction : MyIA.AI.Notebooks/Sudoku/sudoku_lean -> leanprover_lean4_v4.33.0-db584cd6 
  junction : MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry/geometry_lean -> leanprover_lean4_v4.33.0-db584cd6 
  junction : MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/knot_lean -> leanprover_lean4_v4.33.0-db584cd6 
  junction : MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/serre100_lean -> leanprover_lean4_v4.33.0-db584cd6 
  junction : MyIA.AI.Notebooks/SymbolicAI/Lean/calibration_lean -> leanprover_lean4_v4.33.0-db584cd6 
  junction REPOINTEE : MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean
  junction : MyIA.AI.Notebooks/SymbolicAI/Lean/formal_groups_lean -> leanprover_lean4_v4.33.0-db584cd6 
  junction : MyIA.AI.Notebooks/SymbolicAI/Lean/galois_lean -> leanprover_lean4_v4.33.0-db584cd6 
  junction : MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean -> leanprover_lean4_v4.33.0-db584cd6 
  junction : MyIA.AI.Notebooks/SymbolicAI/Lean/hecke_lean -> leanprover_lean4_v4.33.0-db584cd6 
  junction : MyIA.AI.Notebooks/SymbolicAI/Lean/mathlib_examples -> leanprover_lean4_v4.33.0-db584cd6 (backup conserve)
  junction : MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean -> leanprover_lean4_v4.33.0-db584cd6 
  junction : MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean -> leanprover_lean4_v4.33.0-db584cd6 
  junction : MyIA.AI.Notebooks/SymbolicAI/SmartContracts/erc20_lean -> leanprover_lean4_v4.33.0-db584cd6 
  junction REPOINTEE : MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean
Etat persiste : D:\dev\CoursIA-2\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6\share-state.json
```

- **17 junctions creees** (9 nouveaux + 8 remplacements, dont 7 re-pointages PERIMEE→db584cd6 + 1 donneur qui devient junction).
- **1 backup** preserve (mathlib_examples, avant jonction).
- **Donneur** : `knot_lean` (10.02 Go) — son `.lake/packages/mathlib` a ete deplace vers `.mathlib-cache/leanprover_lean4_v4.33.0-db584cd6/mathlib`, puis re-jonctionne.
- **`share-state.json`** ecrit : source de verite des junctions, persistance cross-session.

## Mesure APRES Apply (c.1731)

| Mesure | Valeur |
|---|---|
| Total `.mathlib-cache` | **21.81 Go** (avant purge du cache orphelin) |
| Cache `leanprover_lean4_v4.33.0-db584cd6` | 10.02 Go (donneur = knot_lean) |
| Cache orphelin `leanprover_lean4_v4.32.1-520045ab` | 11.79 Go (plus aucune jonction ne pointe ici) |
| Espace recuperable apres purge de l'orphelin | **11.79 Go** |
| `distinct_code_sorry` total (avant Apply) | 12 (game_theory_lean: 1, decision_theory_lean: 2, knot_lean: 8, conway_lean: 1) |
| `distinct_code_sorry` total (apres Apply) | **12** (identique, sources `*.lean` non touchees) |
| `code_sorry` total (avant/apres) | 24 / 24 (identique) |
| `naive_sorry` total (avant/apres) | 675 / 675 (identique, prose incluse) |
| Source de verite | `python scripts/lean/count_code_sorry.py --json` (instrument de comptage `distinct_code_sorry`) |

## Verdict interim

**`MIXED`** :
- ✅ **Acceptance 1 (Scan)** : cluster rendu **manifest-identique** sur les 24 membres (pas seulement rev Mathlib — pin-tree complet + lean-toolchain). 7 PERIMEE detectees, 17 nouveaux junctions crees.
- ✅ **Acceptance 2 (Apply)** : jonctions posees, etat persiste dans `share-state.json`.
- ✅ **Acceptance 3 (Anti-regression HARD)** : `distinct_code_sorry` **inchangé** avant/apres (12 -> 12). Les sources `*.lean` ne sont pas touchees par le mouvement filesystem.
- ⏳ **Acceptance 3bis (lake build SUCCESS par membre)** : **en cours** (BG byfrzf36p, ~600s+ prevu, 24 membres a compiler sur le pool auto-heberge). Les 7 lacs PERIMEE passes de v4.32.1 a v4.33.0/db584cd6 peuvent avoir des ruptures API — chaque rollback automatique est possible (`Restore-Member`).
- ⏳ **Acceptance 4 (espace recupere)** : **11.79 Go** a liberer par purge du cache orphelin `v4.32.1-520045ab/` (a faire **apres verification `lake build` reussie** sur les 7 lacs re-pointes, sinon rollback).

## Risques identifies

1. **Rupture API v4.32.1 -> v4.33.0** : les 7 lacs re-pointes (game_theory_lean, learning_theory_lean, percolation_lean, kelly_lean, search_lean, conway_lean, argumentation_lean) utilisaient jusqu'ici Mathlib v4.32.1/520045ab (cible de la jonction perimee) bien que leur manifest declare v4.33.0/db584cd6. Si une API Mathlib a change entre les deux revisions, `lake build` peut casser.
2. **Build pre-empted par pool saturé** : 2538 jobs en queue c.1730, l'auto-heberge peut etre lent. BG byfrzf36p gere le cas, mais une PR signalee avant build SUCCESS **n'a pas** la verification anti-regression complete au sens strict de l'acceptance 3.
3. **Cache orphelin v4.32.1-520045ab = 11.79 Go** : a purger **apres** build SUCCESS sur les 7 lacs re-pointes, sinon perte de la possibilite de rollback.
4. **mimo_lean (6.69 Go, isole)** : manifest divergent (`slt 0b1020a4` ajoute), hors groupe db584cd6 mutualisable. Non touche par l'Apply c.1731 — a traiter dans un cycle futur (EPIC #4362 sous-grain dedie).

## Liens

- Issue : [#16034](https://github.com/jsboige/CoursIA/issues/16034)
- EPIC parente : [#4362](https://github.com/jsboige/CoursIA/issues/4362)
- Outillage : `scripts/lean/setup_shared_mathlib.ps1` (livre par #4363, ferme)
- Convergence Mathlib : #4364 (ferme, 22/23 lakes sur v4.32.1/520045ab au moment de la mesure)
- PR scanner pin-tree identity : #14602 (merged)
- Doc precedent (Scan po-2027, c.1470, 2026-10-07) : `docs/lean/junctions-scan-po-2027-CoursIA2.md` — partiellement contredit par la presente mesure
- `scripts/lean/count_code_sorry.py` (instrument de comptage `distinct_code_sorry`)
- BG id : byfrzf36p (Apply -Build verification en cours, journal `C:\Users\Jesse\AppData\Local\Temp\claude\d--dev-CoursIA-2\6643de94-8aa5-456e-b642-8ca6f07ae12d\tasks\byfrzf36p.output`)
- Source verbatim AVANT/APRES : `git ls-files --cached --others --exclude-standard -- '*lake-manifest.json'` (32 fichiers), `Get-DirSizeGB` (script de mesure)
