# Mathlib NTFS Junctions — Scan po-2027 (workspace CoursIA-2)

Issue #13962 — Appliquer les junctions NTFS sur le cluster Mathlib 520045ab (15 lakes, ~90 Go)

**Lane** : `myia-po-2027:CoursIA-2`
**Date mesure** : 2026-09-16 (c.1205)
**Outil** : `scripts/lean/setup_shared_mathlib.ps1 -Mode Scan`
**Worktree scanné** : `D:/dev/CoursIA-2` (clone principal de po-2027, workspace CoursIA-2)
**Statut** : **Scan AVANT Apply** — Apply sur accord explicite (cf prudence de l'issue).

> **Distinction importante** — ce rapport complète (et contredit partiellement) `docs/lean/junctions-scan-po-2027.md` (c.1059, lane `myia-po-2027:CoursIA`, workspace **CoursIA**, date 2026-09-10). Ce dernier rapportait **0 checkout réel** dans un worktree de po-2027 dédié au workspace CoursIA. La présente mesure, depuis **le clone principal `D:/dev/CoursIA-2` (workspace CoursIA-2)**, montre un état radicalement différent : **3 checkouts réels, 9 jonctions actives**. C'est le faux négatif de portée que la note §Portée de l'ancien rapport predisait explicitement (« un checkout présent dans un autre worktree resterait invisible »).

## Mesure first-hand po-2027 (worktree principal `D:/dev/CoursIA-2`)

| Mesure | Valeur |
|---|---|
| Checkouts Mathlib **reels** sur po-2027 | **3** (search_lean + mimo_lean + kelly_lean) |
| Jonctions NTFS **actives** sur po-2027 | **9** (8 v4.32.1 + 1 v4.33.0) |
| Lanes v4.32.1-520045ab jonctionnees | game_theory_lean, repeated_games_lean, learning_theory_lean, percolation_lean, decision_theory_lean, conway_lean, knot_lean, argumentation_lean |
| Lanes v4.33.0-db584cd6 jonctionnees | kelly_lean |
| Lanes v4.33.0-db584cd6 **physiques** | search_lean (6.9 Go), mimo_lean (6.63 Go) |
| Total **physique** non-jonctionne | **~13.5 Go** |
| Cache deja pose sur po-2027 | `.mathlib-cache/leanprover_lean4_v4.32.1-520045ab/` (1 cible — kelly_lean + les 8 du groupe v4.32.1) |

## Groupes identifies par le Scan

### Groupe `leanprover_lean4_v4.32.1-520045ab` [MUTUALISABLE] — 8/8 JUNCTIONED

8 lanes sur 8 manifest-identiques sont **deja** jonctionnees vers
`.mathlib-cache/leanprover_lean4_v4.32.1-520045ab/mathlib`. **Aucun Apply
supplementaire a faire dans ce groupe sur po-2027**.

Liste :
- `MyIA.AI.Notebooks/GameTheory/game_theory_lean`
- `MyIA.AI.Notebooks/GameTheory/repeated_games_lean`
- `MyIA.AI.Notebooks/ML/learning_theory_lean`
- `MyIA.AI.Notebooks/Probas/Applications/Percolation/percolation_lean`
- `MyIA.AI.Notebooks/Probas/decision_theory_lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean`
- `MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean`
- `MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean`

Toutes les junctions pointent verifiees (c.1203 scan) :
`{D:\dev\CoursIA-2\.mathlib-cache\leanprover_lean4_v4.32.1-520045ab\mathlib}`.
Aucun orphelin `v4.31.0-rc1`. Etat sain.

### Groupe `leanprover_lean4_v4.33.0-db584cd6` [MUTUALISABLE / partiellement applique]

| Lane | Statut | Manifest | Note |
|---|---|---|---|
| kelly_lean | **JUNCTIONED** (deja) | 9 packages (Cli, LeanSearchClient, Qq, aesop, batteries, importGraph, mathlib, plausible, proofwidgets) | cible existante |
| search_lean | **physique (6.9 Go)** | 9 packages (**byte-identique a kelly_lean**) | candidat jonction — manifest compatible |
| mimo_lean | **physique (6.63 Go)** | **10 packages** (ajoute `slt 0b1020a4`) | manifest **divergent** — pas jonctionnable tel quel |

**Conclusion search_lean** : le manifeste est **byte-identique** a celui de
kelly_lean. Junctionner search_lean vers la meme cible (vers un nouveau
`.mathlib-cache/leanprover_lean4_v4.33.0-db584cd6/mathlib`) est non
destructif et permet de mutualiser. Gain : **6.9 Go recuperes** sur po-2027.

**Conclusion mimo_lean** : le manifeste inclut `slt 0b1020a4` que les autres
9 lanes du groupe n'ont pas. Soit :
1. mimo_lean et kelly_lean/search_lean divergent en profondeur et la jonction
   est impossible (l'issue #13962 alerte sur ce cas precis — un package
   transitif manquant casse le build) ;
2. soit `slt` est un package **local** (manifest override), pas un pin
   upstream — a verifier dans `lakefile.lean` de mimo_lean ;
3. soit il faut jonctionner mimo_lean vers un cache dedie incluant `slt`.

A investiguer avant Apply.

### Lanes manifest-identique (v4.32.1 ou v4.33.0) **sans checkout local**

| Groupe | Lane | Note |
|---|---|---|
| v4.32.1-520045ab | Search/discrepancy_lean | isole (manifest unique — verifier divergence avec le groupe principal) |
| v4.32.1-520045ab | GameTheory/social_choice_lean_peters | isole (manifest `_peters` diverge des 8 autres — Peters-tier) |
| v4.31.0-rc2-acbd8f07 | GameTheory/conway_cgt_lean | **HORS SCOPE EXPLICIT** cf issue #13962 (Mathlib transitif via `vihdzp/combinatorial-games` ; pin non choisi par nous ; casserait le build cf #6116/#6432) |
| v4.25.0-1ccd71f8 | SymbolicAI/Lean/agent_tests/prover/session_state/reference_docs/stable_marriage/upstream | **HORS SCOPE** cf issue #13962 (fixture tierce, hors scope code-style.md) |
| v4.33.1-0df444a3 | SymbolicAI/Lean/formal_logic_lean | unique pin (4.33.1 != 4.33.0) |
| v4.33.0-db584cd6 | SymbolicAI/Lean/mimo_lean | cf section precedente |

Pas de checkout local = rien a jonctionner sur po-2027, mais les Apply
cibles sur d'autres machines pourraient s'etendre a ces lanes si
manifest-identique.

### Lanes v4.33.0-db584cd6 manifest-identique **sans checkout** (membres potentiels du groupe)

12 lanes (assignment_lean, minimax_lean, sudoku_lean, calibration_lean,
formal_groups_lean, galois_lean, grothendieck_lean, hecke_lean,
mathlib_examples, sensitivity_lean, planning_lean, erc20_lean). Ces lanes
**pourraient** etre jonctionnees vers le meme cache que kelly_lean (et
futur search_lean) **dès qu'elles seront construites pour la premiere
fois** — gain preventif sur ~77 Go.

## Comparaison multi-machine (mise a jour c.1205)

| Mesure | ai-01 (#13962) | po-2023 (#15070) | po-2024 | po-2026 (#14038) | po-2027 CoursIA (c.1059) | po-2027 CoursIA-2 (c.1205) |
|---|---:|---:|---:|---:|---:|---:|
| Checkouts Mathlib reels | **17** | **3** | 22 jonctions posees, store vide | 0 | 0 | **3** |
| Jonctions actives | 0 | 0 | **22** | 0 | **0** | **9** |
| Empreinte totale | ~110 Go | **1,28 Go** | 0 Go — store vide | 0 Go | **0 Go** | **13.5 Go** |
| Groupes mutualisables | 1 (15 lacs) | **2 (13 + 9 lacs)** | **2 (13 + 9 lacs)** | 1 (19 lacs) | **2 (13 + 9 lacs)** | **2 (13 + 9 lacs)** |
| Économie jonction-cluster | ~90 Go | **0,64 Go** | 0 Go (store vide) | 0 Go | **0 GB** | **13.5 Go court terme / ~90 Go futur** |

> **Reconciliation** — la colonne po-2027 CoursIA (c.1059, ancien rapport
> `junctions-scan-po-2027.md`) rapportait 0 checkout reel car elle
> mesurait depuis un worktree de l'autre workspace. La présente mesure
> CoursIA-2 montre l'état du **clone principal**. Les deux rapports
> ensemble documentent l'**état-machine reel de po-2027** : 9 jonctions
> deja actives + 3 checkouts physiques candidats Apply.

## Resume — gain potentiel sur po-2027

| Action | Gain po-2027 | Risque |
|---|---|---|
| Rien (etat actuel) | 0 | aucun |
| Junctionner search_lean (manifest compatible kelly_lean) | **6.9 Go** | faible (manifest byte-identique verifie) |
| Junctionner mimo_lean | **6.63 Go** | **MOYEN** — manifest divergent (`slt` a investiguer) |
| Junctionner les 12 v4.33.0-db584cd6 sans checkout (preventif) | **0 maintenant**, ~77 Go **futur** | nul aujourd'hui (pas de checkout a deplacer) |

**Total court terme** : **6.9 a 13.5 Go recuperes** sur po-2027 seul.
**Total fleet** (generalise a toutes les machines) : **90 Go** cf issue.

## Anti-regression (HARD, bloquant, cf issue #13962 acceptance 3)

Pour chaque Apply :
1. `lake build SUCCESS` **apres** la jonction
2. `python scripts/lean/count_code_sorry.py --json` → champ `distinct_code_sorry`
   inchange avant/apres. **Jamais `grep -c sorry`** (sur-compte la prose ;
   `distinct_code_sorry` est l'instrument canonique, cf MEMORY
   `anti-regression.md` section « Compter les sorry »).
3. Mesure espace **effectivement** recuperee (rapport, pas estimation).

## Prudence — action difficilement reversible

Remplacer un checkout reel par une jonction **supprime** ~6,5 Go dont la
reconstitution coute un `lake exe cache get` + build (des heures par
lake). Mode Rollback du script existe mais ne restaure pas ce qui a ete
efface : il defait le lien. **Scan + rapport AVANT tout Apply**, accord
explicite dans le fil de l'issue.

## Statut Apply sur po-2027

**AUCUN Apply execute ce cycle** — geste = Scan + rapport (cf issue
#13962 prudence : « Faire le Scan et le rapporter AVANT tout Apply »).

Prochaine etape conditionnelle :
1. Accord explicite dans le fil (commentaire repondant a ce rapport) ;
2. Apply sur `search_lean` (manifest compatible, gain 6.9 Go, risque
   faible) ;
3. Investigation `slt 0b1020a4` dans mimo_lean avant tout Apply la-dessus ;
4. Apply sur mimo_lean si investigation OK.

## Verifications

- **Mode Scan execute** : `pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Scan` rendu verbatim dans `c1205_scan_po-2027-coursia2.out`.
- **Discrimination manifest-identity** : 7 groupes distincts (dont 2 MUTUALISABLES et 5 isoles) sur 28 lacs.
- **3 checkouts reels identifies** : search_lean (6.9 Go), mimo_lean (6.63 Go), et kelly_lean (deja junctionne).
- **9 jonctions actives verifiees** : 8 v4.32.1 (toutes pointent vers le cache partage) + 1 v4.33.0 (kelly_lean).
- **Aucun orphelin** v4.31.0-rc1 detecte sur po-2027 (vs etat signale sur po-2024 dans `junctions-scan-po-2024.md`).
- **Tell c.808 ★★★** : mesure genuine (deux passes du script, sortie byte-identique au premier passage).

## References

- Issue #13962 (parent)
- `docs/lean/junctions-scan-po-2027.md` (c.1059, scan du worktree CoursIA — 0 checkout, etat different du clone principal)
- `docs/lean/junctions-scan-po-2024.md` (22 jonctions, store vide — dérive de toolchain sur 11/22)
- `docs/lean/junctions-scan-po-2026.md` (#14038, po-2026, 0 GB)
- #4362 (EPIC parent) · #2611 (outillage `setup_shared_mathlib.ps1`, CLOSED) · #4363 (phase 1-2, CLOSED sans application) · #13146 (reconciliation inventaire GameTheory) · #6116 / #6432 (pin transitif `conway_cgt_lean` exclus)
- MEMORY `lean-warm-mathlib-junction-build.md` (po-2027 junctions warm-Mathlib pattern ; junction vers warm Mathlib d'un lake frere ; `count_sorry --repo` requis)
- MEMORY `lean_kernel_broken.md` (REPL cassé en lean4-wsl mais `lake build` natif OK)
- c.1203 (premier scan po-2027 manuel — 9 jonctions verifiees) ; c.1205 (rapport Scan present, ce document)
