# Mathlib NTFS Junctions — V5 Apply po-2027 (CoursIA-2, c.1731)

Issue : [#16034](https://github.com/jsboige/CoursIA/issues/16034) — Jonction NTFS de search_lean (6,9 Go) sur po-2027 — re-scope 27/09.
EPIC parente : [#4362](https://github.com/jsboige/CoursIA/issues/4362) — Lean : harmoniser Mathlib, mutualiser les checkouts, regrouper les lakes (anti-prolifération).

**Lane** : `myia-po-2027:CoursIA-2`.
**Date** : 2026-10-18 (c.1731).
**Outil** : `scripts/lean/setup_shared_mathlib.ps1 -Mode {Scan,Apply,Apply -Build}`.
**Worktree d'operation** : `D:/dev/CoursIA-2` (clone principal de po-2027, workspace CoursIA-2 — les jonctions NTFS operent au niveau filesystem, pas au niveau git).
**Statut** : **Apply execute ; verification `lake build` CONCLUE** (BG byfrzf36p, sortie 2026-10-18 20:20, exit 4) — **4 SUCCESS / 6 FAILED (rollbackes) / 14 membres non couverts**. La section « Verification `lake build` » plus bas remplace le statut provisoire « en cours » de la premiere version de ce rapport.

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

- **Junctions posees** : la sortie verbatim ci-dessus fait foi — **16** jonctions creees
  (les entrees `junction :`, dont `knot_lean`, le donneur, dont le `.lake/packages/mathlib`
  a ete deplace puis re-jonctionne, et `mathlib_examples`, le seul conserve avec backup),
  **7** re-pointees vers `db584cd6` (les entrees `junction REPOINTEE :`, les jonctions
  PERIMEE), **0** inchangee (aucune entree `junction existante :`) — soit **23** entrees de
  jonction dans la sortie.
- Le total anterieur (« 17 junctions creees (9 nouveaux + 8 remplacements) ») reprenait le
  `17 a traiter` de l'en-tete de l'outil — les membres du groupe *sans* jonction, sur 24
  membres au total (17 + 7 deja jonctionnees) — et ne se raccordait pas aux entrees de la
  sortie : il est retire au profit de la sortie verbatim, qui fait foi.
- L'ecart d'un membre (24 membres declares contre 23 entrees dans la sortie capturee) n'est
  pas explicite par cette sortie : le seul chemin de `setup_shared_mathlib.ps1` qui
  n'imprime rien pour un membre est le skip « backup deja present », dont l'avertissement
  sort sur le flux d'avertissement — hors d'une capture stdout seule. L'etat du groupe apres
  Apply et rollback est mesure par ailleurs (24 declares => 18 jonctions / 6 absents).
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

## Verification `lake build` — resultat CONCLU du BG byfrzf36p (2026-10-18 20:20, exit 4)

Le BG `byfrzf36p` (`setup_shared_mathlib.ps1 -Mode Apply -Build -Group 'db584cd6'`) a **termine** : 10 membres traites, 4 build vert, 6 build rouge avec rollback par membre, puis **arret du run (exit 4)** — les 14 membres restants n'ont pas ete traites. Journal : `tasks/byfrzf36p.output` (11 345 octets, sortie 2026-10-18 20:20).

| Membre | `lake build` | Cause de l'echec |
|---|---|---|
| `Compression/Compression_lean` | SUCCESS | — |
| `GameTheory/assignment_lean` | SUCCESS | — |
| `GameTheory/minimax_lean` | SUCCESS | — |
| `Probas/Applications/Percolation/percolation_lean` | SUCCESS | — |
| `GameTheory/game_theory_lean` | FAILED (rollback) | cibles requises en echec : `SocialChoice.*` (Basic, AMD, MechanismDesign, SortedListCounting), `StableMarriage.*` (GSState, Lattice), `RepeatedGames.Stage`, `CooperativeGames.ConeKernel` (+ variantes `_en`) |
| `ML/learning_theory_lean` | FAILED (rollback) | cibles requises en echec : `PacLearning.*` (BernoulliMGF, Data), `GradientFlow.*` (Plain, Residual), `EffectiveTheory.*` (CircleOfDays, Grokking, InfoBits, Repons), `Perceptron.Data` (+ `_en`) |
| `Probas/DecisionTheory/decision_theory_lean` | FAILED (rollback) | cibles requises en echec : `Coherence.Basic`, `Utility.Basic` (+ `_en`) — `Gittins` compile (12 s, `sorry` preexistant signale, non introduit ici) |
| `QuantConnect/kelly_lean` | FAILED (rollback) | `failed to read file .../mathlib/.lake/build/lib/lean/Mathlib/GroupTheory/GroupAction/Blocks.olean` — **olean manquant dans le cache partage** |
| `Search/search_lean` | FAILED (rollback) | idem (`Blocks.olean.private` manquant dans le cache partage) |
| `Sudoku/sudoku_lean` | FAILED (rollback) | sortie de trace sur `Sudoku.Propagation_en` ; le run s'interrompt la (exit 4) |
| 14 membres restants | NON COUVERTS | run interrompu avant eux (calibration, formal_groups, galois, grothendieck, hecke, sensitivity, serre100, knot_lean, mathlib_examples, conway, geometry, planning, erc20, argumentation) |

**Deux causes distinctes, a ne pas confondre** :

1. **Rupture de cible sur les 7 PERIMEE** (`game_theory_lean`, `learning_theory_lean` — les 2PERIMEE re-pointes qui echouent) : les cibles `SocialChoice.*` / `PacLearning.*` / `EffectiveTheory.*` / `Coherence.Basic` / `Utility.Basic` existaient sous Mathlib **v4.32.1/520045ab** et ne sont pas disponibles sous **v4.33.0/db584cd6** ⇒ le **risque n°1** de la premiere version de ce rapport est **materialise**, et il ne se resume pas a une hypothese de rupture d'API : c'est une **difference de jeu de cibles** entre les deux revisions.
2. **Defaut d'infrastructure du cache partage** (`kelly_lean`, `search_lean`) : le cache `leanprover_lean4_v4.33.0-db584cd6` est **valide** (rev `db584cd6d46c92f209a44c0f1c829460d327499d`, reutilise tel quel) mais son **arbre de build Mathlib est incomplet** (`Blocks.olean` / `Blocks.olean.private` absents) ⇒ les membres qui besoin de ce module echouent sur un **artefact de cache manquant**, pas sur une source cassee. `decision_theory_lean` et `sudoku_lean` sont dans un cas tiers (cibles en echec / run interrompu).

**Etat reel du groupe, mesure le 2026-10-19 sur le disque (hors BG)** — 24 membres declares dans `share-state.json`, **18 jonctions + 6 absents** :

| Etat | Nombre | Membres |
|---|---|---|
| Jonction sur `db584cd6` (mutualisation active) | **18** | les 4 SUCCESS, les 14 non couverts |
| **Rollback — ni jonction ni copie physique** (`.lake/packages/mathlib` **absent**) | **6** | game_theory_lean, learning_theory_lean, decision_theory_lean, kelly_lean, search_lean, sudoku_lean |
| Cache orphelin `v4.32.1-520045ab` | 11,79 Go | toujours present, **toujours referenced par personne** |

Le rollback par membre (`Restore-Member`) **retire la jonction et ne restaure une copie physique que si un backup existe** (`hadBackup`). Les 6 membres en echec etaient `hadBackup: false` (leur mathlib physique avait ete deplace vers le cache partage lors de l'Apply) ⇒ apres rollback, `Restore-Member` **ne restaure rien** et le membre se retrouve **sans Mathlib du tout** : un `lake build` y re-telechargera Mathlib selon son manifest, et la mutualisation n'est pas active pour eux. Le rollback n'est donc **pas** un retour a l'etat anterieur pour ces 6 — c'est un etat tiers, a traiter.

**Defaut constate au passage** : `share-state.json` continue de declarer **24 membres** alors que 6 ont ete rollbackes. La cause est dans la fusion de l'etat (`Invoke-Apply`, etape 4) : `$merged = @($existing) + @($stateMembers)` groupe par `relPath` et garde le dernier element de chaque groupe — un membre **retire** de `$stateMembers` (rollback) mais present dans `$existing` (etat charge avant la boucle) se retrouve **reintroduit**. Consequence : un `-Mode Rollback` ou `-Mode Verify` ulterieur repartira d'une liste qui ne correspond plus au disque. Suivi : issue de suivi nommee (voir « Suite »).

## Suite (ordonnee)

1. **Rebuilder les artefacts Mathlib du cache partage** (`Blocks.olean` / `Blocks.olean.private` manquants) avant tout nouvel essai — sans cela, kelly/search/sudoku echoueront de la meme facon.
2. **Rejouer `lake build`** sur les 6 rollbackes **puis** sur les 14 non couverts, dans un BG unique qui ne s'interrompt pas au premier echec (le run actuel s'arrete a exit 4 et perd les 14 derniers).
3. **Statuer sur les 2 PERIMEE encore re-pointes et non verifies** (`conway_lean`, `argumentation_lean`) : ils sont sur `db584cd6` sans build vert — meme cause que game_theory/learning_theory a confirmer.
4. **Ne pas purger** le cache orphelin `v4.32.1-520045ab` (11,79 Go) : la condition posee par la premiere version (build vert sur les 7 re-pointes) n'est **pas** remplie, et c'est ce cache qui reste la seule voie de retour arriere pour les 6 rollbackes.
5. **Corriger l'outillage** : `share-state.json` doit etre reecrit a l'etat reel apres rollback (cf. issue de suivi).

## Verdict revise (c.1787, 2026-10-19)

**`MIXED` — verdict sur donnees CONCLUES (BG byfrzf36p, 2026-10-18 20:20)** :
- ✅ **Acceptance 1 (Scan)** : cluster rendu **manifest-identique** sur les 24 membres (pas seulement rev Mathlib — pin-tree complet + lean-toolchain). 7 PERIMEE detectees, 16 jonctions creees, 7 re-pointees. *Reste vrai : c'est la construction du groupe (par manifest), pas un build par membre.*
- ✅ **Acceptance 2 (Apply)** : jonctions posees, etat persiste dans `share-state.json` — **avec une reserve** : le fichier d'etat declare 24 membres alors que 6 ont ete rollbackes (cf. « Defaut constate au passage »).
- ✅ **Acceptance 3 (Anti-regression HARD)** : `distinct_code_sorry` **inchangé** avant/apres (12 -> 12). Les sources `*.lean` ne sont pas touchees par le mouvement filesystem — ni par les rollbacks, qui ne portent que sur `.lake/packages/mathlib`.
- ⛔ **Acceptance 3bis (lake build SUCCESS par membre)** : **NON TENU en l'etat** — **4 SUCCESS sur 10 membres traites** (24 membres au groupe), **6 FAILED** avec rollback, **14 non couverts** (run interrompu, exit 4). Le risque de rupture v4.32.1 -> v4.33.0 est **materialise** sur `game_theory_lean` et `learning_theory_lean` ; `kelly_lean` et `search_lean` echouent sur un **artefact de cache manquant** (cause infrastructure, distincte). 7 des 24 membres restent **re-pointes et non verifies** (dont `conway_lean` et `argumentation_lean`, eux aussi PERIMEE).
- ⛔ **Acceptance 4 (espace recupere)** : **11.79 Go NON liberes** — la purge du cache orphelin `v4.32.1-520045ab/` reste **interdite** tant que le build vert sur les 7 re-pointes n'est pas etabli (condition non remplie) : c'est la seule voie de retour arriere pour les 6 rollbackes.

## Risques identifies

1. **Rupture v4.32.1 -> v4.33.0 — MATERIALISEE (mesure BG byfrzf36p, 2026-10-18)** : les 7 lacs re-pointes (game_theory_lean, learning_theory_lean, percolation_lean, kelly_lean, search_lean, conway_lean, argumentation_lean) utilisaient jusqu'ici Mathlib v4.32.1/520045ab (cible de la jonction perimee) bien que leur manifest declare v4.33.0/db584cd6. Sur les 2 PERIMEE effectivement verifies (`game_theory_lean`, `learning_theory_lean`), le build **echoue** : les cibles `SocialChoice.*`, `StableMarriage.*`, `RepeatedGames.Stage`, `CooperativeGames.ConeKernel`, `PacLearning.*`, `GradientFlow.*`, `EffectiveTheory.*`, `Perceptron.Data` ne sont pas disponibles sous v4.33.0/db584cd6. Ce n'est donc pas une hypothese : c'est une **difference de jeu de cibles** entre les deux revisions, qui demande une decision de fond (adapter les sources, ou garder v4.32.1 pour ces membres) — pas un contournement.
2. **Artefacts de build incomplets dans le cache partage** : le cache `db584cd6` est valide (rev `db584cd6d46c92f209a44c0f1c829460d327499d`) mais son arbre de build Mathlib est **incomplet** (`Mathlib/GroupTheory/GroupAction/Blocks.olean` et `.olean.private` absents) ⇒ `kelly_lean` et `search_lean` echouent sur un artefact manquant, pas sur une source. Cause infrastructure distincte de la rupture de cibles, a traiter en amont de tout nouveau run.
3. **Build pre-empted par pool saturé** : 2538 jobs en queue c.1730, l'auto-heberge peut etre lent. **Le BG a bien demarre, mais son run s'est arrete en exit 4 au 10e membre** ⇒ 14 membres n'ont pas ete traites. Le defaut operationnel n'est donc pas seulement la saturation : le run **ne continue pas apres un echec** et perd la queue de verification. A corriger avant de rejouer (cf. « Suite » et l'issue de suivi).
4. **Cache orphelin v4.32.1-520045ab = 11.79 Go** : a purger **apres** build SUCCESS sur les 7 lacs re-pointes, sinon perte de la possibilite de rollback. **Condition non remplie a ce jour** ⇒ purge interdite ; c'est en outre la seule voie de retour arriere pour les 6 membres rollbackes.
5. **Rollback partiel — 6 membres sans Mathlib** : `Restore-Member` retire la jonction et ne restaure une copie physique que si un backup existe (`hadBackup`). Les 6 membres en echec sont `hadBackup: false` ⇒ apres rollback, `.lake/packages/mathlib` est **absent** (mesure du 2026-10-19 : 18 jonctions / 6 absents / 0 physique). Ils ne sont ni mutualises ni fonctionnels : `lake build` y re-telechargera Mathlib depuis le reseau. Le rollback **n'est pas** un retour a l'etat anterieur pour ces membres.
6. **`share-state.json` desynchronise du disque** : le fichier declare 24 membres alors que 6 sont rollbackes (cause : la fusion `$existing` + `$stateMembers` de `Invoke-Apply` reintroduit un membre retire de `$stateMembers` s'il figure dans l'etat charge avant la boucle). Un `-Mode Rollback` ou `-Mode Verify` ulterieur repartira d'une liste non conforme au disque. Issue de suivi nommee.
7. **mimo_lean (6.69 Go, isole)** : manifest divergent (`slt 0b1020a4` ajoute), hors groupe db584cd6 mutualisable. Non touche par l'Apply c.1731 — a traiter dans un cycle futur (EPIC #4362 sous-grain dedie).

## Liens

- Issue : [#16034](https://github.com/jsboige/CoursIA/issues/16034)
- EPIC parente : [#4362](https://github.com/jsboige/CoursIA/issues/4362)
- Outillage : `scripts/lean/setup_shared_mathlib.ps1` (livre par #4363, ferme)
- Convergence Mathlib : #4364 (ferme, 22/23 lakes sur v4.32.1/520045ab au moment de la mesure)
- PR scanner pin-tree identity : #14602 (merged)
- Doc precedent (Scan po-2027, c.1470, 2026-10-07) : `docs/lean/junctions-scan-po-2027-CoursIA2.md` — partiellement contredit par la presente mesure
- `scripts/lean/count_code_sorry.py` (instrument de comptage `distinct_code_sorry`)
- BG id : byfrzf36p — **conclu** (Apply -Build, sortie 2026-10-18 20:20, exit 4), journal `C:\Users\Jesse\AppData\Local\Temp\claude\d--dev-CoursIA-2\6643de94-8aa5-456e-b642-8ca6f07ae12d\tasks\byfrzf36p.output` (11 345 octets)
- Etat du groupe mesure le 2026-10-19 (hors BG) : `Get-Item` sur les 24 `.lake/packages/mathlib` de `share-state.json` ⇒ **18 jonctions / 6 absents / 0 physique** ; caches `v4.32.1-520045ab` = 11,79 Go, `v4.33.0-db584cd6` = 10,02 Go (mesure recursive, identique aux valeurs de l'Apply)
- Source verbatim AVANT/APRES : `git ls-files --cached --others --exclude-standard -- '*lake-manifest.json'`, `Get-DirSizeGB` (script de mesure)
