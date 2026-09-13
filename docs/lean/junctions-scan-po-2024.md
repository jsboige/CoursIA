# Junctions Mathlib — scan po-2024 (V2, worktree principal) : 22 jonctions vivantes vers un store VIDE

**Date** : 2026-09-13
**Lane** : `myia-po-2024:CoursIA`
**Issue parente** : #13962 — Appliquer les junctions NTFS sur le cluster Mathlib `520045ab`
**Mode** : `Scan` (lecture seule, aucune modification) + organe dédié `check_mathlib_cache.py`
**Commandes exécutées** :
- `pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Scan` depuis `C:\dev\CoursIA` (worktree **principal**)
- `python scripts/lean/check_mathlib_cache.py`

Voir aussi :
- `docs/lean/cluster-junctions-c857.md` (#14296, c.857 — **V1 po-2024, worktree frais**)
- `docs/lean/junctions-scan-po-2027.md` (#15507/#15577 — tableau multi-machine)
- `docs/lean/junctions-scan-po-2026.md` (#14038, po-2026, 0 GB)
- #15070 (po-2023, 0.64 GB) · #13962 (issue parente)

## Résumé

Le tirage de cycle a rendu #13962 ; ma lane y portait un claim du **2026-09-05** (« scan actualisé po-2024, le V1 du 2026-09-02 est périmé ») resté **sans livraison** — aucun `docs/lean/junctions-scan-po-2024.md` n'existait sur `main`. Ce rapport le solde, et le verdict est plus fort qu'un simple rafraîchissement.

| Métrique | V1 (#14296, worktree **frais**) | V2 (ce rapport, worktree **principal**) |
|---|---:|---:|
| Projets Lake portant `mathlib` (manifest scanné) | 24 | **28** |
| Groupes par manifest-identity | 6 | 9 |
| Groupes MUTUALISABLES (≥2 membres) | 1 (19 lacs) | **2 (13 + 9 lacs)** |
| Lacs **`JUNCTIONED`** | **0** | **22** |
| Checkouts physiques vus par le Scan | 0 | 0 |
| Oleans Mathlib **atteignables** (organe dédié) | non mesuré | **0 / 22** |
| Économie « potentielle » rendue par le Scan | 0 GB | **0 GB** (métrique aveugle ici) |

**Verdict** : le V1 n'était pas seulement *périmé* — il était **inversé**. po-2024 n'est pas la machine « qui trouve 0 checkout réel et n'a rien à faire » prévue par l'acceptance de #13962 : elle porte un cluster de jonctions **appliqué le 2026-08-30**, dont le **store partagé est vide** et dont **11 des 22 membres ont migré de toolchain sans que leur jonction soit repointée**. Tous les organes consultés rendent pourtant « 0 GB », c'est-à-dire la signature exacte d'une machine sans travail.

## 1. Ce qui a été mesuré, et par quel instrument

| # | Fait | Instrument | Résultat |
|---|---|---|---|
| 1 | 22 jonctions NTFS vivantes | `fsutil reparsepoint query` | balise `0xa0000003` (« Substitut de nom / Point de montage »), échantillon vérifié sur 2 lacs |
| 2 | Toutes vers **un seul** store | `Get-Item -Force` → `LinkType`/`Target` | 22 → `C:\dev\CoursIA\.mathlib-cache\leanprover_lean4_v4.32.1-520045ab\mathlib` |
| 3 | Le store est **vide** | `[System.IO.Directory]::GetFileSystemEntries` | **0 entrée** ; `EnumerateFiles` long-path → **0 fichier** |
| 4 | …et **pas** une jonction déguisée | `Get-Item` sur le store | `Attributes: Directory`, `LinkType` **vide** → répertoire réel vide, non un lien non traversé |
| 5 | Le contenu est absent **à travers** la jonction | énumération `\\?\` sur 4 lacs (dont le donneur) | `entrees=0`, `lakefile.lean`=**False**, `Mathlib/`=**False** |
| 6 | Organe canonique | `python scripts/lean/check_mathlib_cache.py` | `mathlib ok: 0 \| froid: 22 \| partiel: 0 \| caches physiques distincts: 1` |
| 7 | Forensics de l'Apply | `.mathlib-cache/leanprover_lean4_v4.32.1-520045ab/share-state.json` | `createdAt 2026-08-30T04:08:54+02:00`, **19 membres**, donneur `SymbolicAI/Tweety/argumentation_lean`, 3 membres `hadBackup: true` |
| 8 | Backups jamais libérés | `Get-ChildItem` filtré `*.bak-2611` | **3** : `game_theory_lean` (**9 064** fichiers), `repeated_games_lean` (**8 833**), `knot_lean` (**9 114**) |

Les points 3 et 5 sont ceux qui écartent le piège documenté par `check_mathlib_cache.py` (un `0` rendu par `find`/`islink` sur une jonction **saine** ne prouve rien). Ici le `0` est mesuré sur le **chemin résolu** (point 3 : répertoire réel, `LinkType` vide) **et** confirmé par l'organe qui traverse les jonctions (point 6, `realpath`+`walk`).

## 2. Dérive de toolchain — 11 des 22 jonctions visent la mauvaise rev

Les 19 membres enregistrés par l'Apply du 2026-08-30 ont tous été groupés sous `leanprover_lean4_v4.32.1-520045ab`. Re-mesure des `lean-toolchain` et des `lake-manifest.json` **courants** :

| Lac | `lean-toolchain` | manifest `mathlib.rev` | Jonction vers | Cohérent ? |
|---|---|---|---|---|
| `GameTheory/assignment_lean` | `v4.33.0` | `db584cd6…` | cache `v4.32.1`/`520045ab` | **non** |
| `GameTheory/minimax_lean` | `v4.33.0` | `db584cd6…` | cache `v4.32.1`/`520045ab` | **non** |
| `Search/search_lean` | `v4.33.0` | `db584cd6…` | cache `v4.32.1`/`520045ab` | **non** |
| `Sudoku/sudoku_lean` | `v4.33.0` | `db584cd6…` | cache `v4.32.1`/`520045ab` | **non** |
| `SymbolicAI/Lean/calibration_lean` | `v4.33.0` | `db584cd6…` | cache `v4.32.1`/`520045ab` | **non** |
| `SymbolicAI/Lean/galois_lean` | `v4.33.0` | `db584cd6…` | cache `v4.32.1`/`520045ab` | **non** |
| `SymbolicAI/Lean/grothendieck_lean` | `v4.33.0` | `db584cd6…` | cache `v4.32.1`/`520045ab` | **non** |
| `SymbolicAI/Lean/mathlib_examples` | `v4.33.0` | `db584cd6…` | cache `v4.32.1`/`520045ab` | **non** |
| `SymbolicAI/Lean/sensitivity_lean` | `v4.33.0` | `db584cd6…` | cache `v4.32.1`/`520045ab` | **non** |
| `SymbolicAI/Planners/planning_lean` | `v4.33.0` | `db584cd6…` | cache `v4.32.1`/`520045ab` | **non** |
| `SymbolicAI/SmartContracts/erc20_lean` | `v4.33.0` | `db584cd6…` | cache `v4.32.1`/`520045ab` | **non** |

Les 11 autres (8 du groupe `v4.32.1` + 3 isolés) sont **cohérents** avec leur cible.

**Lecture** : au 2026-08-30 ces 11 lacs étaient sur `v4.32.1`/`520045ab` (d'où leur présence dans les 19 membres du même `GroupKey`) ; ils ont **migré depuis** vers `v4.33.0`/`db584cd6` — manifests et `lean-toolchain` mis à jour, **jonction non repointée**. Le store `leanprover_lean4_v4.33.0-db584cd6` existe (`New-Item` d'un cache groupé) et est **vide lui aussi**.

Ce n'est pas un défaut de l'outil : `Invoke-Apply` (l.233) écarte d'emblée les membres `IsJunction` d'un nouveau traitement de groupe (`$members = @($g.Group | Where-Object { -not $_.IsJunction })`), donc un lac jonctionné **reste** sur la cible de son premier Apply même si son manifest a bougé. Le drift n'a pas de détecteur dédié.

**Origine datée de la dérive** : la PR **#15033** (`feat(lean,#14773): bump calibration_lean vers Lean/Mathlib 4.33.0`, lane `myia-po-2024:CoursIA-2`, mergée 2026-09-09) a fait passer `calibration_lean` — l'un des 11 lacs ci-dessus — de `v4.32.1`/`520045ab` à `v4.33.0`/`db584cd6`. Elle a mis à jour `lean-toolchain` et `lake-manifest.json` sans toucher à `.lake/packages/mathlib`, qui est gitignore et n'apparaît donc dans aucun diff. C'est exactement le geste qui fabrique la ligne 5 du tableau ; les 10 autres lacs ont suivi le même chemin lors de la migration 4.33.0.

## 3. Cause du store vide

`Invoke-Apply` **déplace** le checkout physique du donneur dans le store : `Move-Item $donor.MathlibDir -Destination $cacheMathlib` (l.254). Le donneur enregistré est `argumentation_lean` et il **n'a pas** de `.bak-2611` — cohérent avec la branche donneur (déplacé, jamais sauvegardé). Le store correspondant est aujourd'hui **vide**.

Autrement dit : le contenu a été **déplacé dans le store le 2026-08-30, puis a disparu**. Ce que la mesure établit : le store est vide (points 3/5/6). Ce qu'elle n'établit **pas** : *qui* l'a vidé. Aucun script du dépôt ne purge ce chemin (`grep` borné `scripts/` + `.github/` : seules occurrences = l'outil lui-même et `check_mathlib_cache.py`) — la cause est **hors dépôt** ou antérieure à l'historique consultable. `.mathlib-cache/` est gitignore (`.gitignore:932`), donc l'état n'apparaît dans **aucun** artefact versionné ni en CI. Le disque `C:` est sous pression (127,9 Go libres sur ~930 Go), ce qui rend une purge de récupération d'espace l'hypothèse principale — **hypothèse, non mesurée**.

## 4. Angle mort de l'instrument (et proposition)

`Invoke-Scan` ne calcule l'économie que lorsque `$sizes.Count -ge 2`, c'est-à-dire **au moins deux checkouts physiques** dans le groupe (l.179) ; `JUNCTIONED` est un libellé **terminal** (l.170), sans contrôle de la cible. Conséquence mesurée :

- un cluster **appliqué et cassé** rend `=== Economie totale potentielle : 0 GB ===`, **exactement** comme une machine qui n'a rien à faire ;
- le V1 a de plus scanné un **worktree frais** — `$RepoRoot = git rev-parse --show-toplevel` (l.70), donc la mesure ne voit que le worktree courant. C'est le faux négatif de portée que #15568/#15577 a nommé **après** que le V1 (#14296) l'ait produit.

**Proposition** (hors périmètre de cette PR, grain `guard`/`tooling` à dispatcher) : donner à `Invoke-Scan` trois états au lieu d'un — `JUNCTION-OK` / `JUNCTION-COLD` / `JUNCTION-MISMATCH` — en résolvant la cible (`realpath`) et en comparant le `rev8` du manifest à celui du nom du store, plus un comptage d'oleans. `check_mathlib_cache.py` porte déjà les primitives (`MATHLIB_OLEAN_FLOOR = 1000`) ; l'y brancher éviterait de réécrire l'instrument.

## 5. Correction du tableau multi-machine

`docs/lean/junctions-scan-po-2027.md` porte une ligne po-2024 reprise de #14296 **sans re-mesure** (son §« Provenance des colonnes » le dit explicitement). Re-mesurée :

| Mesure | Ancienne ligne (reprise de #14296) | Re-mesure (ce rapport) |
|---|---:|---:|
| Checkouts Mathlib réels | 0 | 0 (vus par le Scan) + **2 réels hors découverte du script** (voir §6) |
| Jonctions actives | 0 | **22** |
| Empreinte totale | 0 Go | 0 Go de contenu **atteignable** (store vide) |
| Groupes mutualisables | 1 (19 lacs) | **2 (13 + 9 lacs)** |
| Économie jonction-cluster | 0 Go | 0 Go récupérable **en l'état** |

La correction est portée dans la même PR.

## 6. Deux angles morts de découverte, notés au passage

- `GameTheory/cooperative_games_lean` et `GameTheory/social_choice_lean` portent un `.lake/packages/mathlib` **réel** (~9 000 fichiers chacun) mais **absent des 28 projets** du Scan : leurs `lake-manifest.json` ne sont pas suivis par git (`git ls-files --error-unmatch` → *did not match any file(s) known to git*), or `Get-LeanProjects` découvre par `git ls-files` (l.97). Le Scan ne les voit donc pas — c'est un trou de découverte, pas une absence.
- Constaté sans être expliqué : `conway_lean` figure parmi les 19 membres de `share-state.json` mais son `.lake/packages/mathlib` **n'existe plus** (le Scan le classe « pas de checkout local »). Une jonction a donc été retirée à un moment non daté.

## 7. Hors scope

- **Aucun `Apply`** — gaté par le §« Prudence » de #13962 (« n'appliquer qu'après accord explicite dans ce fil »), et l'action est ici **difficilement réversible**.
- **Aucune chirurgie de jonction** (retrait de lien, restauration de backup) : machine **partagée**, état produit par l'Apply d'une autre session le 2026-08-30 → signalé, routé au coordinateur (§Recommandation).
- **Aucun `lake build`** délibérément : l'organe lui-même prescrit un build réel avant de conclure à une purge, mais un build à froid sur un store vide déclencherait un `lake update` / `cache get` (~6,5 Go par lac) sur une machine sous pression disque. Le fait structurel qui porte la conclusion est l'**absence de `lakefile.lean` à travers la jonction** (point 5), pas un build.
- **Pas d'alignement de manifests** (#2611 étape 2) · **pas de re-mesure des autres lanes**.

## 8. Recommandation (coordinateur)

1. **Ne pas relancer `Apply` en l'état** : le store vide n'offre aucun donneur, et `Invoke-Apply` saute le groupe faute de checkout physique à promouvoir (l.246-249) — mais la branche `Cache existant reutilise` (l.255) réutiliserait le store **vide**, ce qui reproduirait l'état actuel.
2. **Trancher d'abord la survie du store** : le contenu doit être restauré (`lake exe cache get` par groupe, ou re-checkout d'un donneur) **avant** toute nouvelle pose de jonction.
3. **Traiter les 3 backups séparément** : `game_theory_lean`, `repeated_games_lean`, `knot_lean` portent un `.bak-2611` physique — un `Rollback` sur ces membres est **réversible** et ne dépend d'aucun donneur. C'est le seul geste sûr disponible aujourd'hui.
4. **Repointer les 11 lacs en dérive** après restauration (`v4.33.0`/`db584cd6` → store `leanprover_lean4_v4.33.0-db584cd6`), sans quoi ils jonctionneront vers la mauvaise rev.
5. **Dispatcher l'angle mort de l'instrument** (§4) : tant que `Scan` ne distingue pas `JUNCTION-COLD`, aucune des cinq machines de la série ne peut alerter sur cet état.

## Vérifications

- **Mode Scan exécuté** depuis le worktree **principal** `C:\dev\CoursIA` ; sortie reprise verbatim ci-dessous.
- **Organe dédié exécuté** : `check_mathlib_cache.py` → `mathlib ok: 0 | froid: 22 | caches physiques distincts: 1` (exit 0, advisory).
- **Discrimination manifest-identity** : 9 groupes alors que 20 lacs partagent `toolchain + mathlib rev` — `discrepancy_lean`, `mimo_lean`, `social_choice_lean_peters` partagent `v4.32.1 + 520045ab` avec le groupe 9 et restent **isolés** (deps transitives différentes). Clé de groupe `"$toolchain|$($pairs -join ';')"` (`setup_shared_mathlib.ps1:119-123`).
- **Aucune écriture** : `git status` du worktree propre ; aucun `Apply`, aucun `Rollback`, aucun `lake build`.
- **Chiffres de fichiers** (9 064 / 8 833 / 9 114) : comptés par deux méthodes indépendantes donnant le même résultat (`Get-ChildItem -Recurse` et `Directory.EnumerateFiles` long-path). Les tailles **en Go** ne sont pas revendiquées : elles ne sont pas mesurables de façon fiable au-delà de 260 caractères de chemin sur cette machine — limitation que le script documente lui-même (`Remove-DirRobust`, l.194-195).

## Sortie verbatim du Scan (worktree principal)

```
=== Projets Lake avec dependance mathlib (28) ===

--- Groupe leanprover_lean4_v4.33.0-db584cd6 [MUTUALISABLE] : toolchain=leanprover/lean4:v4.33.0 mathlib=db584cd6 ---
  MyIA.AI.Notebooks/GameTheory/assignment_lean                           JUNCTIONED
  MyIA.AI.Notebooks/GameTheory/minimax_lean                              JUNCTIONED
  MyIA.AI.Notebooks/Search/search_lean                                   JUNCTIONED
  MyIA.AI.Notebooks/Sudoku/sudoku_lean                                   JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/calibration_lean                     JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/formal_groups_lean                   pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/galois_lean                          JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean                    JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/hecke_lean                           pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/mathlib_examples                     JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean                     JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean                    JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/SmartContracts/erc20_lean                 JUNCTIONED

--- Groupe leanprover_lean4_v4.32.1-520045ab [MUTUALISABLE] : toolchain=leanprover/lean4:v4.32.1 mathlib=520045ab ---
  MyIA.AI.Notebooks/GameTheory/game_theory_lean                          JUNCTIONED
  MyIA.AI.Notebooks/GameTheory/repeated_games_lean                       JUNCTIONED
  MyIA.AI.Notebooks/ML/learning_theory_lean                              JUNCTIONED
  MyIA.AI.Notebooks/Probas/Applications/Percolation/percolation_lean     JUNCTIONED
  MyIA.AI.Notebooks/Probas/decision_theory_lean                          JUNCTIONED
  MyIA.AI.Notebooks/QuantConnect/kelly_lean                              JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean                          pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean                            JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean                 JUNCTIONED

--- Groupe leanprover_lean4_v4.25.0-1ccd71f8 [isole] : ...  (stable_marriage/upstream : pas de checkout local)
--- Groupe leanprover_lean4_v4.31.0-rc2-acbd8f07 [isole] : ... (conway_cgt_lean : pas de checkout local)
--- Groupe leanprover_lean4_v4.32.1-520045ab [isole] : ...     (discrepancy_lean : JUNCTIONED)
--- Groupe leanprover_lean4_v4.32.1-520045ab [isole] : ...     (mimo_lean : JUNCTIONED)
--- Groupe leanprover_lean4_v4.32.1-520045ab [isole] : ...     (social_choice_lean_peters : JUNCTIONED)
--- Groupe leanprover_lean4_v4.33.1-0df444a3 [isole] : ...     (formal_logic_lean : pas de checkout local)

=== Economie totale potentielle (groupes en l'etat) : 0 GB ===
Note : l'alignement des manifests (#2611 etape 2) peut elargir les groupes.
```

(Blocs `[isole]` abrégés à leur seul membre — la sortie intégrale est reproductible par la commande citée en tête.)

## Sortie verbatim de l'organe cache

```
Store partage : C:\dev\CoursIA\.mathlib-cache
  toolchain leanprover_lean4_v4.31.0-rc1-d568c8c0
  toolchain leanprover_lean4_v4.32.1-520045ab
  toolchain leanprover_lean4_v4.33.0-db584cd6

  cold      assignment_lean                   0 olean  junction
  absent    conway_cgt_lean                   0 olean  reel
  cold      game_theory_lean                  0 olean  junction
  ...                                                          (22 lignes `cold ... junction`)
  cold      argumentation_lean                0 olean  junction

Lakes: 32 | mathlib ok: 0 | froid: 22 | partiel: 0 | non installe: 7 | caches physiques distincts: 1
```

## Référence croisée

- Issue #13962 — grain parent (NTFS junctions Mathlib) · #2611 (alignement manifests, hors scope) · #15568 / #15577 (portée du scan = worktree)
- `scripts/lean/setup_shared_mathlib.ps1` — instrument Scan/Apply/Rollback (`Invoke-Scan` l.152-189, `Invoke-Apply` l.221+)
- `scripts/lean/check_mathlib_cache.py` — organe de mesure du cache traversant les jonctions (#8801)
- `docs/lean/cluster-junctions-c857.md` — V1 po-2024 (#14296, worktree frais)
- `docs/lean/junctions-scan-po-2027.md` — tableau multi-machine (ligne po-2024 corrigée par cette PR)
