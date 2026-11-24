# Junctions Mathlib — scan po-2024 (V3, arbre principal D:\Dev) : store restauré, 24 lacs chauds, 0 jonction pendante

**Date** : 2026-11-19
**Lane** : `myia-po-2024:CoursIA`
**Issue parente** : #4362 — couverture flotte (« Restent hors couverture… po-2024, po-2026. Chacune devrait un jour passer le meme Scan lecture seule (~2 min) pour fermer la carte », c62)
**Mode** : `Scan` (lecture seule, aucune modification) + organe dédié `check_mathlib_cache.py`
**Commandes exécutées** :

- `pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Scan` depuis `D:\Dev\CoursIA` (arbre **principal**, post-migration du 2026-09-17), exit 0
- `python scripts/lean/check_mathlib_cache.py`, exit 0

## Résumé V3

Le V2 (2026-09-13, conservé intégralement ci-dessous) mesurait **22 jonctions vivantes vers un store VIDE** et **11 lacs en dérive de toolchain**. Entretemps : migration du dépôt `C:\dev` → `D:\Dev` (2026-09-17), puis **mission #13962 exécutée par cette lane le 2026-11-17** (GO ai-01, DM 21:01Z) — `Apply` en 2 passes, **27/27 junctionnés**, `lake build Sensitivity.Fourier` SUCCESS 1671 jobs via la jonction (preuve c.6928398769 sur #13962). Le V3 mesure l'état **après** :

| Métrique | V2 (2026-09-13, `C:\dev`) | V3 (2026-11-19, `D:\Dev`) |
|---|---:|---:|
| Projets Lake portant `mathlib` (manifest scanné) | 28 | **36** |
| Lacs `JUNCTIONED` (tous groupes) | 22 | **24** (23 lacs + 1 junction doc `build-evidence-2026-10-31`) |
| Oleans Mathlib **atteignables** (organe dédié) | **0 / 22** (tous froids) | **24 ok à 8 322 oleans (23 lacs + 1 doc)** |
| Jonctions **pendantes** | non mesuré (store vide ⇒ tout froid) | **0** |
| Lacs froids (checkout physique, 0 olean) | 22 | **4** (`discrepancy`, `formal_logic`, `conway`, `mimo`) |
| Groupes (scan) | 8 (2 + 6) | **10** (1 mutualisable + 9 isolés) |
| Économie « potentielle » | 0 GB | **0 GB** (déjà mutualisé — métrique terminale, cf V2 §4) |

**Verdict** : l'état « inversé » du V2 est **résorbé**. Le store `D:\Dev\CoursIA\.mathlib-cache\leanprover_lean4_v4.33.0-db584cd6` est **peuplé et chaud** (8 322 oleans par membre), les 24 jonctions du groupe mutualisable (23 lacs + 1 doc) pointent dessus, et l'organe ne rapporte **aucune jonction pendante** (contrairement à po-2025 au 2026-10-08 : 14 pendantes). La carte de couverture #4362 peut porter po-2024 comme **couvert(e) et sain(e)**.

## Résiduels mesurés (aucun geste dans ce scan — lecture seule)

| Résiduel | Mesure | Lecture |
|---|---|---|
| `GOL/conway_lean` (aujourd'hui `JeuDeLaVie/conway_lean`) | checkout **physique 0,98 GB, froid** (0 olean) | checkout reconstruit hors jonction pour les builds de #25262 (jamais purgé) — candidat purge **après** merge #25262, un `lake build` réel d'abord (prescription de l'organe) |
| `formal_logic_lean` | checkout **physique 1,06 GB, froid** (groupe isolé `v4.33.1-0df444a3`) | physique car isolé ; les builds R4 de #25236 (po-2023) l'utilisent — ne pas toucher tant que #25236 est ouverte |
| `discrepancy_lean`, `mimo_lean` | checkouts **physiques 0 GB** (coquilles vides) | répertoires vides hérités du V2 (poses manuelles d'opérateur) — purge triviale, non urgente |
| `Compression_lean` | « pas de checkout local » dans le groupe mutualisable | jamais checkouté sur cette machine ; jonctionnable à la première demande de build |
| `torchlean_lean` | groupe isolé `v4.35.0-56a00585`, « pas de checkout local » | confirme **mesuré** la ligne d'arbitrage de la carte (c55/c61 : groupe isolé sans place déclarée) — décision coordinateur, 0 checkout donc 0 urgence disque |

## Sortie verbatim du Scan V3 (rejeu intégral du 2026-11-20, arbre principal `D:\Dev\CoursIA`)

> **Note de lecture (22/11, #26056).** La sortie ci-dessous est **verbatim** : elle reproduit les chemins tels que l'organe les a lus au scan du 19/11, et elle n'est pas réécrite. Depuis, les sous-répertoires de `MyIA.AI.Notebooks/SymbolicAI/Lean/` ont été renommés (`GROTH` → `Grothendieck`, `GOL` → `JeuDeLaVie`, `KNOTS` → `Noeuds`, `ANALYSE` → `Analyse`, `GALOIS` → `Galois`) : les chemins de ce relevé se lisent donc avec cette correspondance. Les **comptes** (24 jonctions, 8 322 oleans, 0 jonction pendante) ne sont pas affectés par le renommage.

Sortie complète du listing (le bloc diagnostic « revision mathlib partagee » qui suit l'économie dans la sortie réelle n'est pas repris ici — il ne porte aucun compteur de jonction). La version initiale de ce rapport condensait ces lignes en une élision à la main ; elle est remplacée par la sortie intégrale, qui est la seule source des comptes.

```text
=== Projets Lake avec dependance mathlib (36) ===

--- Groupe leanprover_lean4_v4.33.0-db584cd6 [MUTUALISABLE -- revision partagee par 3 groupes] : toolchain=leanprover/lean4:v4.33.0 mathlib=db584cd6 ---
  MyIA.AI.Notebooks/Compression/Compression_lean                         pas de checkout local
  MyIA.AI.Notebooks/GameTheory/assignment_lean                           JUNCTIONED
  MyIA.AI.Notebooks/GameTheory/game_theory_lean                          JUNCTIONED
  MyIA.AI.Notebooks/GameTheory/minimax_lean                              JUNCTIONED
  MyIA.AI.Notebooks/ML/learning_theory_lean                              JUNCTIONED
  MyIA.AI.Notebooks/Probas/Applications/Percolation/percolation_lean     JUNCTIONED
  MyIA.AI.Notebooks/Probas/DecisionTheory/decision_theory_lean           JUNCTIONED
  MyIA.AI.Notebooks/QuantConnect/kelly_lean                              JUNCTIONED
  MyIA.AI.Notebooks/Search/search_lean                                   JUNCTIONED
  MyIA.AI.Notebooks/Sudoku/sudoku_lean                                   JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/GALOIS/galois_lean                   JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/GOL/conway_lean                      checkout physique (0.98 GB)
  MyIA.AI.Notebooks/SymbolicAI/Lean/GROTH/formal_groups_lean             JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/GROTH/grothendieck_lean              JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry/geometry_lean               JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/knot_lean                      pas de checkout local
  MyIA.AI.Notebooks/SymbolicAI/Lean/Langlands/hecke_lean                 JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/riemann200_lean           JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/serre100_lean               JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/calibration_lean                     JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/combinators_lean                     JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/mathlib_examples                     JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean                     JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Planners/planning_lean                    JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/SmartContracts/erc20_lean                 JUNCTIONED
  MyIA.AI.Notebooks/SymbolicAI/Tweety/argumentation_lean                 JUNCTIONED
  docs/lean/darksnail/build-evidence-2026-10-31                          JUNCTIONED

--- Groupe leanprover_lean4_v4.25.0-1ccd71f8 [isole] : toolchain=leanprover/lean4:v4.25.0 mathlib=1ccd71f8 ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/session_state/reference_docs/stable_marriage/upstream pas de checkout local

--- Groupe leanprover_lean4_v4.32.1-520045ab [isole -- revision partagee par 2 groupes] : toolchain=leanprover/lean4:v4.32.1 mathlib=520045ab ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/ANALYSE/kls_lean                     pas de checkout local

--- Groupe leanprover_lean4_v4.32.1-520045ab [isole -- revision partagee par 2 groupes] : toolchain=leanprover/lean4:v4.32.1 mathlib=520045ab ---
  MyIA.AI.Notebooks/GameTheory/SocialChoice/social_choice_lean_peters    pas de checkout local

--- Groupe leanprover_lean4_v4.33.0-rc1-5eec30bc [isole] : toolchain=leanprover/lean4:v4.33.0-rc1 mathlib=5eec30bc ---
  MyIA.AI.Notebooks/GameTheory/conway_cgt_lean                           pas de checkout local

--- Groupe leanprover_lean4_v4.33.0-db584cd6 [isole -- revision partagee par 3 groupes] : toolchain=leanprover/lean4:v4.33.0 mathlib=db584cd6 ---
  MyIA.AI.Notebooks/Search/discrepancy_lean                              checkout physique (0 GB)

--- Groupe leanprover_lean4_v4.33.0-db584cd6 [isole -- revision partagee par 3 groupes] : toolchain=leanprover/lean4:v4.33.0 mathlib=db584cd6 ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/mimo_lean                            checkout physique (0 GB)

--- Groupe leanprover_lean4_v4.33.1-0df444a3 [isole -- revision partagee par 2 groupes] : toolchain=leanprover/lean4:v4.33.1 mathlib=0df444a3 ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean                    checkout physique (1.06 GB)

--- Groupe leanprover_lean4_v4.33.1-0df444a3 [isole -- revision partagee par 2 groupes] : toolchain=leanprover/lean4:v4.33.1 mathlib=0df444a3 ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean                    pas de checkout local

--- Groupe leanprover_lean4_v4.35.0-56a00585 [isole] : toolchain=leanprover/lean4:v4.35.0 mathlib=56a00585 ---
  MyIA.AI.Notebooks/SymbolicAI/Lean/torchlean_lean                       pas de checkout local

=== Economie totale potentielle (groupes en l'etat) : 0 GB ===
```

## Sortie verbatim de l'organe cache V3 (rejeu intégral du 2026-11-20)

```text
Store partage : D:\Dev\CoursIA\.mathlib-cache
  toolchain leanprover_lean4_v4.31.0-rc1-d568c8c0
  toolchain leanprover_lean4_v4.32.1-520045ab
  toolchain leanprover_lean4_v4.33.0-db584cd6

  ok        build-evidence-2026-10-31      8322 olean  junction
  absent    Compression_lean                  0 olean  reel
  ok        assignment_lean                8322 olean  junction
  absent    conway_cgt_lean                   0 olean  reel
  ok        game_theory_lean               8322 olean  junction
  ok        minimax_lean                   8322 olean  junction
  absent    social_choice_lean_peters         0 olean  reel
  absent    iit_lean                          0 olean  reel
  ok        learning_theory_lean           8322 olean  junction
  ok        percolation_lean               8322 olean  junction
  ok        decision_theory_lean           8322 olean  junction
  ok        kelly_lean                     8322 olean  junction
  cold      discrepancy_lean                  0 olean  reel
  ok        search_lean                    8322 olean  junction
  ok        sudoku_lean                    8322 olean  junction
  absent    upstream                          0 olean  reel
  absent    kls_lean                          0 olean  reel
  ok        calibration_lean               8322 olean  junction
  ok        combinators_lean               8322 olean  junction
  absent    finiteness_lean                   0 olean  reel
  cold      formal_logic_lean                 0 olean  reel
  ok        galois_lean                     8322 olean  junction
  ok        geometry_lean                   8322 olean  junction
  cold      conway_lean                       0 olean  reel
  ok        formal_groups_lean             8322 olean  junction
  ok        grothendieck_lean              8322 olean  junction
  absent    knot_lean                         0 olean  reel
  ok        hecke_lean                     8322 olean  junction
  ok        mathlib_examples               8322 olean  junction
  cold      mimo_lean                         0 olean  reel
  ok        riemann200_lean                8322 olean  junction
  ok        sensitivity_lean               8322 olean  junction
  ok        serre100_lean                  8322 olean  junction
  absent    tegmark_muh_lean                  0 olean  reel
  ok        planning_lean                  8322 olean  junction
  ok        erc20_lean                     8322 olean  junction
  ok        argumentation_lean             8322 olean  junction

Lakes: 42 | mathlib ok: 24 | froid: 4 | partiel: 0 | non installe: 9 | jonctions pendantes: 0 | illisibles: 0 | caches physiques distincts: 5

Avant de conclure 'cache purge', relancer un `lake build` reel :
  un comptage a 0 via `find` ou `islink` ne prouve rien sur une junction.
```

### Rapprochement des comptes (scan ↔ organe, rejeu 2026-11-20)

Les deux outils ne lisent **pas la même source** : le scan classe par **manifeste** (`lake-manifest.json`), l'organe par **lakefile** (`declares_mathlib`). Chaque compte se recoupe une fois cette lecture croisée nommée :

- **36 (scan) = 27 membres du groupe mutualisable + 9 groupes isolés.** Exact, aucun écart.
- **L'organe affiche 37 entrées = 36 (scan) − 2 + 3.** Il affiche `iit_lean`, `finiteness_lean`, `tegmark_muh_lean` (lakefile déclare mathlib, manifeste non — vérifié : 0 occurrence de mathlib dans leurs trois manifestes) et **saute** `differential_lean` et `torchlean_lean` (manifeste cite mathlib — le scan les groupe en v4.33.1-0df444a3 et v4.35.0-56a00585 — lakefile non).
- **`build-evidence-2026-10-31` est DANS les 27 membres** du groupe mutualisable, pas un 37ᵉ projet : c'est la « junction doc ». Le JUNCTIONED du scan et le `ok` de l'organe le comptent tous deux.
- **Junctionnés : 24 (23 lacs + 1 doc) = les 24 `ok` de l'organe, membre à membre** — les deux ensembles sont identiques, aucun lac manquant. Les 3 membres du groupe mutualisable non junctionnés : `Compression_lean` (pas de checkout local), `conway_lean` (physique 0,98 GB, reconstruit hors jonction pour les builds de #25262), `knot_lean` (pas de checkout local).
- La version condensée initiale comptait **26 jonctions à la main — décompte d'auteur erroné** ; la sortie intégrale ci-dessus fait foi. La mission #13962 du 2026-11-17 rapportait « 27/27 junctionnés » pour ses passes `Apply` : l'état mesuré ici (24 des 27 membres) reflète conway reconstruit physique depuis, et deux membres sans checkout local jamais junctionnables.

**Les 5 lacs non classés de la ligne `Lakes` (42 − 37)** — que l'organe compte dans le total mais n'affiche pas un à un (statut `no_mathlib_dep`, exclu du détail — source de l'organe, ligne du saut d'affichage) — ne sont **pas cinq lacs sans dépendance Mathlib**. Ils se partagent en deux classes, mesurées sur les lakefiles ET les manifestes :

- **3 lacs sans dépendance Mathlib nulle part** (lakefile et manifeste d'accord) : `asymmetric_information_lean`, `lean_game_defs`, `lean_game_defs_ext` (GameTheory).
- **2 lacs dont le `lake-manifest.json` cite mathlib mais dont le lakefile ne la déclare pas** : `differential_lean` et `torchlean_lean` (SymbolicAI/Lean) — le scan les groupe respectivement en v4.33.1-0df444a3 et v4.35.0-56a00585. L'organe ne lit que le lakefile (`declares_mathlib`) : c'est un **angle mort sur les dépendances transitives du manifeste**, signalé sur #4362, non corrigé dans ce rapport.

## Ligne po-2024 pour la carte multi-machine

| Mesure | V2 (2026-09-13) | V3 (ce rapport) |
|---|---:|---:|
| Checkouts Mathlib réels | 0 vus + 2 réels hors découverte | **4 physiques** (conway 0,98 GB · formal_logic 1,06 GB · discrepancy 0 · mimo 0) |
| Jonctions actives | 22 (vers store vide) | **24 chaudes (23 lacs + 1 doc)** |
| Oleans atteignables | 0 | **8 322 × 24 (23 lacs + 1 doc)** |
| Groupes mutualisables | 2 (13 + 9) | **1 (27 membres déclarés, 24 junctionnés)** |
| Économie jonction-cluster | 0 GB | 0 GB — **déjà réalisée** |

---

## Rapport V2 (2026-09-13 — conservé intégralement)

### Junctions Mathlib — scan po-2024 (V2, worktree principal) : 22 jonctions vivantes vers un store VIDE

**Date** : 2026-09-13
**Lane** : `myia-po-2024:CoursIA`
**Issue parente** : #13962 — Appliquer les junctions NTFS sur le cluster Mathlib `520045ab`
**Mode** : `Scan` (lecture seule, aucune modification) + organe dédié `check_mathlib_cache.py`
**Commandes exécutées** :
- `pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Scan` depuis `C:\dev\CoursIA` (worktree **principal**)
- `python scripts/lean/check_mathlib_cache.py`

Voir aussi :
- `../transients/2026-09-02-cluster-junctions-c857.md` (#14296, c.857 — **V1 po-2024, worktree frais**)
- `docs/lean/junctions-scan-po-2027.md` (#15507/#15577 — tableau multi-machine)
- `docs/lean/junctions-scan-po-2026.md` (#14038, po-2026, 0 GB)
- #15070 (po-2023, 0.64 GB) · #13962 (issue parente)

## Résumé

Le tirage de cycle a rendu #13962 ; ma lane y portait un claim du **2026-09-05** (« scan actualisé po-2024, le V1 du 2026-09-02 est périmé ») resté **sans livraison** — aucun `docs/lean/junctions-scan-po-2024.md` n'existait sur `main`. Ce rapport le solde, et le verdict est plus fort qu'un simple rafraîchissement.

| Métrique | V1 (#14296, worktree **frais**) | V2 (ce rapport, worktree **principal**) |
|---|---:|---:|
| Projets Lake portant `mathlib` (manifest scanné) | 24 | **28** |
| Groupes par manifest-identity | 6 | **8** (2 mutualisables + 6 isolés) |
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

**Périmètre de la datation — 22 jonctions = 18 + 4.** L'`Apply` du 2026-08-30 a enregistré **19** membres (`share-state.json`) ; la mesure vivante compte **22** jonctions. L'écart se réconcilie exactement, et il **borne la portée** du paragraphe qui précède :

- **18** des 22 jonctions viennent de cet `Apply` : ce sont les 19 membres **moins `conway_lean`**, dont la jonction a été retirée à un moment non daté (§6).
- **4** jonctions ont été **posées hors de cet `Apply`** : `discrepancy_lean`, `mimo_lean`, `social_choice_lean_peters` (les 3 groupes isolés `v4.32.1`) et `percolation_lean` (membre du bloc des 9). Aucune n'apparaît dans `share-state.json`.

Conséquence : les **11 lacs en dérive sont tous parmi les 18** issus de l'`Apply`. La chaîne #15033 les couvre donc **tous**, et la lecture « la dérive vient de la migration 4.33.0, pas d'un défaut de l'outil » n'est pas une hypothèse mais une conséquence du périmètre. Les 4 jonctions hors-`Apply` sont, elles, **cohérentes** avec leur cible (`v4.32.1` / `520045ab`) : leur origine est antérieure et sans lien avec la dérive — `Invoke-Apply` (l.233) ne les aurait de toute façon jamais repointées.

**Origine datée de la dérive** : la PR **#15033** (`feat(lean,#14773): bump calibration_lean vers Lean/Mathlib 4.33.0`, lane `myia-po-2024:CoursIA-2`, mergée 2026-09-09) a fait passer `calibration_lean` — l'un des 11 lacs ci-dessus — de `v4.32.1`/`520045ab` à `v4.33.0`/`db584cd6`. Elle a mis à jour `lean-toolchain` et `lake-manifest.json` sans toucher à `.lake/packages/mathlib`, qui est gitignore et n'apparaît donc dans aucun diff. C'est exactement le geste qui fabrique la ligne 5 du tableau ; les 10 autres lacs ont suivi le même chemin lors de la migration 4.33.0.

### Datation des 4 poses hors-`Apply` (Item 1 de #15959)

Les 4 jonctions du paragraphe précédent étaient **identifiées sans être datées**. Datation par trace d'historique git du lac — trace explicitement admise par l'acceptance —, une ligne par jonction :

| Jonction | Paire cible atteinte le (trace) | Dans `share-state.json` ? | Fourchette de pose |
|---|---|---|---|
| `Search/discrepancy_lean` | **2026-08-25 00:50** — création du lac (`d84eb35f5`, #12823) ; `lean-toolchain` ne porte **qu'un seul** commit, la paire `v4.32.1`/`520045ab` est celle d'origine (rev re-confirmée inchangée par `81684122e`, 2026-08-29) | non | **2026-08-30 04:08:54+02:00 → 2026-09-13** |
| `SymbolicAI/Lean/mimo_lean` | **2026-08-17 00:50** — `29d2e445c` (#11325) fait passer la paire de `v4.32.0`/`81a5d257` à `v4.32.1`/`520045ab` | non | **2026-08-30 04:08:54+02:00 → 2026-09-13** |
| `GameTheory/social_choice_lean_peters` | **2026-08-20 06:15** — `a4187ecd5` (#11888) fait passer la paire de `v4.27.0-rc1`/`8cb93191` à `v4.32.1`/`520045ab` | non | **2026-08-30 04:08:54+02:00 → 2026-09-13** |
| `Probas/Applications/Percolation/percolation_lean` | **2026-09-06 14:13** — création du lac (`43875927b`, #14892) | non | **2026-09-06 14:13 → 2026-09-13** |

**Bornes.** La borne **basse** est le maximum de deux contraintes : (a) la paire cible doit déjà être celle du lac — sinon la jonction viserait un autre store, et l'outil ne repointe jamais une jonction existante (l.233) ; (b) le store cible `leanprover_lean4_v4.32.1-520045ab` doit exister — sa date d'enregistrement est `createdAt 2026-08-30T04:08:54+02:00` (§1 point 7), et `Invoke-Apply` crée le store **avant** de jonctionner (l.253-259). Pour les trois premiers lacs, c'est (b) qui mord ; pour `percolation_lean`, c'est (a) — le lac est **postérieur** à l'`Apply`. La borne **haute** est la date de la mesure du §1 (2026-09-13).

**L'outil ne peut pas être l'auteur de ces 4 poses.** `Invoke-Apply` ne retient que les groupes de `Count -ge 2` (l.223) : les 3 groupes isolés n'ont jamais été traités par un `Apply`. Et l'`Apply` **ré-enregistre** les membres déjà jonctionnés qu'il croise (l.259-262, « les membres deja junctionnes sont re-traites aussi ») : si ces lacs avaient été membres d'un groupe traité, ils figureraient dans `share-state.json`. Ils n'y figurent pas. `percolation_lean`, lui, n'existait pas encore au 2026-08-30. Les 4 sont donc des **poses manuelles d'opérateur** — ce que le V1 avait déjà documenté sur `mimo_lean` (« action manuelle de l'opérateur sur le worktree source (pas un Apply) », #14296 §« Nettoyage du checkout orphelin `mimo_lean` 1.18 GB »). Conséquence pour le §2 : l'hypothèse d'un **`Apply` antérieur** est **écartée**, et aucune des 4 n'étant dans les 11 lacs en dérive, la chaîne #15033 reste bien le seul chemin de datation de la dérive.

**Limite explicite de cette datation.** La trace directe — `CreationTime` du point d'analyse NTFS, qui *est* l'instant de pose — n'est **pas lisible depuis cette lane** : po-2023 n'a pas d'accès au disque de po-2024, et les 4 chemins n'existent pas localement (`fsutil reparsepoint query` → « chemin introuvable » sur les quatre, vérifié le 2026-09-13). L'outil, lui, **n'écrit aucun log** : sa seule écriture de fichier est le `Set-Content` du `share-state.json` (l.337). Il n'existe donc **aucune trace d'horodatage côté outil**, et la fourchette ci-dessus est la borne la plus serrée dérivable à distance. Le geste qui la referme est **une commande par lac sur po-2024** :

```powershell
Get-Item -Force 'C:\dev\CoursIA\MyIA.AI.Notebooks\<lac>\.lake\packages\mathlib' |
    Select-Object FullName, LinkType, Target, CreationTime, LastWriteTime
```

## 3. Cause du store vide

`Invoke-Apply` **déplace** le checkout physique du donneur dans le store : `Move-Item $donor.MathlibDir -Destination $cacheMathlib` (l.254). Le donneur enregistré est `argumentation_lean` et il **n'a pas** de `.bak-2611` — cohérent avec la branche donneur (déplacé, jamais sauvegardé). Le store correspondant est aujourd'hui **vide**.

Autrement dit : le contenu a été **déplacé dans le store le 2026-08-30, puis a disparu**. Ce que la mesure établit : le store est vide (points 3/5/6). Ce qu'elle n'établit **pas** : *qui* l'a vidé. Aucun script du dépôt ne purge ce chemin (`grep` borné `scripts/` + `.github/` : seules occurrences = l'outil lui-même et `check_mathlib_cache.py`) — la cause est **hors dépôt** ou antérieure à l'historique consultable.

**Piste `Remove-DirRobust` — inventoriée puis fermée.** Ce `grep` portait sur le **chemin du store**, il ne pouvait donc pas voir le seul organe du dépôt qui supprime des répertoires **Mathlib**. Inventaire de ses **appelants** (fait le 2026-09-13) : `Remove-DirRobust` a **un unique appelant** — `setup_shared_mathlib.ps1:311`, dans la branche `-RemoveBackups` de l'`Apply`, qui retire les `.bak-2611` des membres et **jamais le store**. Son commentaire (l.194-195) documente une purge de `mathlib.bak-2611` sur `calibration_lean` le **2026-06-11** : c'est un geste **manuel d'opérateur**, visant un **backup**, et **antérieur de 2,5 mois** à l'`Apply` du 2026-08-30. Le dépôt ne contient donc **aucun mécanisme automatique** capable de vider le store : la piste est **fermée**, et la cause reste hors dépôt. `.mathlib-cache/` est gitignore (`.gitignore:932`), donc l'état n'apparaît dans **aucun** artefact versionné ni en CI. Le disque `C:` est sous pression (127,9 Go libres sur ~930 Go), ce qui rend une purge de récupération d'espace l'hypothèse principale — **hypothèse, non mesurée**.

**Inventaire exhaustif des sites de suppression du script (complément Item 2 de #15959).** Le paragraphe ci-dessus ne couvrait que les **appelants** de `Remove-DirRobust`. L'acceptance d'#15959 demande aussi « toute fonction de purge de répertoire du même script », avec cible et date. Les voici toutes, `setup_shared_mathlib.ps1` :

| Site | Fonction | Cible supprimée | Condition | Date documentée |
|---|---|---|---|---|
| l.198 | `Remove-DirRobust` | le `$Path` reçu | après `Test-Path` | — |
| l.201-202 | `Remove-DirRobust` | idem, **fallback** `robocopy /MIR` + `rd /s /q` | si `Remove-Item` a échoué | incident **2026-06-11** (commentaire l.194-195) |
| l.203 | `Remove-DirRobust` | `$env:TEMP\empty-2611` (dossier vide jetable) | après le fallback | — |
| **l.311 — unique appelant de `Remove-DirRobust`** | `Invoke-Apply`, branche `-RemoveBackups` | `<membre>\.lake\packages\mathlib.bak-2611` | `-RemoveBackups` **et** `hadBackup` **et** `lake build` SUCCESS | **2026-06-11** (purge manuelle du `.bak-2611` de `calibration_lean`) |
| l.213 | `Restore-Member` | le **lien** (`cmd /c rmdir`), jamais la cible | membre `IsJunction`, sur échec de build | — |
| l.362 | `Invoke-Rollback` | le **lien** (`cmd /c rmdir`), par membre, donneur en dernier | `IsJunction` | — |
| l.385 | `Invoke-Rollback` | `<store>/share-state.json` | tous les membres restaurés | — |
| l.389 | `Invoke-Rollback` | `<store>/` — le répertoire **de groupe** | `remaining` vide **et** `mathlib` absent du store | — |

Deux lignes du script sont des **déplacements**, pas des purges, et ne figurent donc pas au tableau : l.217 (`Move-Item` du `.bak-2611` vers la cible) et l.365 (`Move-Item` du cache vers le donneur).

**Lecture — le dépôt ne peut pas avoir vidé le store, et l'état mesuré n'est reproductible par aucun de ces sites.** Les seules cibles atteintes sont (a) des `.bak-2611` **de membres** (lignes 198-203, 311 — le seul appelant réel), (b) des **liens** de jonction (l.213, l.362 : `rmdir` ne touche jamais la cible), (c) des `share-state.json` et le répertoire de groupe **déjà vidé de son `mathlib` par le déplacement du donneur** (l.385/389). Crucialement, l'état relevé au §1 — store **présent**, `mathlib/` **présent mais vide**, `share-state.json` **présent** — n'est produit par **aucune** séquence : un `Rollback` mené à son terme **supprime le répertoire de groupe** (l.389, atteint parce que l.365 vient de déplacer `mathlib` hors du store, donc `Test-Path $cacheMathlib` est faux), et un `Rollback` interrompu avant l.365 laisse `mathlib` **absent**, jamais « présent et vide ». La piste dépôt reste donc **fermée**, et la cause hors dépôt.

## 4. Angle mort de l'instrument (et proposition)

`Invoke-Scan` ne calcule l'économie que lorsque `$sizes.Count -ge 2`, c'est-à-dire **au moins deux checkouts physiques** dans le groupe (l.179) ; `JUNCTIONED` est un libellé **terminal** (l.170), sans contrôle de la cible. Conséquence mesurée :

- un cluster **appliqué et cassé** rend `=== Economie totale potentielle : 0 GB ===`, **exactement** comme une machine qui n'a rien à faire ;
- le V1 a de plus scanné un **worktree frais** — `$RepoRoot = git rev-parse --show-toplevel` (l.70), donc la mesure ne voit que le worktree courant. C'est le faux négatif de portée que #15568/#15577 a nommé **après** que le V1 (#14296) l'ait produit.

**Proposition** (hors périmètre de cette PR, grain `guard`/`tooling` à dispatcher) : donner à `Invoke-Scan` trois états au lieu d'un — `JUNCTION-OK` / `JUNCTION-COLD` / `JUNCTION-MISMATCH` — en résolvant la cible (`realpath`) et en comparant le `rev8` du manifest à celui du nom du store, plus un comptage d'oleans. `check_mathlib_cache.py` porte déjà les primitives (`MATHLIB_OLEAN_FLOOR = 1000`) ; l'y brancher éviterait de réécrire l'instrument.

### Seconde occurrence consolidée (po-2025, 2026-10-08)

Le scan po-2025 — mesure intégrale préservée sur le dashboard RooSync `workspace-CoursIA` (post `[INFO] PRESERVATION INTEGRALE`, 08/10) — confirme les deux cécités et en mesure une **troisième, propre à l'organe dédié** :

1. **Même cécité de cible** (`JUNCTIONED` terminal) : 18 jonctions, **0 utilisable** — dont **14 pendantes** (classe absente de po-2024, qui n'avait que des jonctions vivantes vers store vide) et 4 `MISMATCH` vers `v4.32.1-520045ab`.
2. **Même cécité de classement** : `game_theory`/`percolation`/`knot`/`argumentation` listés sous le groupe déclaré `v4.33.0-db584cd6` alors que leur cible réelle est `v4.32.1-520045ab`.
3. **`check_mathlib_cache.py` classe les pendantes en `reel`** : retour anticipé l.88 (`if not mathlib.exists(): status = "absent"; return` — `exists()` **suit** le lien vers une cible absente) avant la détection de jonction l.93-96, puis l.158 affiche `reel`. `Path.is_junction()` (Python ≥ 3.12) et `Path.resolve()` voient juste ; c'est l'**ordre des tests** qui perd l'information. Le verdict global d'atteignabilité reste exact — seule la classe de panne est faussée.

**Méthode durable** (une jonction ne se juge pas sur son libellé) : résoudre la cible ET énumérer **à travers** le lien — `fsutil reparsepoint query` (balise `0xa0000003`), `Test-Path` sur le chemin résolu, énumération `\\?\` à travers la jonction (un `0` rendu par `find`/`islink` sur le chemin du lien ne prouve rien), `lean-toolchain` du lac vs groupe du `share-state.json`. La proposition ci-dessus s'élargit à **quatre** états : `JUNCTION-OK` / `JUNCTION-COLD` / `JUNCTION-MISMATCH` / `JUNCTION-DANGLING`.

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
- Constaté sans être expliqué : `conway_lean` figure parmi les 19 membres de `share-state.json` mais son `.lake/packages/mathlib` **n'existe plus** (le Scan le classe « pas de checkout local »). Une jonction a donc été retirée à un moment non daté. C'est **le seul membre de l'`Apply` dans ce cas**, et c'est lui qui explique l'écart 19 → 18 du §2 (22 jonctions = 18 de l'`Apply` + 4 posées ailleurs).

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

- **Mode Scan exécuté** depuis le worktree **principal** `C:\dev\CoursIA` ; sortie reprise verbatim ci-dessous (blocs `[isole]` abrégés à leur seul membre, comme indiqué sous le bloc).
- **Ré-ancrage post-revue (2026-09-13)** : la revue `[NanoClaw]` (myia-ai-01, 08:18Z) a relevé deux compteurs que la sortie citée **ne reproduisait pas** — « 9 groupes » et « 20 lacs » (§Vérifications), ainsi que la ligne « 6 → 9 » du §Résumé. Re-mesurés sur une **nouvelle exécution** du Scan : **8** groupes (2 + 6) et **25** lacs partageant leur paire `(toolchain, rev)`. Les deux nombres publiés étaient des **reports de prose non ré-ancrés sur l'artefact** — le défaut même que ce rapport reproche au V1. Corrigés ci-dessus ; aucune conclusion n'en dépendait (le verdict V1-inversé tient sur les 22 jonctions et le store vide, tous deux recomptés).
- **Organe dédié exécuté** : `check_mathlib_cache.py` → `mathlib ok: 0 | froid: 22 | caches physiques distincts: 1` (exit 0, advisory).
- **Discrimination manifest-identity** : **8** groupes (2 `[MUTUALISABLE]` + 6 `[isole]`) alors que **25** lacs partagent leur paire `toolchain + mathlib rev`. Ces 25 se répartissent en **5 blocs** : 13 sous `v4.33.0 + db584cd6` (1 bloc) et 12 sous `v4.32.1 + 520045ab` (**1 bloc de 9 + 3 blocs d'1**). C'est cet éclatement qui porte la démonstration : `discrepancy_lean`, `mimo_lean`, `social_choice_lean_peters` partagent `v4.32.1 + 520045ab` avec le **bloc des 9** et restent néanmoins **isolés** — leurs deps transitives diffèrent. Clé de groupe `"$toolchain|$($pairs -join ';')"` (`setup_shared_mathlib.ps1:119-123`), plus stricte que la paire `(toolchain, rev)`. Les 3 lacs restants (`v4.25.0`, `v4.31.0-rc2`, `v4.33.1`) ont une paire unique et forment 3 blocs d'1. **Total : 13 + 12 + 3 = 28.**
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
- Issue #15959 — points de veille de la revue #15938 : datation des 4 poses hors-`Apply` (§2) + inventaire exhaustif des sites de suppression du script (§3)
- `scripts/lean/setup_shared_mathlib.ps1` — instrument Scan/Apply/Rollback (`Invoke-Scan` l.152-189, `Invoke-Apply` l.221+)
- `scripts/lean/check_mathlib_cache.py` — organe de mesure du cache traversant les jonctions (#8801)
- `../transients/2026-09-02-cluster-junctions-c857.md` — V1 po-2024 (#14296, worktree frais)
- `docs/lean/junctions-scan-po-2027.md` — tableau multi-machine (ligne po-2024 corrigée par cette PR)
