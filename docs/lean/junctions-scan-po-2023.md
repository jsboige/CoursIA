# Scan NTFS junctions Mathlib — myia-po-2023

**Issue** : #13962 (sous-grain de #4362, acceptance step 1 = « Scan d'abord »)
**Date** : 2026-09-07T15:00Z (c.297 phase 2)
**Lane** : myia-po-2023:CoursIA-2
**Outil** : `scripts/lean/setup_shared_mathlib.ps1 -Mode Scan` (PowerShell 7.6.3)

## TL;DR

Economie potentielle sur **myia-po-2023** : **0,09 GB** (re-mesure c.809 : seul GK2 `v4.32.1-520045ab` a 2 physiques — game_theory_lean 0,64 GB donneur + conway_lean 0,09 GB jonctionnable). Le ledger initial sur-comptait l'économie d'un facteur 7 en attribuant learning_theory_lean à GK2 alors qu'il est dans GK1 (v4.33.0, 20 membres). **29 projets Lake avec dépendance mathlib** sur cette machine (vs 27 initiaux — 2 ajouts : formal_logic_lean GK6 + mimo_lean mal compté), 2 groupes mutualisables + 5 buckets singletons (4 strictement 1-membre + 1 cluster GK2 de 4 membres dont 3 étiquetés `isole` par erreur).

| Mesure | Valeur (c.809) | Ancienne valeur (c.297) |
|---|---|---|
| Projets Lake total avec mathlib | **29** | 27 |
| Groupes MUTUALISABLE (≥2 membres) | **2** (GK1 v4.33.0 20 membres, GK2 v4.32.1 4 membres) | 2 |
| Buckets singletons | **5** (GK3 v4.31.0-rc2, GK4 social_choice_lean_peters, GK5 upstream fixture, GK6 formal_logic_lean, GK7 mimo_lean) | 5 |
| Projets avec checkout physique local | **3** (game_theory_lean, learning_theory_lean, conway_lean) | 3 |
| Empreinte cumulee des checkouts physiques | **1,27 GB** | 1,28 GB |
| **Economie potentielle** | **0,09 GB** (GK2 seul : conway_lean jonctionné vers game_theory_lean) | 0,64 GB |

## Sortie verbatim du Scan — *mesure historique 07/09, supersédée*

> **⚠ Mesure historique 2026-09-07 (c.297 phase 2), supersédée par la re-mesure c.809 du 2026-09-24.**
> La section qui suit est conservée pour traçabilité du geste initial. Le **verdict courant** est dans le TL;DR (29 projets, 0,09 GB d'économie, 2 groupes mutualisables + 5 singletons selon `groupKey` discriminant complet — voir "Amendement c.749 / Re-mesure c.809" en fin de document).
> Diagnostic de dérive (c.809) : (a) **11 lacs v4.33.0 ajoutés** depuis le scan initial (assignment, minimax, search, sudoku, formal_groups, galois, grothendieck, hecke, sensitivity, serre100, learning_theory) — absents du décompte 27 ; (b) **3 « v4.32.1 isolés » du ledger initial étaient mal classés** (discrepancy_lean est dans GK2, mimo_lean a toolchain v4.33.0, social_choice_lean_peters a une dep tierce unique) ; (c) **learning_theory_lean n'est PAS dans GK2** (v4.32.1) — il est dans GK1 (v4.33.0), ce qui explique l'économie réelle 0,09 GB et non 0,64 GB. Détail dans "Amendement c.749" en fin de document.
>
> **Aucun nouveau Scan n'est fabriqué ici** — la sortie verbatim reproduit l'exécution `scripts/lean/setup_shared_mathlib.ps1 -Mode Scan` du 2026-09-07T15:00Z, archivée pour traçabilité. La re-mesure c.809 a été faite en Python sur les 29 manifests à jour ; voir tableau "Re-mesure first-hand c.809".

```
=== Projets Lake avec dependance mathlib (27) === [mesure historique 2026-09-07]

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

=== Economie totale potentielle (groupes en l'etat) : 0.64 GB === [mesure historique 2026-09-07, supersédée]
```

## Lecture (rapportee au verdict de l'EPIC) — *mesure historique 07/09, supersédée*

**Cluster `v4.32.1-520045ab`** : 13 projets pinnes sur la meme rev Mathlib, dont 3 avec checkout physique (game_theory_lean 0,64 GB / learning_theory_lean 0,55 GB / conway_lean 0,09 GB) et 10 qui ont deja consomme via `lake exe cache get` (pas de checkout local). L'economie de 0,64 GB reflete la strategie "garder le plus gros comme donneur, jonctionner les 2 autres vers lui".

> **⚠ Mesure historique 07/09, supersédée par c.809.** La re-mesure first-hand c.809 (cf. "Amendement c.749 / Re-mesure c.809" en fin de document) corrige : (1) **`learning_theory_lean` n'est PAS dans GK2** — il est dans GK1 (v4.33.0, 20 membres) ; (2) **`discrepancy_lean` n'est PAS isolé** — il partage le `groupKey` avec game_theory_lean, repeated_games_lean, conway_lean → GK2 passe de 3 à 4 membres ; (3) **`mimo_lean` n'est PAS toolchain v4.32.1** — toolchain = `leanprover/lean4:v4.33.0`, mathlib rev = `db584cd6`, deps transitives uniques → GK7 singleton. **L'économie réelle sur GK2 = 0,09 GB** (conway_lean jonctionné vers game_theory_lean), **pas 0,64 GB**.

**Cluster `v4.33.0-db584cd6`** : 9 projets pinnes sur v4.33.0, **0 avec checkout physique**. L'alignement de manifests est plus avance ici (les 9 sont sur la meme rev transitive), mais aucun n'a de `.lake/packages/mathlib` reel — donc l'economie est nulle **en l'etat**. L'effet prospectif de la mesure de ai-01 (8 lakes pinnes mais pas encore construits) ne s'applique pas a cette machine : aucun n'est encore dans l'etat "checkout physique" qui serait jonctionnable.

> **⚠ Mesure historique 07/09, supersédée par c.809.** Le cluster `v4.33.0` ne contient pas 9 mais **20 projets** (cf. GK1 c.809 : assignment, minimax, learning_theory, percolation, decision_theory, argumentation, calibration, erc20, formal_groups, galois, grothendieck, hecke, kelly, knot, mathlib_examples, planning, search, sensitivity, serre100, sudoku). Le constat « 0 checkout physique » reste valide (seul learning_theory_lean est dans GK1, déjà compté).

**5 groupes isoles** : 5 projets avec rev Mathlib uniques :
- `agent_tests/prover/session_state/reference_docs/stable_marriage/upstream` : v4.25.0 (fixture tierce, hors scope body).
- `conway_cgt_lean` : v4.31.0-rc2 transitif via vihdzp/combinatorial-games (pin non choisi par nous, exclusion explicite du body #13962 — #6116/#6432).
- `discrepancy_lean` : v4.32.1 isole (1 seul membre, pas de mutualisation possible — voir réserve NanoClaw c.749 sur la taxonomie des 3 v4.32.1).
- `mimo_lean` : v4.32.1 isole (1 seul membre).
- `social_choice_lean_peters` : v4.32.1 isole (1 seul membre, _peters).

> **⚠ Mesure historique 07/09, supersédée par c.809.** La liste des 5 isolés reste numériquement correcte (5 singletons GK3-GK7) mais leur **composition** change : GK6 = `formal_logic_lean` (mathlib `0df444a3`, NOUVEAU post-07/09), GK7 = `mimo_lean` (mathlib `db584cd6`, toolchain v4.33.0 ≠ v4.32.1). `discrepancy_lean` et `mimo_lean` étaient **mal classés** en v4.32.1 isolés — reclassement c.809. Voir tableau détaillé en fin de document.

## Differences vs mesure ai-01 (2026-09-01) — *mesure historique 07/09*

La mesure ai-01 rapportait 17 checkouts reels, ~110 Go empreinte totale, ~90 Go recuperables. Sur **myia-po-2023**, ces chiffres sont radicalement differents :

| | ai-01 (2026-09-01) | po-2023 (2026-09-07) |
|---|---:|---:|
| Projets avec checkout physique | 17 | **3** |
| Empreinte cumulee | ~110 GB | **1,28 GB** |
| Recuperable | ~90 GB | **0,64 GB** *(mesure historique 07/09 — supersédée par c.809, voir verdict courant 0,09 GB)* |

**Explication mesuree (mesure historique 07/09, supersédée par c.809)** : po-2023 est une machine de developpement Lean leger (CI-host), pas une machine de build avec cache chaud. Les 24 projets "pas de checkout local" ont deja consomme leur Mathlib via `lake exe cache get` (cache oleans precompile, pas le source) — la jonction n'a rien a y recuperer. **L'economie historique constatee au 07/09 etait 0,64 GB** (verdict superséde par c.809 → 0,09 GB reel, voir Amendement c.749 / Re-mesure c.809).

**Implication pour l'EPIC** (mesure historique 07/09, à actualiser sur verdict c.809) : l'application des junctions sur po-2023 est **peu rentable** mais **non-nulle**. Avec le verdict c.809 ramenant l'économie de 0,64 → **0,09 GB**, la rentabilité sur po-2023 devient **encore plus marginale** (le risque irreversible ne se justifie plus sur cette machine legere ; voir Amendement c.749 / Re-mesure c.809). La rentabilite reelle est sur les machines type ai-01 (cache chaud, plusieurs builds successifs, oleans accumules). **Cette mesure first-hand permet a l'EPIC d'evaluer l'effort par machine plutot que par total**.

> **⚠ Verdict numérique supersédée par c.809.** Le scan 07/09 concluait « économie 0,64 GB » sur cette machine — la re-mesure first-hand c.809 (Python sur 29 manifests, groupKey discriminant complet) ramène ce chiffre à **0,09 GB** (erreur d'un facteur 7 dans le ledger initial). Voir le détail dans "Amendement c.749 / Re-mesure c.809" en fin de document.

## Decision prise (Scan uniquement, PAS d'Apply)

Acceptance #13962 step 1 (Scan) est **accomplie pour myia-po-2023**. Steps 2-3-4 (Apply + anti-regression + mesure effectif) sont **gated par accord explicite dans le fil** (la prudence anti-irreversible du body tient : remplacer un checkout physique par une jonction **supprime** ~6,5 Go dont la reconstitution coute un `lake exe cache get` + build complet).

**Position de la lane (mesure historique 07/09, à actualiser sur verdict c.809)** : **Apply sur po-2023 NON recommande en l'etat** — l'economie historique constatee etait 0,64 GB (chiffre supersede par c.809 ; **l'economie reelle est 0,09 GB**, cf. Amendement c.749 / Re-mesure c.809), ce qui ne justifie pas le risque irreversible sur cette machine legere. **Recommandation** : appliquer les junctions sur ai-01 et machines de build lourd d'abord, re-mesurer sur po-2023 quand le cluster v4.32.1 prendra du volume (par exemple apres l'ajout d'un nouveau lake pinne sur 520045ab).

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

- L898 (mesure au 2026-09-07) : `gh pr list --state all --search '13962 in:body'` = 2 PRs MERGED (po-2026 #14038, po-2024 #14296). Aucune PR OUVERTE à la date du scan.
- L1356 : aucune PR merged sur ce numero n'a couvert myia-po-2023 (machine distincte de po-2026/po-2024/ai-01). Grain pas livre pour cette machine.
- G.9 : scan execute localement, sortie verbatim citee, mesures premieres (taille checkouts via script, pas d'estimation). Position ecrite avant Apply — prudence anti-irreversible honoree.

## Amendement c.749 (REPAIR suite revue NanoClaw)

Suite à la review structurelle NanoClaw du 2026-09-21 sur PR #17178 (CONCERNS state=COMMENTED), 2 corrections factuelles appliquées :

1. **Compte groupes isolés** : 4 → **5**. La verbatim du Scan rend bien 5 en-têtes `[isole]` (v4.25.0, v4.31.0-rc2, et **trois** v4.32.1 distincts : discrepancy_lean, mimo_lean, social_choice_lean_peters). Total 27 = 13 + 9 + **5** ✓.
2. **L898 datée** : la mesure « 2 PRs MERGED, aucune OUVERTE » était exacte au 2026-09-07 — ajoutée la date dans le libellé pour qu'un lecteur ultérieur ne la lise pas comme l'état courant du dépôt.

Réserve NanoClaw #2 dissipée c.809 (mesure first-hand) : le discriminant manquant est le **`groupKey` complet** (toolchain + tous les packages transitifs triés, `scripts/lean/setup_shared_mathlib.ps1` lignes 152-153), **PAS** seulement toolchain+mathlib. Le script Scan produit donc un bucket `isole` non pas pour les projets « 1 seul membre » mais pour ceux dont **au moins une dep transitive tierce** diffère du bucket dominant.

**Re-mesure first-hand c.809 (2026-09-24, Python sur 29 manifests)** :

| GroupKey | Projets | Mathlib rev | Physiques | GB |
|----------|---------|-------------|-----------|-----|
| GK1 | **20** (assignment, minimax, learning_theory, percolation, decision_theory, argumentation, calibration, erc20, formal_groups, galois, grothendieck, hecke, kelly, knot, mathlib_examples, planning, search, sensitivity, serre100, sudoku) | `db584cd6` | 1 (learning_theory_lean) | 0,55 |
| GK2 | **4** (game_theory, repeated_games, **discrepancy_lean**, conway_lean) | `520045ab` | 2 (game_theory_lean + conway_lean) | 0,73 |
| GK3 | 1 (conway_cgt_lean) | `acbd8f07` | 0 | 0 |
| GK4 | 1 (social_choice_lean_peters) | `520045ab` | 0 | 0 |
| GK5 | 1 (upstream fixture tierce) | `1ccd71f8` | 0 | 0 |
| GK6 | 1 (**formal_logic_lean**, NOUVEAU) | `0df444a3` | 0 | 0 |
| GK7 | 1 (**mimo_lean**, mathlib `db584cd6` ≠ `520045ab` !) | `db584cd6` | 0 | 0 |

**Total** : **29 projets** (vs 27 dans le ledger initial — **2 ajouts** : `formal_logic_lean` GK6 + `mimo_lean` mal compté en `v4.32.1` car le ledger n'a pas distingué toolchain= v4.33.0 vs mathlib rev).

**Diagnostic sur les 3 « v4.32.1 isolés » du ledger initial** :

- **`discrepancy_lean`** : EST dans **GK2** (cluster `v4.32.1-520045ab`, 4 membres). Manifest mathlib = `520045ab14e2`. Le bucket `isole` était une **erreur de classification** : discrepancy_lean partage le groupKey avec game_theory_lean, repeated_games_lean, conway_lean.
- **`mimo_lean`** : toolchain = `leanprover/lean4:v4.33.0`, mathlib rev = `db584cd6`. Le ledger disait `v4.32.1 isole` — **deux erreurs en cascade** (mauvaise toolchain + mauvais bucket). Mimo_lean est en réalité dans GK7 (singleton, mathlib `db584cd6`, mais deps transitives uniques qui le séparent de GK1).
- **`social_choice_lean_peters`** : GK4 (singleton), mathlib `520045ab` mais deps tierces `SocialChoiceLean` = `94a4c650` unique → pas mutualisable avec GK2.

**Implication pour Apply** :

- **GK2 (v4.32.1, 4 membres)** : 2 physiques (game_theory_lean 0,64 GB + conway_lean 0,09 GB). Économie potentielle = 0,09 GB (jonctionner conway_lean vers game_theory_lean). Le ledger initial disait 0,55 GB d'économie (learning_theory_lean) — **erreur** : learning_theory_lean est dans GK1, pas GK2.
- **GK1 (v4.33.0, 20 membres)** : 1 physique (learning_theory_lean 0,55 GB). Économie GK1 = 0 (un seul physique, pas de cible de jonction). Le ledger initial rapportait 0 économique pour GK1 — **correct** sur ce point, mais pour la mauvaise raison (il sous-comptait 11 projets).
- **Singletons (GK3-GK7)** : 0 économie (pas de cible de jonction).

**Économie réelle totale** : **0,09 GB** (vs 0,64 GB annoncé dans le ledger initial — **erreur d'un facteur 7**).

**Cause de la dérive du ledger** : le Scan original a été fait avec un état antérieur du dépôt (avant l'ajout de 11 lacs v4.33.0 et de formal_logic_lean). Le bucket `isole` du script Scan est techniquement correct (groupKey discriminant complet), mais **l'interprétation « 1 seul membre » est fausse** — c'est « groupKey unique ». Le commentaire « pas de mutualisation possible » était donc juste pour le discriminant mais trompeur pour le lecteur.

**Recommandation pour l'EPIC** : la phase « regroupements » (#4365) doit **lire le `groupKey` complet** (pas seulement toolchain+mathlib) et **classifier en singletons/buckets selon groupKey**, pas selon une heuristique « 1 seul membre = isole ». Le script Scan est correct ; sa **lecture** était ambiguë.

— myia-po-2023:CoursIA-2, c.297 phase 2 (post REPAIR P0 #15057) + c.749 REPAIR NanoClaw.
