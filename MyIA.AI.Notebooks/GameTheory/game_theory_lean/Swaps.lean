/-
  Swaps — root aggregator FR
  ==========================

  Chemins de swaps sur les jeux 2×2 ordinaux : compagnon formel du
  notebook `GameTheory-03a-Chemins-de-Swaps.ipynb` (grain #12222).

  Le module substantiel vit dans `Swaps/Basic.lean` : type `Table`,
  les six générateurs adjacents (`Etape`), l'application d'un chemin
  (`applique`), et les quatre théorèmes du certificat —
  `certificat_chemin` (arrivée, par `rfl`), `chemin_valide_non_minimal`
  (valide ≠ minimal), `aucun_chemin_court` (borne inférieure par
  énumération décidable) et `distance_dilemme_chicken` (la distance
  Dilemme → Chicken vaut exactement 2).

  `Swaps/Parite.lean` ajoute l'obstruction **non bornée** (§6 de l'EPIC
  #12205). Là où `aucun_chemin_court` réfute 7 chemins par énumération
  et où le certificat du notebook `GameTheory-24b` réfute tout chemin
  au-delà d'un budget `k_max`, la parité jointe du nombre d'inversions
  est un invariant transporté le long d'un chemin de longueur
  **quelconque** : `parite_determinee` lit la parité de la longueur sur
  les deux extrémités, et `aucun_chemin_impair_dilemme_chicken` en
  déduit qu'aucun chemin de longueur impaire ne relie le Dilemme à
  Chicken — une famille infinie. Les deux obstructions sont
  complémentaires ; aucune ne subsume l'autre.

  Ce fichier existe parce que le `lean_lib Swaps` du lakefile déclare
  `globs := #[`Swaps.*]` : Lake résout la racine `Swaps` de la
  bibliothèque, et son absence rend `error: Swaps: some modules have
  bad imports` (CI de la PR #12260). Les quatre bibliothèques sœurs du
  même package suivent exactement cette convention — `SocialChoice.lean`,
  `CooperativeGames.lean`, `RepeatedGames.lean`, `StableMarriage.lean`
  sont chacune une racine qui n'agrège que des imports.

  Volontairement SANS Mathlib : tout est calcul fini décidable sur des
  listes littérales, clos par `rfl` et `decide`. `lake build Swaps` ne
  déclenche donc aucune compilation de dépendance.
-/

import Swaps.Basic
import Swaps.Parite
