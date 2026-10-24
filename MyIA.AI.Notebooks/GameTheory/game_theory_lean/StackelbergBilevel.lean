/-
  StackelbergBilevel — root aggregator FR
  =====================================

  Module de formalisation du cadre leader/suiveur (Stackelberg) en
  demande linéaire et coûts marginaux constants, adossé aux
  invariants `tests/test_stackelberg.py` et
  `tests/test_stackelberg_asymmetric.py` du dossier
  `MyIA.AI.Notebooks/GameTheory/`.

  Le module substantiel vit dans `StackelbergBilevel/StackelbergBilevel.lean` :
  types `DemandIntercept`, `MarginalCost`, `Quantity` (tous rationnels) ;
  `cournotReaction` (meilleure réponse clampée à 0) ;
  `cournotEquilibriumSym` (quantité de Cournot symétrique, point fixe) ;
  `stackelbergLeader` (forme close de la quantité du leader) ;
  `stackelbergFollower` (forme close du suiveur) ;
  `stackelbergFollowerEqReaction` (l'invariant central : le suiveur
  best-respond au leader) ; `firstMoverAdvantage` (qL > qF sous
  coûts symétriques) ; `welfareAboveCournot` (qL + qF > 2·q*).

  Ce fichier existe parce que le `lean_lib StackelbergBilevel` du
  lakefile déclare `globs := #[`StackelbergBilevel.*]` : Lake résout
  la racine `StackelbergBilevel` de la bibliothèque, et son absence
  rend « error: StackelbergBilevel: some modules have bad imports »
  (cf convention des sept bibliothèques sœurs du même package —
  `SocialChoice.lean`, `CooperativeGames.lean`, `RepeatedGames.lean`,
  `StableMarriage.lean`, `Swaps.lean`, `Abstraction.lean`,
  `ProgramGames.lean`).

  Suivre les usages des autres modules : ce module est
  VOLONTAIREMENT sans `ProgramGames` (pas de bilevel imbriqué —
  Stackelberg est un cas particulier du bilevel où le leader sait
  l'identité du suiveur), sans `RepeatedGames` (pas de jeu répété —
  le temps n'apparaît pas dans le jeu de Stackelberg statique), et
  sans le sibling `_en` (EPIC #4980, flot drainé — le grain n'a
  pas d'audience externe prévue, l'EN sera ajouté si publication
  ultérieure).
-/

import StackelbergBilevel.StackelbergBilevel
