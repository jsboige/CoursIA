/-
  Abstraction — racine FR
  =======================

  Statut formel de la dette d'abstraction mesurée par le notebook
  `GameTheory-19-Abstraction-a-Dette.ipynb` (grain #12204, opération 2).

  Le module substantiel vit dans `Abstraction/Basic.lean` : modèle fini
  en stratégies pures sur les entiers (duels 2×2 à somme nulle, dette =
  exploitabilité par meilleures réponses, abstraction par SOMME de
  bloc, retransport), lois générales (`encadrement`, `dette_nonneg`,
  `selle_dette_nulle`) et contre-exemple nommé
  `raffinement_aggrave_la_dette` : sur trois duels d'entiers, raffiner
  la partition grossière {{0,1,2}} en {{0},{1,2}} fait passer la dette
  totale retransportée de 3 à 4 (aggravation stricte, indépendante du
  choix des selles — elles sont uniques), tandis que la partition
  discrète retombe à 0. La non-croissance observée par le notebook
  n'est donc pas un théorème général.

  Ce fichier existe parce que le `lean_lib Abstraction` du lakefile
  déclare `globs := #[`Abstraction.*]` : Lake résout la racine
  `Abstraction` de la bibliothèque, et son absence rend
  « error: Abstraction: some modules have bad imports ». Les cinq
  bibliothèques sœurs du même package suivent cette convention
  (`SocialChoice.lean`, `CooperativeGames.lean`, `RepeatedGames.lean`,
  `StableMarriage.lean`, `Swaps.lean`).

  Comme `Swaps`, ce module est VOLONTAIREMENT sans Mathlib : tout est
  certifié par réduction du noyau (`decide`/`rfl`) sur des littéraux
  entiers — `lake build Abstraction` ne déclenche aucune compilation
  de dépendance, et aucun théorème concret ne dépend du moindre axiome.
-/

import Abstraction.Basic
