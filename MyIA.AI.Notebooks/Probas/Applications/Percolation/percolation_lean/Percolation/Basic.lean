import Mathlib.Combinatorics.SetFamily.HarrisKleitman

/-! # Noyau fini de la percolation — module d'amorce

Le but de ce lake (`percolation_lean`) est de formaliser le **noyau fini** de la
percolation de Bernoulli sur un graphe fini, avant le pont vers la cours ICT
(voir `#14871`).

Le cœur de ce noyau est l'inégalité de **Harris–Kleitman** (forme finie du
théorème FKG) : sur l'espace des sous-ensembles d'un alphabet fini `α` — ici les
« arêtes » —, deux **événements croissants** corrèlent positivement. En percolation,
les événements monotones croissants (plus d'arêtes ouvertes ⇒ l'événement tient
toujours, ex. la connexité) vérifient précisément cette corrélation.

Convention i18n EPIC #4980 : docstrings en français ici, le miroir anglais vit
dans `Percolation/Basic_en.lean` (byte-identiques hors docstrings/comments).
-/

namespace Percolation

open Finset

/-- **Inégalité de Harris–Kleitman (FKG fini)**, forme « deux croissants ».

Sur l'espace des configurations `Finset α` (une configuration = un sous-ensemble
d'arêtes ouvertes, `α` fini), deux événements **croissants** `𝒜` et `ℬ` corrèlent :

`#𝒜 * #ℬ ≤ 2 ^ Fintype.card α * #(𝒜 ∩ ℬ)`

Autrement dit, dans la mesure uniforme sur le treillis booléen `2^α`, la
probabilité de `𝒜 ∩ ℬ` est au moins le produit des probabilités — la **positivité
de l'association** (FKG), qui est la version finie du théorème de Harris–Kleitman.

C'est la brique du noyau fini : appliquée à la percolation de Bernoulli sur un
graphe fini à `|α|` arêtes, elle borne la corrélation de deux événements
croissants (ex. « deux sommets sont reliés » et « un sous-graphe est connexe »).
-/
theorem harris_kleitman_upper_upper {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    #𝒜 * #ℬ ≤ 2 ^ Fintype.card α * #(𝒜 ∩ ℬ) :=
  h𝒜.le_card_inter_finset hℬ

/-- **Inégalité de Harris–Kleitman**, forme « deux décroissants ».

La version duale : deux événements **décroissants** corrèlent également. Cet
énoncé dualise le précédent (passer au complémentaire). -/
theorem harris_kleitman_lower_lower {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
    #𝒜 * #ℬ ≤ 2 ^ Fintype.card α * #(𝒜 ∩ ℬ) :=
  h𝒜.le_card_inter_finset hℬ

end Percolation
