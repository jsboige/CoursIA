import Mathlib.Combinatorics.SetFamily.HarrisKleitman

/-! # Noyau fini de la percolation — module d'amorce

Le but de ce lake (`percolation_lean`) est de formaliser le **noyau fini** de la
percolation de Bernoulli sur un graphe fini, avant le pont vers le cours / la
série ICT (voir `#14871`).

Ce jalon couvre le **cas uniforme** `p = 1/2` (mesure uniforme sur le cube
booléen `2^α`) : le passage à la mesure produit de Bernoulli de paramètre
général `p` reste hors de ce jalon.

Le cœur de ce noyau est l'inégalité de **Harris–Kleitman uniforme** (forme finie du
théorème FKG) : sur l'espace des sous-ensembles d'un alphabet fini `α` — ici les
« arêtes » —, deux **événements croissants** corrèlent positivement. En percolation,
les événements monotones croissants (plus d'arêtes ouvertes ⇒ l'événement tient
toujours, ex. la connexité) vérifient précisément cette corrélation.

Convention i18n EPIC #4980 : docstrings en français ici, le miroir anglais vit
dans `Percolation/Basic_en.lean` (byte-identiques hors docstrings/comments).
-/

namespace Percolation

open Finset

/-- **Inégalité de Harris–Kleitman uniforme (FKG fini, cas `p = 1/2`)**, forme
« deux croissants ».

Sur l'espace des configurations `Finset α` (une configuration = un sous-ensemble
d'arêtes ouvertes, `α` fini), deux événements **croissants** `𝒜` et `ℬ` corrèlent :

`#𝒜 * #ℬ ≤ 2 ^ Fintype.card α * #(𝒜 ∩ ℬ)`

Autrement dit, dans la **mesure uniforme** sur le treillis booléen `2^α` (soit la
percolation indépendante à probabilité d'ouverture `p = 1/2`), la probabilité de
`𝒜 ∩ ℬ` est au moins le produit des probabilités — la **positivité de
l'association** (FKG), version finie du théorème de Harris–Kleitman.

Le passage à la mesure produit de Bernoulli de paramètre général `p` reste hors
de ce jalon. La brique s'applique ici au cas uniforme : à `p = 1/2` sur un graphe
fini à `|α|` arêtes, elle borne la corrélation de deux événements croissants (ex.
« deux sommets sont reliés » et « un sous-graphe est connexe »).
-/
theorem harris_kleitman_upper_upper {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
    (hℬ : IsUpperSet (ℬ : Set (Finset α))) :
    #𝒜 * #ℬ ≤ 2 ^ Fintype.card α * #(𝒜 ∩ ℬ) :=
  h𝒜.le_card_inter_finset hℬ

/-- **Inégalité de Harris–Kleitman uniforme (FKG fini, cas `p = 1/2`)**, forme
« deux décroissants ».

La version duale : deux événements **décroissants** corrèlent également. Cet
énoncé dualise le précédent (passer au complémentaire) ; comme lui, il est au
cas uniforme `p = 1/2`, le cas Bernoulli-`p` général restant hors de ce jalon. -/
theorem harris_kleitman_lower_lower {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
    #𝒜 * #ℬ ≤ 2 ^ Fintype.card α * #(𝒜 ∩ ℬ) :=
  h𝒜.le_card_inter_finset hℬ

end Percolation
