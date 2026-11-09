/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 43 : lois de treillis indexées de la forme flèche

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-42 ont établi les fondamentaux : catégories, cribles,
topologies, lois de treillis, identités de pullback, bases de faisceaux,
clôture couvrante, calibration, sous-canonicalité, topologies denses,
faisceaux, hom interne, cohomologie de Čech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, équivalences, catégories monoïdales,
la construction de Grothendieck, l'image directe/exceptionnelle, la forme
flèche de la couverture et les lois de cohérence du pseudo-foncteur pullback.
La partie 39 (`TopologyLattice.lean`) a établi les lois de treillis
ponctuelles des topologies — borne inférieure, borne supérieure — et leurs
traductions à la forme flèche pour les opérations **binaires**. Cette partie
complète le tableau avec les opérations **indexées** : le `sInf` d'une famille
(`mem_sInf` de Mathlib) et le `sSup` d'une famille (`sSup_covering`), dont on
donne les traductions à la forme flèche `J.Covers`.

Le fil conducteur : tout énoncé ponctuel `S ∈ J X` admet un jumeau en forme
flèche `J.Covers S f` (par `covers_iff`, `S.pullback f ∈ J Y`). La partie 39
a montré le motif pour `⊓` et `⊔` ; ici on le généralise aux bornes indexées.

Les énoncés suivants complètent exactement ce que `TopologyLattice.lean`
n'avait pas : `sInf_covering` et `sInf_covers` (le dual indexé de la paire)
et `sSup_covers` (la forme flèche du `sSup`, absente alors que
`sSup_covering` y figurait).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Grothendieck.TopologyLattice

namespace Grothendieck.CoversLattice

open CategoryTheory

/-!
## Section 1 : borne inférieure indexée (sInf)

L'instance `CompleteLattice` de Mathlib définit le `sInf` d'une famille de
topologies comme le `sInf` ponctuel des familles de cribles, et fournit la
caractérisation `mem_sInf` : `S ∈ sInf s X ↔ ∀ J ∈ s, S ∈ J X`. On en donne
la traduction à la forme flèche `J.Covers`.
-/

/-- La borne inférieure d'une famille est ponctuelle : `S ∈ sInf s X` si et
    seulement si `S` est couvert par chaque topologie de la famille.
    Preuve : c'est exactement `mem_sInf` de Mathlib. -/
theorem sInf_covering {C : Type*} [Category C] {s : Set (GrothendieckTopology C)}
    {X : C} (S : Sieve X) :
    S ∈ sInf s X ↔ ∀ J ∈ s, S ∈ J X := by
  exact GrothendieckTopology.mem_sInf s S

/-- Traduction de `sInf_covering` à la forme flèche : couvrir par le `sInf`
    d'une famille équivaut à couvrir par chaque topologie de la famille.
    Preuve : `covers_iff` des deux côtés — le membre gauche est
    `S.pullback f ∈ sInf s Y`, le membre droit est la quantification
    `∀ J ∈ s, S.pullback f ∈ J Y` — puis `sInf_covering`. -/
theorem sInf_covers {C : Type*} [Category C] {s : Set (GrothendieckTopology C)}
    {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (sInf s).Covers S f ↔ ∀ J ∈ s, J.Covers S f := by
  rw [GrothendieckTopology.covers_iff]
  constructor
  · intro hS J hJ
    rw [GrothendieckTopology.covers_iff]
    exact (sInf_covering (S.pullback f)).mp hS J hJ
  · intro h
    rw [← GrothendieckTopology.covers_iff]
    exact (sInf_covering (S.pullback f)).mpr h

/-!
## Section 2 : borne supérieure indexée (sSup)

La borne supérieure `sSup s` d'une famille est la topologie engendrée : un
crible y est couvert si et seulement s'il est couvert par **toute** topologie
`K` au-dessus de tous les membres de `s`. C'est la caractérisation de la
partie 39 (`sSup_covering`) — la réciproque de l'union ponctuelle, qui n'est
pas stable par pullback. On en donne ici la traduction à la forme flèche,
qui était la pièce manquante.
-/

/-- Traduction de `sSup_covering` à la forme flèche : `(sSup s).Covers S f`
    si et seulement si `K.Covers S f` pour toute topologie `K` au-dessus de
    tous les membres de `s`.
    Preuve : `covers_iff` des deux côtés (les deux membres sont des
    appartenances `∈ sSup s Y` / `∈ K Y` sur `S.pullback f`) puis
    `sSup_covering`. -/
theorem sSup_covers {C : Type*} [Category C] {s : Set (GrothendieckTopology C)}
    {X Y : C} (S : Sieve X) (f : Y ⟶ X) :
    (sSup s).Covers S f ↔
      ∀ K : GrothendieckTopology C, (∀ J ∈ s, J ≤ K) → K.Covers S f := by
  rw [GrothendieckTopology.covers_iff]
  constructor
  · intro hS K hK
    rw [GrothendieckTopology.covers_iff]
    exact (Grothendieck.TopologyLattice.sSup_covering (s := s) (S.pullback f)).mp hS K hK
  · intro h
    rw [← GrothendieckTopology.covers_iff]
    exact (Grothendieck.TopologyLattice.sSup_covering (s := s) (S.pullback f)).mpr h

end Grothendieck.CoversLattice
