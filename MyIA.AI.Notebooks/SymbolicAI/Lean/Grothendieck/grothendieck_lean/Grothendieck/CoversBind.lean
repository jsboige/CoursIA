/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hommage Grothendieck — Partie 46 : forme flèche de la transitivité indexée (bind)

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Les parties 1-45 ont établi les fondamentaux : catégories, cribles,
topologies, lois de treillis, identités de pullback, bases de faisceaux,
clôture couvrante, calibration, sous-canonicalité, topologies denses,
faisceaux, hom interne, cohomologie de Čech, limite de Mayer-Vietoris,
extensions de Kan, adjonctions, monades, équivalences, catégories monoïdales,
la construction de Grothendieck, l'image directe/exceptionnelle, la forme
flèche de la couverture, les lois de cohérence du pseudo-foncteur pullback,
les lois de treillis indexées, la forme flèche des topologies extrémales et
la forme flèche de l'adjonction pushforward-pullback.

Cette partie applique le fil conducteur « forme flèche » à la transitivité
indexée des couvertures — le « bind » des cribles. Mathlib fournit la
transitivité ponctuelle `GrothendieckTopology.bind_covering` et la forme
flèche de la transitivité à couverture constante
`GrothendieckTopology.arrow_trans`, mais aucune loi ne relie la forme flèche
`J.Covers` au crible indexé `Sieve.bind S T`. On comble le trou avec
`covers_bind` (la forme flèche de la transitivité indexée : si `S` couvre
`f` et si chaque crible `T hg` recouvre son objet de départ, alors le bind
couvre `f`), ses corollaires (`covers_of_bind`, la forme flèche inverse
portée par l'inclusion `bind_le` ; `covers_bind_id`, la retombée ponctuelle
sur l'identité) et les deux identités de crible sous-jacentes, absentes de
Mathlib : `bind_le` (`Sieve.bind S T ≤ S`) et `bind_top` (le bind par le
crible top est l'identité).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck.CoversBind

open CategoryTheory

/-!
## Section 1 : l'inclusion du bind dans le crible

Le crible `Sieve.bind S T` est contenu dans `S` : chaque flèche du bind est
une précomposition `k ≫ g` d'une flèche `g ∈ S`, et un crible est clos par
précomposition (`S.downward_closed`). La forme flèche de cette inclusion est
la réciproque naturelle de `covers_bind` : si le bind couvre `f`, alors `S`
couvre `f` (un sur-ensemble d'une couverture est une couverture).
-/

/-- Le bind est contenu dans le crible de départ : `Sieve.bind S T ≤ S`.
    Preuve : une flèche du bind est une précomposition `k ≫ g` d'une flèche
    `g ∈ S`, et un crible est clos par précomposition (`S.downward_closed`). -/
theorem bind_le {C : Type*} [Category C] {X : C} (S : Sieve X)
    (T : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y) : Sieve.bind S T ≤ S := by
  intro Y f hf
  rcases hf with ⟨Z, g, hg, k, hkT, rfl⟩
  exact S.downward_closed k g

/-- La forme flèche de l'inclusion : si le bind couvre `f`, alors `S` couvre
    `f`. Preuve : `covers_iff`, monotonie du pullback (`Sieve.pullback_monotone`)
    avec `bind_le`, puis `superset_covering`. -/
theorem covers_of_bind {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (S : Sieve X) (T : ∀ ⦃Z : C⦄ ⦃g : Z ⟶ X⦄, S g → Sieve Z) (f : Y ⟶ X)
    (h : J.Covers (Sieve.bind S T) f) : J.Covers S f := by
  rw [GrothendieckTopology.covers_iff] at h ⊢
  exact J.superset_covering (Sieve.pullback_monotone f (bind_le S T)) h

/-!
## Section 2 : la forme flèche de la transitivité indexée

C'est le théorème central de cette partie, le gap de Mathlib. La
transitivité ponctuelle `bind_covering` et sa forme flèche à couverture
constante `arrow_trans` sont deux faces extrêmes ; `covers_bind` les réunit :
l'indexation est portée par `T : ∀ ⦃Z⦄ ⦃g : Z ⟶ X⦄, S g → Sieve Z`, et
l'hypothèse de recouvrement devient `∀ g ∈ S, J.Covers (T hg) (𝟙 Z)` — la
forme flèche de `T hg ∈ J Z`, un crible couvrant l'identité de son objet
équivaut à appartenir à la topologie. La preuve utilise la transitivité de
la topologie, via sa forme flèche `J.arrow_trans` spécialisée en
`R := Sieve.bind S T`, puis l'unité du bind `Sieve.le_pullback_bind` qui
relie chaque `T hg` au pullback du bind le long de la flèche `g`.
-/

/-- La forme flèche de la transitivité indexée : si `S` couvre `f` et si
    chaque crible `T hg` recouvre son objet de départ — `J.Covers (T hg) (𝟙 Z)`,
    la forme flèche de `T hg ∈ J Z` — alors le bind `Sieve.bind S T` couvre
    `f`. Preuve : instantiation de la forme flèche de la transitivité de
    Mathlib (`J.arrow_trans`, R := `Sieve.bind S T`) ; chaque flèche `g ∈ S`
    se relève par l'unité du bind `Sieve.le_pullback_bind` — `T hg` est un
    sous-crible du pullback du bind le long de `g` — et l'hypothèse indexée
    `hT`. -/
theorem covers_bind {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (S : Sieve X) (f : Y ⟶ X) (hS : J.Covers S f)
    (T : ∀ ⦃Z : C⦄ ⦃g : Z ⟶ X⦄, S g → Sieve Z)
    (hT : ∀ ⦃Z : C⦄ ⦃g : Z ⟶ X⦄ (hg : S g), J.Covers (T hg) (𝟙 Z)) :
    J.Covers (Sieve.bind S T) f := by
  exact J.arrow_trans f S (Sieve.bind S T) hS (by
    intro Z g hg
    rw [GrothendieckTopology.covers_iff]
    have hTg : J.Covers (T hg) (𝟙 Z) := hT hg
    rw [GrothendieckTopology.covers_iff] at hTg
    rw [Sieve.pullback_id] at hTg
    exact J.superset_covering (Sieve.le_pullback_bind S T g hg) hTg)

/-!
## Section 3 : la retombée ponctuelle

Quand la flèche est l'identité `𝟙 X`, la forme flèche retombe sur
l'appartenance ponctuelle : `J.Covers S (𝟙 X) ↔ S ∈ J X` (`covers_iff` +
`Sieve.pullback_id`). La transitivité indexée se spécialise donc en la
version ponctuelle du bind — l'analogue flèche de `bind_covering` — avec une
hypothèse uniformément exprimée en couvertures.
-/

/-- La transitivité indexée, spécialisée sur l'identité :
    `J.Covers S (𝟙 X) → (∀ g ∈ S, J.Covers (T hg) (𝟙 Z)) →
    J.Covers (Sieve.bind S T) (𝟙 X)` — l'analogue flèche de `bind_covering`.
    Preuve : instantiation de `covers_bind` en `f := 𝟙 X`. -/
theorem covers_bind_id {C : Type*} [Category C] {X : C} (J : GrothendieckTopology C)
    (S : Sieve X) (hS : J.Covers S (𝟙 X))
    (T : ∀ ⦃Z : C⦄ ⦃g : Z ⟶ X⦄, S g → Sieve Z)
    (hT : ∀ ⦃Z : C⦄ ⦃g : Z ⟶ X⦄ (hg : S g), J.Covers (T hg) (𝟙 Z)) :
    J.Covers (Sieve.bind S T) (𝟙 X) := by
  exact covers_bind J S (𝟙 X) hS T hT

/-!
## Section 4 : le bind par le crible top

Quand chaque `T hg` est le crible top, le bind restitue exactement `S` :
chaque flèche `g ∈ S` se précompose par l'identité (`g = 𝟙 ≫ g`), et
réciproquement le bind est contenu dans `S` (`bind_le`). Cette identité de
crible, absente de Mathlib, donne la forme flèche : couvrir par
`Sieve.bind S (fun ⦃Z⦄ ⦃g : Z ⟶ X⦄ _ => ⊤)` équivaut à couvrir par `S`.
-/

/-- Le bind par le crible top est l'identité :
    `Sieve.bind S (fun ⦃Y⦄ ⦃f : Y ⟶ X⦄ _ => ⊤) = S`.
    Preuve : anti-symétrie entre `bind_le` et l'inclusion inverse — chaque
    `g ∈ S` se précompose par l'identité, `g = 𝟙 ≫ g`, et le crible top
    accepte toute flèche. -/
theorem bind_top {C : Type*} [Category C] {X : C} (S : Sieve X) :
    Sieve.bind S (fun ⦃Y : C⦄ ⦃_ : Y ⟶ X⦄ _ => (⊤ : Sieve Y)) = S := by
  apply le_antisymm
  · exact bind_le S (fun ⦃Y : C⦄ ⦃_ : Y ⟶ X⦄ _ => (⊤ : Sieve Y))
  · intro Y f hS
    exact ⟨Y, 𝟙 Y, f, hS, by simp, by simp⟩

/-- La forme flèche du bind par le crible top :
    `J.Covers (Sieve.bind S (fun ⦃Z⦄ ⦃g : Z ⟶ X⦄ _ => ⊤)) f ↔ J.Covers S f`.
    Preuve : réécriture de l'identité `bind_top`. -/
theorem covers_bind_top {C : Type*} [Category C] {X Y : C} (J : GrothendieckTopology C)
    (S : Sieve X) (f : Y ⟶ X) :
    J.Covers (Sieve.bind S (fun ⦃Z : C⦄ ⦃_ : Z ⟶ X⦄ _ => (⊤ : Sieve Z))) f ↔
      J.Covers S f := by
  rw [bind_top S]

end Grothendieck.CoversBind
