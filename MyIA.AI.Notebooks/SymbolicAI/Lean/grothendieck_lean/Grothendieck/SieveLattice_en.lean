/-
Grothendieck tribute — Part 6: Sieve pullback identities and lattice laws
Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #2162).

Part 1 (CategoryAndSites.lean) introduces sieves, the three axioms,
and the complete lattice on Sieve X. This module records the basic
identities of pullback along morphisms:

  - Pullback along the identity is the identity (pullback_id).
  - Pullback composes contravariantly (pullback_pullback).
  - Pullback of the bottom sieve is bottom (pullback_bot).
  - Pullback is monotone in the sieve (pullback_monotone).

These complete the picture started by Part 5 calibration P2
(pullback_top in Calibration.lean), and pave the way for Phase 3
work on sieve generation and sheafification.

Epic #1646, Phase 2 (#2159). All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck

namespace Grothendieck_en

open CategoryTheory

/-!
## Pullback along the identity is the identity

`Sieve.pullback (𝟙 X) S = S`. Pulling back along the identity does
nothing: `g` is in the pullback iff `g ≫ 𝟙 X = g` is in `S`.
-/

/-- CALIBRATION (ext + simp): pullback along the identity morphism
    is the identity transformation on sieves. -/
theorem pullback_id {C : Type*} [Category C] {X : C} (S : Sieve X) :
    (Sieve.pullback (𝟙 X) S) = S := by
  ext Y f
  simp [Sieve.pullback]

/-!
## Pullback composes contravariantly

For a sieve `S` on `X` and morphisms `f : Y ⟶ X`, `g : Z ⟶ Y`, pulling
back `S` along `f` and then along `g` gives the same sieve as pulling
back `S` along the composite `g ≫ f`.
-/

/-- CALIBRATION (ext + simp + assoc): pullback composes contravariantly.
    Pulling back along `g ≫ f` equals pulling back along `f` then `g`. -/
theorem pullback_pullback {C : Type*} [Category C] {X Y Z : C} (S : Sieve X)
    (f : Y ⟶ X) (g : Z ⟶ Y) :
    (Sieve.pullback g (Sieve.pullback f S)) = Sieve.pullback (g ≫ f) S := by
  ext W h
  simp [Sieve.pullback, Category.assoc]

/-!
## Pullback of the bottom sieve is the bottom sieve

The empty sieve has no arrows; pulling it back along any morphism still
gives the empty sieve. Dual to `pullback_top` (Calibration P2).
-/

/-- CALIBRATION (ext + simp): pullback of the bottom sieve along any
    morphism is the bottom sieve. -/
theorem pullback_bot {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X) :
    (Sieve.pullback f (⊥ : Sieve X)) = (⊥ : Sieve Y) := by
  ext Z g
  simp [Sieve.pullback]

/-!
## Pullback is monotone in the sieve

If `S ≤ T`, then for any `f : Y ⟶ X`, `Sieve.pullback f S ≤ Sieve.pullback f T`.
This is the order-theoretic component of pullback's functoriality.
-/

/-- CALIBRATION (intro + simp + apply): pullback is monotone in the sieve. -/
theorem pullback_monotone {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X)
    {S T : Sieve X} (hST : S ≤ T) :
    Sieve.pullback f S ≤ Sieve.pullback f T := by
  intro Z g hg
  simp [Sieve.pullback] at hg ⊢
  exact hST _ hg

end Grothendieck_en