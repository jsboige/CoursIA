/-
Grothendieck tribute — Part 65: characterization of the equalizer sheaf condition.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #1646).

Part 63 (`SheafCondition.lean`) linked the **equalizer-product sheaf condition**
to the definition `Presieve.IsSheaf J P`. Part 7 (`SheafBasics.lean`) showed that
`IsSheaf`/`IsSeparated` are monotone descending along `J₁ ≤ J₂`. This module pushes
both threads **into the explicit equalizer form**:

  - `equalizer_sheaf_condition_mono`: the equalizer condition descends monotone —
    if `J₁ ≤ J₂`, then any presheaf satisfying the equalizer condition for the
    finer topology `J₂` satisfies it for `J₁` as well. This is the "equalizer-form"
    version of `isSheaf_of_le` (Part 7).
  - `equalizer_sheaf_condition_iff_separated_compatible`: the equalizer condition
    is equivalent exactly to the conjunction of **separatedness** and the
    **existence of an amalgamation** for every compatible family. This is the
    "equalizer-form" version of
    `isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor` (Mathlib): a
    presheaf is a sheaf in the equalizer sense iff it is separated and every
    compatible family amalgamates — separatedness alone gives uniqueness, the
    existence is precisely what the sheaf condition adds.

References:
  - Stacks Project, tag 00VM ("sheaves on sites via equalizers").
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Ch. III §4 — the sheaf condition as gluing + separatedness.
  - M. Kashiwara, P. Schapira, *Categories and Sheaves* [KS06] §17.

All `sorry`s eliminated at creation.
-/

import Grothendieck.SheafBasics
import Grothendieck.SheafCondition
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Sites.SheafOfTypes

namespace Grothendieck_en

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section Contenu

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C)
  (P : Cᵒᵖ ⥤ Type (max v u))

/-- **The equalizer condition descends along `J₁ ≤ J₂`.**

If `J₁ ≤ J₂` (every covering sieve for `J₁` is covering for `J₂`), then a
presheaf satisfying the equalizer-product sheaf condition for the finer topology
`J₂` satisfies it for `J₁` as well. This is the "equalizer-form" version of
`isSheaf_of_le` from Part 7: being a sheaf in the equalizer sense is monotone
decreasing in the topology. Reference: MM92 Ch. III §4; Stacks 00VM. -/
theorem equalizer_sheaf_condition_mono {J₁ : GrothendieckTopology C} {J₂ : GrothendieckTopology C}
    (h : J₁ ≤ J₂) :
    (∀ ⦃X : C⦄ (S : Sieve X), S ∈ J₂ X → Nonempty (IsLimit (Fork.ofι _ (Equalizer.Sieve.w P S))))
      → (∀ ⦃X : C⦄ (S : Sieve X), S ∈ J₁ X → Nonempty (IsLimit (Fork.ofι _ (Equalizer.Sieve.w P S)))) := by
  intro h₂
  rw [← Grothendieck.sheaf_iff_equalizer_sieve J₁ P]
  rw [← Grothendieck.sheaf_iff_equalizer_sieve J₂ P] at h₂
  exact Grothendieck.isSheaf_of_le h h₂

/-- **The equalizer condition is equivalent to: separated and every compatible family amalgamates.**

A presheaf is a sheaf in the equalizer-product sense iff it is **separated**
(for every covering sieve, every compatible family has at most one amalgamation)
**and** every compatible family amalgamates (at least one amalgamation).
Separatedness carries uniqueness; the existence of the amalgamation is precisely
the extra condition the sheaf condition adds. This is the "equalizer-form"
version of `isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor` (Mathlib).
Reference: MM92 Ch. III §4; Stacks 00VM. -/
theorem equalizer_sheaf_condition_iff_separated_compatible :
    (∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → Nonempty (IsLimit (Fork.ofι _ (Equalizer.Sieve.w P S))))
      ↔ Presieve.IsSeparated J P ∧
        (∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → ∀ x : Presieve.FamilyOfElements P (S : Presieve X),
          x.Compatible → ∃ t, x.IsAmalgamation t) := by
  rw [← Grothendieck.sheaf_iff_equalizer_sieve J P]
  constructor
  · intro h
    constructor
    · intro X S hS
      exact (Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor.2 (h S hS)).1
    · intro X S hS x hx
      exact (Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor.2 (h S hS)).2 x hx
  · intro h X S hS
    exact Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor.1 ⟨h.1 S hS, h.2 S hS⟩

end Contenu

end Grothendieck_en
