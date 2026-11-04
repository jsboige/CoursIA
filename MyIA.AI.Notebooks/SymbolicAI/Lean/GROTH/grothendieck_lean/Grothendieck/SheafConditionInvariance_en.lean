/-
Grothendieck tribute — Part 64: invariance of the equalizer sheaf condition.

Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #1646).

Part 63 (`SheafCondition.lean`) formalised the **equalizer-product sheaf
condition** in three forms (sieves, arrow families, pretopology) and linked it
to the definition `Presieve.IsSheaf J P`. Part 7 (`SheafBasics.lean`) showed
that the `IsSheaf`/`IsSeparated` conditions are invariant under isomorphism and
natural equivalence of presheaves.

This module pushes that invariance **all the way to the equalizer form itself**:

  - `equalizer_sheaf_condition_iff_of_nat_equiv`: the equalizer sheaf condition
    (sieve form) is preserved in both directions by a componentwise natural
    equivalence. This is the "equalizer-form" version of `isSheaf_iff_of_nat_equiv`
    from Part 7 — neither Mathlib nor Part 63 states it in this form.
  - `equalizer_arrows_iff_sieve_generate`: for a covering family
    `π : (i : I) → X i ⟶ B`, the equalizer condition (arrow form, `Arrows.w`)
    is equivalent to the equalizer condition (sieve form, `Sieve.w`) on the
    sieve `Sieve.generate (ofArrows X π)` it generates. This is the operational
    bridge between the two forms: checking the equalizer on a covering family
    amounts to checking it on its generated sieve.

References:
  - Stacks Project, tag 00VM ("sheaves on sites via equalizers").
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Ch. III §4 — the sheaf condition is a property of the isomorphism class
    of the presheaf.
  - M. Kashiwara, P. Schapira, *Categories and Sheaves* [KS06] §17.

All `sorry`s eliminated at creation.
-/

import Grothendieck.SheafBasics
import Grothendieck.SheafCondition
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
import Mathlib.CategoryTheory.Sites.SheafOfTypes

namespace Grothendieck_en

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

section Contenu

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C)
  (P : Cᵒᵖ ⥤ Type (max v u))

/-- **Invariance of the equalizer condition under natural equivalence (sieve form).**

If two presheaves `P₁` and `P₂` are related componentwise by a family of
natural equivalences `e : ∀ {X}, P₁(X) ≃ P₂(X)`, then the equalizer-product sheaf
condition of `P₁` (every covering sieve gives an equalizer) is equivalent to that
of `P₂`. The property "being a sheaf in the equalizer sense" therefore depends
only on the natural-equivalence class of the presheaf. This strengthens
`isSheaf_iff_of_nat_equiv` from Part 7: we are not satisfied with an invariance
of `Presieve.IsSheaf`, we transport it into the explicit equalizer form.
Reference: MM92 Ch. III §4. -/
theorem equalizer_sheaf_condition_iff_of_nat_equiv
    {P₁ : Cᵒᵖ ⥤ Type (max v u)} {P₂ : Cᵒᵖ ⥤ Type (max v u)}
    (e : ∀ ⦃X : C⦄, P₁.obj (Opposite.op X) ≃ P₂.obj (Opposite.op X))
    (he : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₁.obj (Opposite.op Y)),
      e (P₁.map f.op x) = P₂.map f.op (e x)) :
    (∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X →
      Nonempty (IsLimit (Fork.ofι _ (Equalizer.Sieve.w P₁ S))))
      ↔ (∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X →
        Nonempty (IsLimit (Fork.ofι _ (Equalizer.Sieve.w P₂ S)))) := by
  rw [← Grothendieck.sheaf_iff_equalizer_sieve J P₁]
  rw [← Grothendieck.sheaf_iff_equalizer_sieve J P₂]
  exact Grothendieck.isSheaf_iff_of_nat_equiv J e he

/-- **The equalizer condition (arrows) is equivalent to the equalizer condition (generated sieve).**

For a covering family `π : (i : I) → X i ⟶ B` of a pretopology, the sheaf
condition expressed on the family `ofArrows X π` (arrow form,
`Equalizer.Presieve.Arrows.w`) is equivalent to the sheaf condition expressed on
the sieve `Sieve.generate (ofArrows X π)` it generates (sieve form,
`Equalizer.Sieve.w`). This is the operational bridge between the two forms:
checking the equalizer on a covering family amounts to checking it on its
generated sieve — which legitimises testing the sheaf condition on a basis of
coverings rather than on all sieves. Reference: Stacks 00VM. -/
theorem equalizer_arrows_iff_sieve_generate [HasPullbacks C]
    {B : C} {I : Type (max v u)} (X : I → C)
    (π : (i : I) → X i ⟶ B) :
    Nonempty (IsLimit (Fork.ofι _ (Equalizer.Presieve.Arrows.w P X π))) ↔
      Nonempty (IsLimit (Fork.ofι _ (Equalizer.Sieve.w P (Sieve.generate (Presieve.ofArrows X π))))) := by
  rw [← Equalizer.Presieve.Arrows.sheaf_condition P X π]
  rw [← Equalizer.Sieve.equalizer_sheaf_condition P (Sieve.generate (Presieve.ofArrows X π))]
  exact Presieve.isSheafFor_iff_generate (Presieve.ofArrows X π)

end Contenu

end Grothendieck_en
