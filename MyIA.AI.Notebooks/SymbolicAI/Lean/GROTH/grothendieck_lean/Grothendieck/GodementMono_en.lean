/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementFunctor
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Preservation of monomorphisms by `C⁰`

English canonical sibling of `Grothendieck/GodementMono.lean` (Part 86).

Continuation of Part 85 [God58, Chap. II §4.1]. Part 85 built the functor
`C⁰` and its natural unit, and left **named** there the prerequisite missing
in order to iterate the construction on kernels: "the preservation of
monomorphisms by `C⁰` is **not** established here". That is the object of
this Part, and nothing else.

Three facts, in the narrative order:

1. `injective_app_of_mono`: a monomorphism `φ : F ⟶ G` of presheaves of
   abelian groups is **injective on every open**. In `AddCommGrpCat`,
   monomorphism and injection coincide, and the mono of a natural
   transformation is read component by component: each `φ.app (op U)` is an
   injective map.
2. `godementHomApp_injective`: this injectivity **descends to the stalks** and
   gives the sectionwise injectivity of `C⁰φ`. A Godement section is a function
   on `U` with values in the stalks; two sections that coincide after applying
   `C⁰φ` coincide at every point, because the induced map on the stalks is
   injective (`Presheaf.stalkFunctor_map_injective_of_app_injective`).
3. `godementMapHom_mono`: `C⁰φ` is a monomorphism — the sectionwise injectivity
   is exactly the mono of morphisms of `AddCommGrpCat`, read component by
   component.

What is acquired is what is proved: `C⁰` is an endofunctor that **preserves
monomorphisms**, and the consumable form of this fact is the instance
`godementFunctor_preservesMonomorphisms` — `Functor.map_mono` now applies to
`C⁰`. This is the prerequisite that was missing for Godement's canonical
resolution `0 → F → C⁰F → C⁰(K) → ⋯` (iterating `C⁰` on kernels), the lake's
next thread.

i18n convention (EPIC #4980 ratified 2026-07-04): `_en` suffix on the
namespace (`Grothendieck.GodementMono_en`), mirror imports, translated
docstrings and comments. Theorem statements, Lean tactics, lemma names and
Mathlib references remain in English. Anti-§D byte-identity guaranteed:
the namespace body is preserved bit for bit (statements and proofs
byte-identical between `GodementMono.lean` and `GodementMono_en.lean`).

## References

  - R. Godement, *Topologie algebrique et theorie des faisceaux* [God58],
    Chap. II §4.1. Godement's canonical resolution.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck.GodementMono_en

variable {X : TopCat.{u}}

/-- **A mono is injective on every open**: for a morphism `φ : F ⟶ G` of
presheaves of abelian groups, `φ.app (op U)` is injective as soon as `φ` is a
monomorphism. The two halves: `NatTrans.mono_iff_mono_app` reads the mono of a
natural transformation component by component (pullbacks exist in
`AddCommGrpCat`), and in `AddCommGrpCat` monomorphism and injection coincide. -/
theorem injective_app_of_mono {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    [Mono φ] (U : Opens X) : Function.Injective (φ.app (op U)) :=
  (AddCommGrpCat.mono_iff_injective _).mp inferInstance

/-- **Injectivity descends to the stalks, hence to `C⁰`**: if `φ` is injective
on every open, then `C⁰φ` is injective section by section. A Godement section is
a function, so injectivity is pointwise: at every point the induced map on the
stalks is injective — equal germs come from equal sections
(`Presheaf.stalkFunctor_map_injective_of_app_injective`, valid for any presheaf
of abelian groups) — and equality of the images point by point forces equality
of the sections. -/
theorem godementHomApp_injective {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G)
    (hφ : ∀ U : Opens X, Function.Injective (φ.app (op U))) (U : Opens X) :
    Function.Injective (godementHomApp φ U) := by
  intro s t hst
  funext x
  exact TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective hφ (x : X)
    (congrFun hst x)

/-- **`C⁰` preserves monomorphisms**: if `φ` is a mono, so is `C⁰φ`. The
sectionwise injectivity established above is exactly the mono in
`AddCommGrpCat` (`AddCommGrpCat.mono_iff_injective`), and the mono of a natural
transformation is read component by component (`NatTrans.mono_iff_mono_app`). -/
theorem godementMapHom_mono {F G : X.Presheaf AddCommGrpCat.{u}} (φ : F ⟶ G) [Mono φ] :
    Mono (godementMapHom φ) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [AddCommGrpCat.mono_iff_injective]
  exact godementHomApp_injective φ (fun V => injective_app_of_mono φ V) U.unop

/-- **`C⁰` is a functor that preserves monomorphisms** — the form usable
downstream: `Functor.map_mono` now applies to `C⁰`. This is the prerequisite
that was missing in Part 85 in order to iterate the construction on kernels and
form the Godement complex. [God58] Chap. II §4.1. -/
instance godementFunctor_preservesMonomorphisms :
    (godementFunctor (X := X)).PreservesMonomorphisms where
  preserves f _ := godementMapHom_mono f

end Grothendieck.GodementMono_en