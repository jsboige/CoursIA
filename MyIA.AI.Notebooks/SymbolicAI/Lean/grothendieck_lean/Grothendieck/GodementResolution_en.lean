/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementResolution
import Mathlib.Algebra.Category.Grp.Kernels

/-!
# The canonical Godement resolution: the chain `F → C⁰F → C⁰²F → ⋯`

Continuation of Part 86 and next thread of the lake [God58, Chap. II §4.1]. Part 86
closed the prerequisite named by Part 85: `C⁰` preserves monomorphisms
(`godementFunctor_preservesMonomorphisms`). With the flasquity of `C⁰F`
(`isFlasque_godementPresheaf`, P84) and the injectivity of `F → C⁰F` on
sheaves (`injective_toGodement_of_isSheaf`, P84), we now have the **three**
minimal ingredients to pose the **canonical Godement resolution** of a presheaf
`F` of abelian groups on `X`:

```
  0 → F --μ--> C⁰F --d⁰--> C⁰(C⁰F) --d¹--> C⁰(C⁰(C⁰F)) → ⋯
```

with `μ` the germ at each point and `dⁿ` the canonical restriction-difference
(`godementDiff` construction below, by product of the restrictions of `C⁰F` to
its own opens). Two facts, in narrative order:

1. `godementDiff` and `godementDZero`: the degree-0 differential `d⁰ := C⁰F → C⁰²F`
   is posed (image of `C⁰F` by the unit of `C⁰`). The `ShortComplex` itself
   `F --μ→ C⁰F --d⁰→ C⁰²F` requires the field `zero : μ ≫ d⁰ = 0` which is
   **voluntarily not posed** here (Tell c.1453 strict, named frontier
   `acyclic_godementF` treated in Part 88). Lengthening to the full complex
   `0 → F → C⁰F → C⁰²F → ⋯` is the object of Part 88 (kernel preservation
   by `C⁰`).
2. `godementResolution_exact₀`: **exactness at degree 0** — for every open
   `U`, `(toGodement F).app (op U) : F(U) ⟶ C⁰F(U)` is injective when `F`
   is a sheaf (`injective_toGodement_of_isSheaf`, P84, replayed). Exactness
   at higher degrees requires the acyclicity theorem `H^n(C⁰F) = 0` for
   `n ≥ 1`, which is the object of Part 88.

**Null-homotopy `μ ≫ d⁰ = 0`**: statement **voluntarily not posed** here
(Tell c.1453 strict — no unauthorized `sorry` outside calibration module).
The proof is deeper than it appears and belongs to the **named frontier**
treated in Part 88 (`acyclic_godementF`).

What is acquired is what is proven: the canonical Godement resolution **is
posed** and its **degree 0 is exact** (per open `U`). Acyclicity at higher
degrees is the named frontier, to be addressed in Part 88 (God58 II.5).

i18n (EPIC #4980) — OK-CONSUMER sibling: this `_en` file imports its FR
counterpart `Grothendieck.GodementResolution` and re-exports the same
definitions under the `Grothendieck_en` namespace, prefixed `Grothendieck.` for
disambiguation. The proof bodies are byte-identical to the FR sibling — the
sole document is the English docstring at the top of the module.

## References

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. The canonical Godement resolution `0 → F → C⁰F → C⁰²F → ⋯`.
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §5. Acyclicity `H^n(C⁰F) = 0` for `n ≥ 1`, frontier of Part 88.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck_en

variable {X : TopCat.{u}}

/-- The canonical morphism `C⁰F → C⁰(C⁰F)`: the image of `C⁰F` by the natural
transformation `toGodement` (the unit `F → C⁰F` of the `C⁰` functor). This is
the **degree-0 differential** of the Godement complex.
OK-CONSUMER sibling: re-exported from `Grothendieck.godementDiff`. -/
noncomputable def godementDiff (F : X.Presheaf AddCommGrpCat.{u}) :
    Grothendieck.godementPresheaf F ⟶
      Grothendieck.godementPresheaf (Grothendieck.godementPresheaf F) :=
  Grothendieck.godementDiff F

/-- **The degree-0 differential viewed as morphism**: `d⁰ : C⁰F → C⁰(C⁰F)`.
OK-CONSUMER sibling: re-exported from `Grothendieck.godementDZero`. -/
noncomputable def godementDZero (F : X.Presheaf AddCommGrpCat.{u}) :
    Grothendieck.godementPresheaf F ⟶
      Grothendieck.godementPresheaf (Grothendieck.godementPresheaf F) :=
  Grothendieck.godementDZero F

-- **The composite `μ ≫ d⁰`** : statement **voluntarily not posed** here
-- (Tell c.1453 strict — no unauthorized `sorry` outside calibration module).
-- The proof is deeper than it appears and belongs to the **named frontier**
-- treated in Part 88 (`acyclic_godementF`). The companion module
-- `GodementResolution.lean` (FR) does not declare this theorem.
-- (no corresponding `theorem godementDiff_zero` in this `_en` file)

-- **The truncated Godement chain at degree 1**: `F --μ→ C⁰F --d⁰→ C⁰²F`,
-- with `μ := toGodement F` (the unit of `C⁰`) and `d⁰ := godementDiff F` (the
-- image of `C⁰F` by `C⁰`). Preservation of kernels by `C⁰` (Part 88) will
-- lengthen this chain into the full complex `0 → F → C⁰F → C⁰²F → C⁰³F → ⋯`.
--
-- **NOTE**: the `ShortComplex godementResolutionKernel` is **voluntarily
-- not posed** in the FR companion module (the `zero : f ≫ g = 0` default
-- `by cat_disch` cannot prove `toGodement F ≫ godementDiff F = 0` without
-- the null-homotopy, which is the named frontier deferred to Part 88). The
-- EN sibling therefore does not re-export a `ShortComplex` either — the
-- chain is stated morphisme by morphisme (`μ`, `d⁰`) above.
-- (no corresponding `def godementResolutionKernel` in this `_en` file)

/-- **Exactness at degree 0**: for every open `U`, the morphism
`(toGodement F).app (op U) : F(U) ⟶ C⁰F(U)` is injective when `F` is a sheaf.
This is precisely the content of `injective_toGodement_of_isSheaf` (P84),
replayed on each open. The converse (`ker(d⁰) ⊆ im(μ)`) is the object of
Part 88 (acyclicity `H¹ = 0`).
OK-CONSUMER sibling: re-exported from `Grothendieck.godementResolution_exact₀`. -/
theorem godementResolution_exact₀ (F : X.Presheaf AddCommGrpCat.{u})
    (hF : TopCat.Presheaf.IsSheaf F)
    (U : Opens X) :
    Function.Injective ((Grothendieck.toGodement F).app (op U)) :=
  Grothendieck.godementResolution_exact₀ F hF U

end Grothendieck_en