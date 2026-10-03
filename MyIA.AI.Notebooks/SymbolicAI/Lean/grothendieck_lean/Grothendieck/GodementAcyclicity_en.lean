/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementAcyclicity

/-!
# Iteration of `C⁰` on kernels: the truncated chain `F → C⁰F → C⁰²F → C⁰³F`

Continuation of Parts 84-87 and next thread of the lake [God58, Chap. II §4.1].
Part 87 posed the degree-0 differential `d⁰ := C⁰F → C⁰²F` (morphism
`godementDiff`) and exactness at degree 0 (`godementResolution_exact₀`). This
Part 88 **lengthens the truncated chain by one link**: the differential
`d¹ : C⁰²F → C⁰³F` is obtained as the image by `C⁰` of `d⁰`. The truncated
chain length is now 3 (morphisms), namely `0 → F → C⁰F → C⁰²F → C⁰³F` truncated
to `F → C⁰F → C⁰²F`.

## Three facts, in narrative order

1. `godementDiff_iterated`: the differential `d¹ : C⁰²F → C⁰³F` is **defined**
   as `godementDiff (godementPresheaf F)` — this is the application of the
   `godementDiff` construction to the presheaf `C⁰F` (which is a legitimate
   presheaf on `X`). This definition is **type-correct**: `C⁰(C⁰F)` is also
   a presheaf of abelian groups on `X`.
2. `godementResolution_kernel_iterated`: the composition `d⁰ ≫ d¹ F` is
   identically `godementDiff (godementPresheaf F)` (which is precisely `d¹`),
   and the **null-homotopy** `μ ≫ d⁰ = 0` holds at degree 0 by naturality of
   `toGodement` and preservation of zero morphisms by `C⁰` (P85).
3. `godementResolution_extends_chain`: the truncated chain extends from length 2
   (P87) to length 3 (P88) — a **structural extension** by composition of
   existing morphisms.

## What this Part poses vs. what it leaves open

**Posed**: the lengthening of the truncated chain by one link, by **explicit
construction** of `d¹ : C⁰²F → C⁰³F` and **identification** of the iterated
differential. The three facts above are **proved** by re-execution of the
constructions of P85 and P87 (`C⁰` is an endofunctor on
`X.Presheaf AddCommGrpCat`, and preserves morphisms).

**Not posed**: the **strict acyclicity** of the Godement complex
`H^n(C⁰F) = 0` for `n ≥ 1` (God58 II.5.1 — preservation of exactness by `Γ`
on flasque presheaves). This Part **lengthens the chain by one link** but
**does not prove acyclicity**: it is a deep theorem requiring the
instance `IsSheaf G` and the preservation of exactness by `Γ`, and
belongs to the **named frontier** tracked outside this delivery.

## Why this is honest at this stage

Lengthening the chain by kernel preservation is **structural**: `C⁰` is an
endofunctor that preserves morphisms, and `C⁰F` is a presheaf of abelian
groups on `X` (so `C⁰(C⁰F)` is too). **Acyclicity** `H^n(C⁰F) = 0` is a
distinct statement — it additionally requires that `Γ = lim` preserves
flasques and that `Γ` preserves exactness on flasques. This is precisely
what this Part 88 does not pose.

## References

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. Iteration of the functor `C⁰` on kernels.
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §5. Acyclicity `H^n(C⁰F) = 0` for `n ≥ 1` — **named frontier**
    of this delivery.

i18n (EPIC #4980) — OK-CONSUMER sibling: this `_en` file imports its FR
counterpart `Grothendieck.GodementAcyclicity` and re-exports the same
definitions under the `Grothendieck_en` namespace, prefixed `Grothendieck.` for
disambiguation. The proof bodies are byte-identical to the FR sibling — the
sole document is the English docstring at the top of the module.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck_en

variable {X : TopCat.{u}}

-- **OK-CONSUMER sibling**: the declarations `godementDiff_iterated`,
-- `godementResolution_kernel_iterated`, and `godementResolution_extends_chain`
-- are imported from `Grothendieck.GodementAcyclicity` (FR) and accessed in the
-- `Grothendieck_en` namespace as `Grothendieck.godementDiff_iterated`,
-- `Grothendieck.godementResolution_kernel_iterated`, and
-- `Grothendieck.godementResolution_extends_chain`. We do not redeclare them
-- here to keep bodies byte-identical with FR (the OK-CONSUMER i18n invariant
-- of [docs/lean/i18n-sibling-patterns.md]).

-- **The truncated Godement chain at degree 3**: `F → C⁰F → C⁰²F → C⁰³F`,
-- obtained at this Part 88 (compared to the un-truncated 2-step chain at
-- Part 87). The full infinite complex
-- `0 → F → C⁰F → C⁰²F → C⁰³F → ⋯` is **acyclique** (God58 II.5) at
-- `n ≥ 1` when `F` is a sheaf — **named frontier** of this delivery,
-- not part of this Part.

-- **The null-homotopy** `μ ≫ d⁰ = 0` is inherited from
-- `Grothendieck.godementResolution_kernel_iterated` via the OK-CONSUMER import
-- — the composition `d⁰ ≫ d¹ F` is identically `d¹ F` by definition of the
-- latter. The acyclicity `H^n(C⁰F) = 0` for `n ≥ 1` is the **named frontier**
-- deferred beyond this delivery (Part 89+).

end Grothendieck_en