/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementExactness

/-!
# The augmented Godement complex: d¹ and the categorical mono of the unit

Part 90 — the announced continuation of Part 89. The latter posed the canonical
step `godementStep f := cokernel.π f ≫ toGodement (coker f)` and the differential
`d⁰ := godementCanonicalDZero` with its null-composition `μ ≫ d⁰ = 0`. This
Part takes two more steps on the same thread (the third — the **reduction of
exactness** — has been withdrawn : see the author's note at the end of the
namespace).

## Two facts, in the order of the narrative

1. `godementCanonicalDOne` : the **degree-1 differential** — the canonical step
   applied to `d⁰`. The next term `C²F := C⁰(coker d⁰)` is the Godement
   presheaf of the cokernel of `d⁰`, and `d¹ : C¹F ⟶ C²F` is the connecting
   arrow. The null-composition `d⁰ ≫ d¹ = 0`
   (`godementCanonicalDZero_comp_godementCanonicalDOne`) is an instance of
   `comp_godementStep_zero` (P89) : **the canonical resolution is a complex
   beyond degree 0** — each degree is obtained by applying the canonical step
   to the previous differential, and the null-composition is free at each
   step.
2. `mono_toGodement_of_isSheaf` : **the Godement unit is a categorical
   monomorphism on sheaves**. Part 84 had proved the injectivity section by
   section (`godementUnit_injective_of_isSheaf`) ; this fact is its categorical
   ascent : mono in the category of presheaves, via
   `NatTrans.mono_iff_mono_app` (the mono of a natural transformation between
   presheaves of abelian groups is exactly the pointwise mono). It is the
   exactness of `0 → F → C⁰F` **at F**, now stated in the language of complexes.

## What this Part poses vs. what it leaves open

**Posed** : the complex at degrees 0 and 1 (and the iteration pattern that
extends to all degrees), and the categorical mono of the unit on sheaves.

**Not posed** — named frontier of Part 91 : the **reduction of exactness at
`C⁰F` to the mono of the cokernel's unit**
(`exact_toGodement_godementCanonicalDZero_of_mono`), whose proof requires the
**separatedness of the cokernel** `coker μ` for `F` sheaf — the gluing of local
sections of the quotient through germs, which requires the gluing argument of
[God58] (local sections `sᵢ` glue via separatedness of `F` and injectivity of
`μ`). The **complete iteration** of the reduction to higher degrees, and the
**acyclicity** `H^n(C⁰F) = 0` for `n ≥ 1` ([God58] II.5) are also in P91
scope.

## References

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. The canonical resolution `0 → F → C⁰F → C¹F → ⋯` : complex
    (d⁰ ≫ d¹ = 0) and exactness at `C⁰F` — reduced here to the mono of the
    cokernel's unit.
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §5. Acyclicity — named frontier of Part 91.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck_en

variable {X : TopCat.{u}}

-- **OK-CONSUMER sibling**: the declarations `godementCanonicalDOne`,
-- `godementCanonicalDZero_comp_godementCanonicalDOne`, and
-- `mono_toGodement_of_isSheaf` are imported from
-- `Grothendieck.GodementExactness` (FR) and accessed in the `Grothendieck_en`
-- namespace as `Grothendieck.godementCanonicalDOne`, etc. We do not redeclare
-- them here to keep bodies byte-identical with FR (the OK-CONSUMER i18n
-- invariant of [docs/lean/i18n-sibling-patterns.md]).

-- **The complex beyond degree 0** : with `d¹ := godementCanonicalDOne F` and
-- the null-composition `d⁰ ≫ d¹ = 0`
-- (`godementCanonicalDZero_comp_godementCanonicalDOne`), the canonical resolution
-- extends to a chain complex. **The unit on sheaves is mono**
-- (`mono_toGodement_of_isSheaf`) — the categorical ascent of Part 84's
-- pointwise injectivity. **The reduction of exactness at `C⁰F`** is the named
-- frontier of Part 91, where the separatedness of `coker μ` (gluing of local
-- sections on sheaves) is the mathematical fact that closes the loop — and
-- the statement `exact_toGodement_godementCanonicalDZero_of_mono` will be
-- posed and proved there. The draft r65 of Part 90 carried this statement
-- with a `sorry` tactical proof; the gate `proof-integrity` of the caller
-- workflow elevated that `sorry` to a `sorryAx` transitive at import
-- (forbidden axiom, pr-review-discipline §B), and the honest option is the
-- **withdrawal** of the statement from this Part. The proof of P91 will
-- proceed by direct construction of the gluing, which the reordering of the
-- imports in P91 will naturally place before any subsequent use.

end Grothendieck_en
