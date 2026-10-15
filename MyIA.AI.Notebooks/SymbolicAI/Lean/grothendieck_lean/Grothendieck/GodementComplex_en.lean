/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementComplex

/-!
# The Godement complex: iterating the canonical step at all degrees

Part 92 — the named frontier of Parts 90 and 91. Part 89 posed the
**canonical step** `godementStep f = cokernel.π f ≫ toGodement (coker f)` and
its null-composition `f ≫ godementStep f = 0`; Parts 89-90 derived from it the
differentials `d⁰` and `d¹` with `d⁰ ≫ d¹ = 0`; Part 91 established the
exactness of the beginning (`exact_toGodement_godementCanonicalDZero`). This
module iterates the step **at all degrees** and assembles the result as a
`CochainComplex` object [God58, Chap. II §4.1].

## The chain of differentials

1. `godementDChain F`: the chain of differentials as a sequence of arrows
   (`Arrow`), by recursion on the degree — degree `n + 1` is the canonical
   step of the degree-`n` arrow: `d^{n+1} := godementStep dⁿ`. This is the
   exact iteration of the construction of [God58], each arrow passing through
   the cokernel of the previous one — the contrast with Part 87: the iterated
   unit sequence is **not** a complex, the canonical-step one is.
2. `godementCanonicalObj F n` and `godementCanonicalD F n`: the degree-`n`
   term and the differential `X n ⟶ X (n+1)` extracted from the chain, with
   `rfl` lemmas calibrating them on the notations of Parts 89-90
   (`godementCanonicalD_zero`, `godementCanonicalD_one`,
   `godementCanonicalD_succ`).
3. `godementCanonicalD_comp_zero`: **null-composition at every degree** —
   `dⁿ ≫ d^{n+1} = 0` for all `n`, immediate instance of
   `comp_godementStep_zero` (Part 89) applied at degree `n`.
4. `godementCanonicalComplex F`: the assembly as a `CochainComplex` indexed by
   `ℕ`, via Mathlib's canonical constructor `CochainComplex.of`, with
   interface lemmas `godementCanonicalComplex_X_zero`,
   `godementCanonicalComplex_d_zero`, `godementCanonicalComplex_d_one`.
5. `toGodement_comp_godementCanonicalD`: the start of the augmented complex —
   `μ ≫ d⁰ = 0`, restating Part 89 in the iterated notations.

## What this Part poses vs. what it leaves open

**Posed**: the recursion `d^{n+1} = godementStep dⁿ` at all degrees, the
null-composition `dⁿ ≫ d^{n+1} = 0` for all `n`, and the object
`godementCanonicalComplex : CochainComplex … ℕ` — the canonical Godement
resolution now exists **as a complex object**, not merely as a sequence of
arrows pinned degree by degree.

**Not posed** — named frontier of Part 93: **acyclicity**
`Hⁿ(C⁰) = 0` for `n ≥ 1` ([God58] II Th. 5.2.1). It will require exactness at
every degree — that is, the iteration of
`exact_toGodement_godementCanonicalDZero` (P91, not yet merged) along the
chain — and then the passage to homology. The augmented complex
`F ⟶ C⁰F ⟶ C⁰(coker μ) ⟶ ⋯` as a **resolution** of `F` (the
quasi-isomorphism) follows acyclicity and is not approached here.

## References

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. The canonical resolution assembled as a cochain complex —
    the pattern posed in this module.
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §5. Acyclicity `Hⁿ(C⁰F) = 0` for `n ≥ 1` — named frontier of
    Part 93.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck_en

variable {X : TopCat.{u}}

-- **OK-CONSUMER sibling**: the declarations `godementDChain`,
-- `godementCanonicalObj`, `godementCanonicalD`,
-- `godementCanonicalD_comp_zero`, `toGodement_comp_godementCanonicalD`, and
-- `godementCanonicalComplex` are imported from
-- `Grothendieck.GodementComplex` (FR) and accessed in the
-- `Grothendieck_en` namespace as `Grothendieck.godementDChain`,
-- `Grothendieck.godementCanonicalObj`, `Grothendieck.godementCanonicalD`,
-- `Grothendieck.godementCanonicalD_comp_zero`,
-- `Grothendieck.toGodement_comp_godementCanonicalD`, and
-- `Grothendieck.godementCanonicalComplex`. We do not redeclare them here to
-- keep bodies byte-identical with FR (the OK-CONSUMER i18n invariant of
-- [docs/lean/i18n-sibling-patterns.md]).

-- **The canonical complex**: with `d^{n+1} = godementStep dⁿ` at every
-- degree, the null-composition `dⁿ ≫ d^{n+1} = 0` (P89) makes the sequence of
-- canonical steps an actual `CochainComplex` — the condition the iterated
-- unit sequence of P87 provably fails. Acyclicity `Hⁿ(C⁰) = 0` for `n ≥ 1`
-- is the named frontier of Part 93.

end Grothendieck_en
