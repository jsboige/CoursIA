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
-- unit sequence of P87 provably fails.
--
-- **Part 93(b), assembly landed in the FR twin of this module**:
-- `Grothendieck.stalk_exact_godementCanonicalD` — the canonical complex is
-- exact at every stalk, at every degree: for every `n`, the stalk sequence
-- `CⁿFₓ₀ ⟶ C^{n+1}Fₓ₀ ⟶ C^{n+2}Fₓ₀` is exact at `C^{n+1}Fₓ₀`, with **no
-- sheaf hypothesis**. Every degree is the generic lemma
-- `stalk_exact_godementStep` at `f = dⁿ`, both assembly patterns —
-- `d^{n+1} = godementStep dⁿ` and `C^{n+2} = C⁰(coker dⁿ)` — being
-- definitional (`rfl`): the recurrence promised by Part 93(a) is the lemma
-- itself, no induction over `n` is needed.
--
-- **Part 93(b), homological reading landed in the FR twin**:
-- `Grothendieck.isZero_stalk_homology_godementCanonicalComplex` — the
-- homology of the canonical complex is zero at every stalk, for every
-- degree `n ≥ 1`, with **no sheaf hypothesis**. Three gestures: the stalk
-- short complex centered at `n` is exact (the assembly theorem in `n - 1`);
-- an exact short complex has zero homology; and the
-- `stalkFunctor_preservesHomology` instance transports this `IsZero` along
-- `ShortComplex.mapHomologyIso` — the homology of the stalk is the stalk
-- of the homology. **Why stalks and not the presheaf**: a presheaf with
-- all stalks zero need not be zero (non-separated) — stalkwise nullity is
-- the unconditional form. The sheaf corollary (nullity of `Hⁿ` in the
-- category of sheaves, [God58] II Th. 5.2.1) is the next frontier.
--
-- **Part 94, flabbiness of the canonical tower landed in the FR twin**:
-- `Grothendieck.isFlasque_godementCanonicalComplex` — every stage of the
-- canonical Godement complex is flasque, with **no hypothesis on `F`**
-- (step 1 of the "flabby resolution" reading of [God58] II Th. 5.2.1).
-- The three cases of the `godementCanonicalObj` recursion (degree 0,
-- degree 1, degree n+2) each reduce definitionally to `godementPresheaf`
-- of some presheaf, so the generic flabbiness `isFlasque_godementPresheaf`
-- (zero-extension of germ families: a family of germs on `V` lifts to any
-- open `U ⊇ V` by extending by zero outside `V`) covers the whole tower —
-- a three-case `exact`, no recursion to write. Calibrating note
-- (2026-10-18): Mathlib `TopCat.Presheaf.IsFlasque` does exist
-- (Topology/Sheaves/Flasque.lean) — the #2159 addendum c.6242821964
-- wrongly called it sheaf-only; the file carries both versions. The sheaf
-- corollary of [God58] II Th. 5.2.1 remains behind abelian sheafification,
-- absent from Mathlib at the pinned version (`sheafify`/`sheafifyStalkIso`
-- Type-valued only; `HasSheafify`/`HasSheafCompose (forget A)` hypotheses
-- with no instance for `(AddCommGrpCat, TopCat)`); the presheaf track —
-- stalk acyclicity (Part 93(b)), flabby stages (this Part) — advances
-- without it, and the flabby resolution (long exact sequence, Part 95+)
-- will consume the brick landed here.

end Grothendieck_en
