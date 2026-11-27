/-
Grothendieck Part 22 -- Mayer-Vietoris long exact sequence in sheaf cohomology

Part 21 (MayerVietorisSquare.lean) introduced Mayer-Vietoris squares: the
geometric input (a pushout square in sheaves) and the associated short
exact complex of free abelian sheaves.

This module bridges the **Mayer-Vietoris long exact sequence** in sheaf
cohomology from Mathlib (`CategoryTheory.Sites.SheafCohomology.MayerVietoris`).

Given a Mayer-Vietoris square S for a site (C, J) and an abelian sheaf F,
there is a long exact sequence:

  ... ⟶ H^n(X₄, F) ⟶ H^n(X₂, F) ⊞ H^n(X₃, F) ⟶ H^n(X₁, F) ⟶ H^{n+1}(X₄, F) ⟶ ...

where X₁ = intersection, X₂/X₃ = covering opens, X₄ = covered space.

Key constructions bridged from Mathlib:

  - `toBiprod` : sum of restrictions H^n(X₄) → H^n(X₂) ⊞ H^n(X₃)
  - `fromBiprod` : difference of restrictions H^n(X₂) ⊞ H^n(X₃) → H^n(X₁)
  - `toBiprod_fromBiprod` : composition is zero
  - `δ` : connecting homomorphism H^{n₀}(X₁) → H^{n₁}(X₄) (n₁ = n₀ + 1)
  - `sequence` : the full long exact sequence (ComposableArrows AddCommGrp 5)
  - `sequence_exact` : the sequence is exact
  - `δ_toBiprod` : δ >> toBiprod = 0
  - `fromBiprod_δ` : fromBiprod >> δ = 0

This completes the Mayer-Vietoris machinery: from a geometric covering
condition (Part 21) to the cohomological consequence (this part).

Epic #1646, See #2159. All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

universe w v u

namespace Grothendieck.SheafCohomology.MayerVietoris_en

open CategoryTheory Category Opposite Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-! ## 1. Restriction maps in cohomology

Given a Mayer-Vietoris square S and an abelian sheaf F, the maps
between cohomology groups are induced by the restriction maps
in the square.

`toBiprod` is the sum of restrictions:
  H^n(X₄, F) ⟶ H^n(X₂, F) ⊞ H^n(X₃, F)
sending y to (f₂₄* y, f₃₄* y).

`fromBiprod` is the difference of restrictions:
  H^n(X₂, F) ⊞ H^n(X₃, F) ⟶ H^n(X₁, F)
sending (y₁, y₃) to f₁₂* y₁ - f₁₃* y₃.
-/

-- Sum of restrictions: H^n(X₄, F) ⟶ H^n(X₂, F) ⊞ H^n(X₃, F).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod

-- Explicit formula for toBiprod.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod_apply

-- Difference of restrictions: H^n(X₂, F) ⊞ H^n(X₃, F) ⟶ H^n(X₁, F).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod

/-! ## 2. Composition and the zero condition

The composition toBiprod >> fromBiprod is zero:
  H^n(X₄) ⟶ H^n(X₂) ⊞ H^n(X₃) ⟶ H^n(X₁)
This is the cohomological shadow of the commutativity of the square.
-/

-- toBiprod >> fromBiprod = 0.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod_fromBiprod

-- Explicit formula for fromBiprod applied to a pair.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod_biprodIsoProd_inv_apply

/-! ## 3. The connecting homomorphism

The connecting homomorphism δ : H^{n₀}(X₁, F) ⟶ H^{n₁}(X₄, F) (where
n₁ = n₀ + 1) is the key map in the long exact sequence. It measures
the obstruction to lifting a cohomology class from the intersection
to the covered space.

This is defined as `shortComplex_shortExact.extClass.precomp`.
-/

-- The connecting homomorphism δ : H^{n₀}(X₁) ⟶ H^{n₁}(X₄).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.δ

/-! ## 4. The long exact sequence

The Mayer-Vietoris long exact sequence is packaged as a
`ComposableArrows AddCommGrp 5`:

  H^n(X₄) ⟶ H^n(X₂) ⊞ H^n(X₃) ⟶ H^n(X₁) ⟶ H^{n+1}(X₄) ⟶ H^{n+1}(X₂) ⊞ H^{n+1}(X₃) ⟶ H^{n+1}(X₁)

This is `sequence S F n₀ n₁ h` where `h : n₀ + 1 = n₁`.
-/

-- The Mayer-Vietoris long exact sequence (6 terms, ComposableArrows 5).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence

/-! ## 5. Exactness

The long exact sequence is exact at every position. This is the main
theorem of the module, proven by comparison with the contravariant
sequence of Ext-groups.
-/

-- The Mayer-Vietoris sequence is exact.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence_exact

/-! ## 6. Boundary conditions

The connecting homomorphism satisfies two boundary conditions:
  - δ >> toBiprod = 0  (δ lands in the kernel of toBiprod)
  - fromBiprod >> δ = 0  (δ factors through the cokernel of fromBiprod)
-/

-- δ >> toBiprod = 0.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.δ_toBiprod

-- fromBiprod >> δ = 0.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod_δ

/-! ## 7. Bridge theorems

Bridge theorems connecting the Mayer-Vietoris long exact sequence
to concrete verification.
-/

/-- Bridge theorem: the Mayer-Vietoris sequence is exact. For a
    Mayer-Vietoris square S and abelian sheaf F, the sequence of
    cohomology groups is exact at every position. -/
theorem mv_sequence_exact
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (S.sequence F n₀ n₁ h).Exact :=
  S.sequence_exact F n₀ n₁ h

/-- Bridge theorem: the connecting homomorphism composed with the
    sum of restrictions is zero: δ >> toBiprod = 0. -/
theorem mv_delta_toBiprod_eq_zero
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.δ F n₀ n₁ h ≫ S.toBiprod F n₁ = 0 :=
  S.δ_toBiprod F n₀ n₁ h

/-- Bridge theorem: the difference of restrictions composed with the
    connecting homomorphism is zero: fromBiprod >> δ = 0. -/
theorem mv_fromBiprod_delta_eq_zero
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.fromBiprod F n₀ ≫ S.δ F n₀ n₁ h = 0 :=
  S.fromBiprod_δ F n₀ n₁ h

/-!
## Proper bridges (c.1301+131)

The definitions and theorems below *re-export* the fields of the
`J.MayerVietorisSquare` structure exposed in
`Mathlib/CategoryTheory/Sites/SheafCohomology/MayerVietoris.lean`. All these
fields operate on the resident structure `J.MayerVietorisSquare` non
polymorphic over universes — therefore **L902 ★★ SAFE** (cf c.1301+108-L1 ★★:
polymorphic universe constructors are to be proscribed, unlike resident
fields on X).

1. `mv_toBiprod_field`: restatement of `S.toBiprod F n` (def, sum of
   restrictions H^n(X₄) → H^n(X₂) ⊞ H^n(X₃)).
2. `mv_fromBiprod_field`: restatement of `S.fromBiprod F n` (def,
   difference of restrictions H^n(X₂) ⊞ H^n(X₃) → H^n(X₁)).
3. `mv_delta_field`: restatement of `S.δ F n₀ n₁ h` (def, connecting
   homomorphism H^{n₀}(X₁) → H^{n₁}(X₄)).
4. `mv_sequence_field`: restatement of `S.sequence F n₀ n₁ h` (def, the
   long exact sequence ComposableArrows AddCommGrpCat.{w} 5).
5. `mv_toBiprod_fromBiprod_field`: restatement of `S.toBiprod_fromBiprod F
   n` (theorem, composition toBiprod >> fromBiprod = 0 — the nullity
   condition).

These are "showcase" bridges that certify that these fields of the
`J.MayerVietorisSquare` structure are effectively computable in the same
Lean execution.
-/

/-- Bridge: the sum of restrictions H^n(X₄) → H^n(X₂) ⊞ H^n(X₃).
    β-equivalent to the field `S.toBiprod F n`. -/
noncomputable def mv_toBiprod_field
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n : ℕ) :
    F.H' n S.X₄ ⟶ F.H' n S.X₂ ⊞ F.H' n S.X₃ :=
  S.toBiprod F n

/-- Bridge: the difference of restrictions H^n(X₂) ⊞ H^n(X₃) → H^n(X₁).
    β-equivalent to the field `S.fromBiprod F n`. -/
noncomputable def mv_fromBiprod_field
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n : ℕ) :
    F.H' n S.X₂ ⊞ F.H' n S.X₃ ⟶ F.H' n S.X₁ :=
  S.fromBiprod F n

/-- Bridge: the connecting homomorphism H^{n₀}(X₁) → H^{n₁}(X₄).
    β-equivalent to the field `S.δ F n₀ n₁ h`. -/
noncomputable def mv_delta_field
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    F.H' n₀ S.X₁ ⟶ F.H' n₁ S.X₄ :=
  S.δ F n₀ n₁ h

/-- Bridge: the Mayer-Vietoris long exact sequence (ComposableArrows
    AddCommGrpCat.{w} 5). β-equivalent to `S.sequence F n₀ n₁ h`. -/
noncomputable def mv_sequence_field
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{w} 5 :=
  S.sequence F n₀ n₁ h

/-- Bridge: the composition toBiprod >> fromBiprod is zero.
    β-equivalent to the lemma `S.toBiprod_fromBiprod F n`. -/
theorem mv_toBiprod_fromBiprod_field
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n : ℕ) :
    S.toBiprod F n ≫ S.fromBiprod F n = 0 :=
  S.toBiprod_fromBiprod F n

/-! ## 8. Stacks correspondence (group #12 of #28537, surveyed 2026-11-26)

Statement-by-statement comparison with the reference `AxiomMath/Stacks`
(`StacksFrontier/Topology/Sheaves/Cohomology/MayerVietoris/`). References are
given as `file:line` in the Stacks repository.

**Method point.** Stacks and this module **share the same Mathlib base**
(`Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris`): Stacks
attaches **tag 01EB** to Mathlib's long exact sequence
(`LongExactSequence.lean:141-142`) and adds two results this module does not
have (the leading zero and the naturality of the connecting morphism).

| Statement | Class | Stacks reference | What our version adds / what diverges |
|---|---|---|---|
| `mv_sequence_exact` | covered | `MayerVietoris/LongExactSequence.lean:141-142` — `add_to_stacks 01EB "successive windows"` | It is the **same** Mathlib statement: Stacks attaches tag 01EB to it. What our version adds: the named bridge, the long sequence spelled out over six terms, and the EN twin. |
| `mv_delta_toBiprod_eq_zero` | covered | `MayerVietoris/ColimitDescent.lean:462` (`w₂`, via `δ_toBiprod`) | Stacks uses the **same** field `S.δ_toBiprod` to prove exactness of the sequence after a colimit. Our version names it and declares it. |
| `mv_fromBiprod_delta_eq_zero` | covered | `MayerVietoris/ColimitDescent.lean:461` (`w₁`, via `fromBiprod_δ`) | idem, same field `S.fromBiprod_δ`. |
| `mv_toBiprod_field` | covered | `MayerVietoris/LongExactSequence.lean:101,109` and `ColimitDescent.lean:205-206` (`mono_toBiprod_zero`) | Stacks manipulates `S.toBiprod F n` literally, and derives the injectivity of the head map from it (`Mono (S.toBiprod F 0)`). Our version adds the bridge. |
| `mv_fromBiprod_field` | covered | `MayerVietoris/ColimitDescent.lean:330-334` (`fromBiprodNat`) | Stacks manipulates `S.fromBiprod F n` literally, and its naturality in the square. Our version adds the bridge. |
| `mv_delta_field` | covered | `MayerVietoris/LongExactSequence.lean:131-132` | Stacks uses `S.δ F n₀ n₁ h` literally. Our version adds the bridge. |
| `mv_sequence_field` | covered | `MayerVietoris/LongExactSequence.lean:82,110` (`S.sequence F 0 1 rfl`) | idem for the long sequence itself. |
| `mv_toBiprod_fromBiprod_field` | covered | `MayerVietoris/ColimitDescent.lean:460` (`w₀`, via `toBiprod_fromBiprod`) | Same Mathlib field; Stacks uses it for exactness after a colimit. |

**What Stacks establishes and this module does not** — two gaps to be told
apart from the references above:

- the **leading zero**: Stacks shows that `H⁰(X₄,F) ⟶ H⁰(X₂,F) ⊞ H⁰(X₃,F)`
  is injective (`ColimitDescent.lean:205-206`, `mono_toBiprod_zero`), so the
  six-term window starts with a zero (`LongExactSequence.lean:81-87`,
  `mayerVietorisInitialSequence` and `mayerVietorisInitialSequence_exact`);
  this module carries the successive windows only (tag 01EB), without the
  leading zero;
- the **naturality of the connecting morphism in `F`**: Stacks establishes it
  (`LongExactSequence.lean:129-132`, `mayerVietoris_delta_naturality`); this
  module does not state it.

-/

end Grothendieck.SheafCohomology.MayerVietoris_en
