import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Algebra.Category.Grp.IsFinite
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.Algebra.Lie.SerreConstruction
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.Field.ZMod

/-!
# Serre in Mathlib: a tour of five landmarks

This module accompanies the notebook `08-serre-dans-mathlib.ipynb`
(*Serre 100* series, grain 6 of EPIC #16334). Jean-Pierre Serre lent his
name to five distinct constructions, each formalized by Mathlib in a
different corner of the library; this tour visits them one by one:

1. **Serre classes** (`Mathlib.CategoryTheory.Abelian.SerreClass.Basic`):
   a class of objects of an abelian category closed under subobjects,
   quotients and extensions — the language of the finiteness conditions
   of *Local Fields*.
2. **The Serre derivative** (`Mathlib.NumberTheory.ModularForms.Derivative`):
   the derivation preserving modular forms of weight `k + 2`,
   `∂ₖ = D − (k/12)·E₂`.
3. **The Serre construction** (`Mathlib.Algebra.Lie.SerreConstruction`):
   the Lie algebra presented by generators `H`, `E`, `F` and relations
   encoding a Cartan matrix — the gateway to Kac–Moody algebras.
4. **Serre's criterion** (`Mathlib.RingTheory.DiscreteValuationRing.Basic`):
   an integral domain is a discrete valuation ring if and only if it is
   principal with a unique nonzero prime ideal.
5. **Perfect rings "in the sense of Serre"**
   (`Mathlib.FieldTheory.Perfect`): bijective Frobenius in
   characteristic `p`, as in *Local Fields*, ch. II §3 — distinct from
   Bass perfection.

Each station below states and proves a significant fact drawn from
Mathlib, ready for interactive exploration from the notebook.
-/

set_option autoImplicit false

noncomputable section

namespace Serre100_en

/-! ## Station 1 — Serre classes

A Serre class `P` on an abelian category `C` contains the zero object
and passes to subobjects, quotients and extensions. The "two-out-of-
three" criterion for short exact sequences is its central theorem.
-/

open CategoryTheory

section SerreClasses

variable {C : Type*} [Category C] [Abelian C] (P : ObjectProperty C)

/-- The universal property `⊤` (all objects) is a Serre class: the
largest one, filtering nothing. -/
example : (⊤ : ObjectProperty C).IsSerreClass := inferInstance

/-- The class of objects isomorphic to zero is a Serre class: the
smallest one, retaining only the zero object. -/
example {C : Type*} [Category C] [Abelian C] :
    ObjectProperty.IsSerreClass (Limits.IsZero (C := C)) := inferInstance

/-- **Finite** abelian groups form a Serre class of `AddCommGrp`: this is
the historical example of chapter I of *Local Fields*, and the reason the
formalism exists. -/
example : AddCommGrpCat.isFinite.IsSerreClass := inferInstance

variable [P.IsSerreClass]

/-- The "two-out-of-three" criterion: in a short exact sequence, the
middle term belongs to the class if and only if both outer terms do.
This packs closure under extensions together with both half-closures
(subobjects and quotients). -/
theorem member_iff_outer {S : ShortComplex C} (hS : S.ShortExact) :
    P S.X₂ ↔ P S.X₁ ∧ P S.X₃ := P.prop_iff_of_shortExact hS

/-- "Three-out-of-three" version: an exact (not necessarily short)
sequence whose outer terms are in the class also has its middle term
there. -/
theorem member_of_exact {S : ShortComplex C} (hS : S.Exact)
    (h₁ : P S.X₁) (h₃ : P S.X₃) : P S.X₂ := P.prop_X₂_of_exact hS h₁ h₃

end SerreClasses

/-! ## Station 2 — The Serre derivative

On the upper half-plane `ℍ`, the weight-`k` Serre derivative corrects
the normalized derivative `D` by an `E₂` term:

`∂ₖ F(z) = D F(z) − (k/12) · E₂(z) · F(z)`

so that `∂ₖ` maps modular forms of weight `k` to weight `k + 2` (the
notebook explores the `SL(2, ℤ)` variance; here we pin down the
algebraic identities).
-/

open Derivative
open UpperHalfPlane
open scoped Manifold ModularForm

section SerreDerivative

/-- The defining formula, restated: the Serre derivative is the
normalized derivative corrected by the `E₂` term, with the `k/12`
normalization. -/
example (k : ℂ) (F : ℍ → ℂ) (z : ℍ) :
    serreDerivative k F z =
      normalizedDerivOfComplex F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z := rfl

/-- Additivity: the Serre derivative is additive in the function, at
fixed weight. -/
example (k : ℂ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serreDerivative k (F + G) = serreDerivative k F + serreDerivative k G :=
  serreDerivative_add k F G hF hG

/-- **Weighted** Leibniz rule: on a product, weights add up and each
factor is differentiated with its own weight — the hallmark of a graded
derivation. -/
example (k₁ k₂ : ℂ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serreDerivative (k₁ + k₂) (F * G) =
      serreDerivative k₁ F * G + F * serreDerivative k₂ G :=
  serreDerivative_mul k₁ k₂ F G hF hG

/-- The Serre derivative preserves differentiability: `∂ₖ` creates no
new singularity. -/
example (k : ℂ) {F : ℍ → ℂ} (hF : MDiff F) :
    MDiff (serreDerivative k F) :=
  serreDerivative_mdifferentiable k hF

end SerreDerivative

/-! ## Station 3 — The Serre construction

Given a generalized Cartan matrix `CM : Matrix B B ℤ`, the "Serre" Lie
algebra is the quotient of the free Lie algebra on generators `H i`,
`E i`, `F i` (`i : B`) by the ideal of **Serre relations**: commutation
of the `H`s, diagonal bracket `⁅E i, F j⁆`, action of the `H`s on `E`s
and `F`s weighted by `CM`, and nilpotency of order `1 − CM i j` for the
`ad E i`, `ad F i`.
-/

section SerreConstruction

/-- The Cartan matrix of type **A₂**: the simplest rank-2 root system,
that of `sl₃`. -/
def cartanA2 : Matrix (Fin 2) (Fin 2) ℤ := !![2, -1; -1, 2]

/-- The generators of the construction: a family `H` (Cartan), a family
`E` (positive), a family `F` (negative), indexed by `B`. -/
example (i : Fin 2) : CartanMatrix.Generators (Fin 2) := .H i

/-- The ideal of Serre relations of `A₂` lives in the free Lie algebra
on the generators — quotienting by it yields the Serre algebra `sl₃`. -/
example (R : Type*) [CommRing R] :
    LieIdeal R (FreeLieAlgebra R (CartanMatrix.Generators (Fin 2))) :=
  CartanMatrix.Relations.toIdeal R cartanA2

end SerreConstruction

/-! ## Station 4 — Serre's criterion for discrete valuation rings

*Local Fields*, ch. I §2, prop. 2: a discrete valuation ring is exactly
a principal ring **having a unique nonzero prime ideal**. Mathlib states
it for commutative integral domains.
-/

section DVRCriterion

/-- Serre's criterion: `R` is a discrete valuation ring if and only if
`R` is principal and has exactly one nonzero prime ideal (the maximal
ideal). The "∃!" captures uniqueness. -/
example (R : Type*) [CommRing R] [IsDomain R] :
    IsDiscreteValuationRing R ↔
      IsPrincipalIdealRing R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime :=
  IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R

end DVRCriterion

/-! ## Station 5 — Perfect rings "in the sense of Serre"

*Local Fields*, ch. II §3: a ring of characteristic `p` is perfect when
the Frobenius endomorphism `x ↦ x ^ p` is bijective. Mathlib calls this
`PerfectRing` and notes in its docstring that this is Serre's sense —
not to be confused with Bass perfection.
-/

section PerfectInTheSenseOfSerre

/-- `ZMod 2` is perfect in the sense of Serre, exponent `2`: Frobenius
`x ↦ x²` is bijective on the field with two elements. -/
example : PerfectRing (ZMod 2) 2 := inferInstance

/-- Every finite field `ZMod p` inherits the same perfection — a finite
reduced ring of characteristic `p`. (Literal `Fact` instances only exist
for 2 and 3: we supply them by hand for other primes.) -/
example : PerfectRing (ZMod 5) 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact inferInstance

/-- A finite reduced ring of characteristic `2` is perfect in the sense
of Serre: surjectivity of Frobenius is free (finite cardinal +
injectivity), and injectivity comes from reducedness. -/
example (R : Type*) [CommRing R] [ExpChar R 2] [Finite R] [IsReduced R] :
    PerfectRing R 2 := inferInstance

/- Serre's bridge needs `Field (ZMod 7)` as early as statement
elaboration: the literal `Fact` must therefore be registered BEFORE, at
file level (literal instances only exist for 2 and 3). -/
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- Serre's bridge: a **field** perfect in the sense of Serre is a
perfect field in the polynomial sense (every irreducible is separable). -/
example : PerfectField (ZMod 7) := PerfectRing.toPerfectField (ZMod 7) 7

end PerfectInTheSenseOfSerre

end Serre100_en
