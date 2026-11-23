import FormalGroups.Basic_en
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.CharP.Defs

/-!
# Iterates of the law, linear part and finite height

The iterates `[n]F` of the law of a formal group are defined by recursion:
`[0]F = 0` and `[n+1]F = F([n]F, X)`. The linear part of a tuple of series
is the matrix of its degree-one homogeneous coefficients; a formal group
over a field of characteristic `p` has **finite height** when the quotient
by the ideal spanned by `[p]F` is finite-dimensional.
-/

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace FormalGroups_en.MvFormalGroup

variable {g h : ℕ} {R : Type*} [CommRing R]

/-- Iterates of the law: `[0]F = 0` and `[n+1]F = F([n]F, X)`, component by
component. -/
def nthSeries (F : MvFormalGroup g R) : ℕ → Fin g → MvPowerSeries (Fin g) R
  | 0 => fun _ => 0
  | n + 1 => fun i =>
      subst (Sum.elim (nthSeries F n) fun j => X j) (F.toPowerSeries i)

@[simp]
theorem nthSeries_zero (F : MvFormalGroup g R) : F.nthSeries 0 = fun _ => 0 := rfl

theorem nthSeries_succ (F : MvFormalGroup g R) (n : ℕ) : F.nthSeries (n + 1) = fun i =>
    subst (Sum.elim (F.nthSeries n) fun j => X j) (F.toPowerSeries i) := rfl

/-- Linear part of an `h`-tuple of series in `g` variables: the matrix of
its degree-one homogeneous coefficients. -/
def linearPart (φ : Fin h → MvPowerSeries (Fin g) R) : Matrix (Fin h) (Fin g) R :=
  Matrix.of fun i j => (φ i).coeff (Finsupp.single j 1)

/-- Finite height over a field `K` of characteristic `p`: the quotient of
the power series ring by the ideal spanned by the components of `[p]F` is
a finite-dimensional `K`-vector space. -/
def FiniteHeight (p : ℕ) {K : Type*} [Field K] [CharP K p] (F : MvFormalGroup g K) : Prop :=
  FiniteDimensional K (MvPowerSeries (Fin g) K ⧸ Ideal.span (Set.range (F.nthSeries p)))

end MvFormalGroup

end FormalGroups_en

end
