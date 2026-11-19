import FormalGroups.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.CharP.Defs

/-!
# Itérés de la loi, partie linéaire et hauteur finie

Les itérés `[n]F` de la loi d'un groupe formel se définissent par
récurrence : `[0]F = 0` et `[n+1]F = F([n]F, X)`. La partie linéaire d'un
uplet de séries est la matrice de ses coefficients homogènes de degré un ;
un groupe formel sur un corps de caractéristique `p` est de **hauteur
finie** lorsque le quotient par l'idéal engendré par `[p]F` est de dimension
finie.
-/

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace FormalGroups.MvFormalGroup

variable {g h : ℕ} {R : Type*} [CommRing R]

/-- Itérés de la loi : `[0]F = 0` et `[n+1]F = F([n]F, X)`, composante par
composante. -/
def nthSeries (F : MvFormalGroup g R) : ℕ → Fin g → MvPowerSeries (Fin g) R
  | 0 => fun _ => 0
  | n + 1 => fun i =>
      subst (Sum.elim (nthSeries F n) fun j => X j) (F.toPowerSeries i)

@[simp]
theorem nthSeries_zero (F : MvFormalGroup g R) : F.nthSeries 0 = fun _ => 0 := rfl

theorem nthSeries_succ (F : MvFormalGroup g R) (n : ℕ) : F.nthSeries (n + 1) = fun i =>
    subst (Sum.elim (F.nthSeries n) fun j => X j) (F.toPowerSeries i) := rfl

/-- Partie linéaire d'un `h`-uplet de séries en `g` variables : la matrice
des coefficients homogènes de degré un. -/
def linearPart (φ : Fin h → MvPowerSeries (Fin g) R) : Matrix (Fin h) (Fin g) R :=
  Matrix.of fun i j => (φ i).coeff (Finsupp.single j 1)

/-- Hauteur finie sur un corps `K` de caractéristique `p` : le quotient de
l'anneau des séries par l'idéal engendré par les composantes de `[p]F` est
un `K`-espace vectoriel de dimension finie. -/
def FiniteHeight (p : ℕ) {K : Type*} [Field K] [CharP K p] (F : MvFormalGroup g K) : Prop :=
  FiniteDimensional K (MvPowerSeries (Fin g) K ⧸ Ideal.span (Set.range (F.nthSeries p)))

end MvFormalGroup

end FormalGroups

end
