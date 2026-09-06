import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Multivariate formal groups: the basic structure

This module defines the notion of **multivariate formal group** of dimension
`g` over a commutative ring `R`: a composition law given by `g` formal power
series in `2g` variables (the two copies of the ambient space), whose origin
is the identity and whose linear part is the identity map.

The upstream file is `Definitions/Def_MvFormalGroup_BasicV2.lean` from
[`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem)
(commit `aa2d8b34`, Apache-2.0 — see `NOTICE`), split here into progressive
modules (issue #14785). Witt, Cartier and Artin–Hasse are out of scope.
-/

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace FormalGroups_en

/-- A multivariate formal group of dimension `g` over `R`: the law is a
`g`-tuple of formal power series in `2g` variables satisfying the identity
axiom (vanishing constant coefficient), the identity linear part, and
associativity (via substitution). -/
@[ext]
structure MvFormalGroup (g : ℕ) (R : Type*) [CommRing R] where

  toPowerSeries : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R

  /-- The constant coefficient vanishes: the origin is the identity of the law. -/
  constantCoeff_eq_zero : ∀ i, (toPowerSeries i).constantCoeff = 0

  /-- Linear part, first copy: each component `i` depends linearly on the
  variable `inl i` only. -/
  coeff_single_inl : ∀ i j,
    (toPowerSeries i).coeff (Finsupp.single (Sum.inl j) 1) = if i = j then 1 else 0

  /-- Linear part, second copy: symmetric to `coeff_single_inl` for the
  variable `inr j`. -/
  coeff_single_inr : ∀ i j,
    (toPowerSeries i).coeff (Finsupp.single (Sum.inr j) 1) = if i = j then 1 else 0

  /-- Associativity of the law: substituting the law into the law, on the
  left or on the right, yields the same series in `3g` variables. -/
  assoc : ∀ i,
    subst
      (Sum.elim
        (fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
            fun l => X (Sum.inr (Sum.inl l)))
          (toPowerSeries j))
        fun j => X (Sum.inr (Sum.inr j)))
      (toPowerSeries i)
      =
    subst
      (Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
            fun l => X (Sum.inr (Sum.inr l)))
          (toPowerSeries j))
      (toPowerSeries i)

namespace MvFormalGroup

variable {g : ℕ} {R : Type*} [CommRing R]

/-- Commutativity of a multivariate formal group: the law is invariant under
swapping the two blocks of variables. A `Prop` class, instantiated for the
additive law in `FormalGroups.Additive_en`. -/
class IsComm (F : MvFormalGroup g R) : Prop where
  comm : ∀ i,
    subst
      (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        fun j => X (Sum.inl j))
      (F.toPowerSeries i)
      = F.toPowerSeries i

/-- The law of a formal group is substitutable: its components have
vanishing constant coefficients. -/
theorem hasSubst_toPowerSeries (F : MvFormalGroup g R) : HasSubst F.toPowerSeries :=
  hasSubst_of_constantCoeff_zero F.constantCoeff_eq_zero

/-- Substitution is additive on sums of indeterminates:
`subst a (X s + X t) = a s + a t` whenever the family `a` has vanishing
constant coefficients. Key lemma in the associativity proofs of the
additive law. -/
theorem subst_X_add_X {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, (a s).constantCoeff = 0) (s t : σ) :
    subst a (X s + X t : MvPowerSeries σ R) = a s + a t := by
  have h := hasSubst_of_constantCoeff_zero ha
  rw [subst_add h, subst_X h, subst_X h]

end MvFormalGroup

end FormalGroups_en

end
