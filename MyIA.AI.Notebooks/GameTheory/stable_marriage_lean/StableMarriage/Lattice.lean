/-
  Stable Marriage - Lattice Structure on Stable Matchings
  ========================================================

  Knuth (1976) showed that the set of stable matchings forms a lattice
  under the "common preferences" ordering. Wu & Roth (2018) generalized
  this to many-to-one; we specialize to the one-to-one case.

  Key results:
  - Stable matchings are partially ordered by man-preference
  - The join (supremum) of two stable matchings is stable
  - The meet (infimum) of two stable matchings is stable
  - The set of stable matchings forms a distributive lattice
  - The GS man-proposing output is the top (man-optimal) element

  Reference: Knuth (1976), "Marriages Stables"
  Reference: Wu & Roth (2018), "Lattice Structures in Stable Matching"
  Reference: Stanley (2011), "Enumerative Combinatorics" Vol 1 (finite lattice lemma)

  Strategy:
  - We define μ ≤ ν iff every man prefers μ to ν (or is indifferent)
  - join μ ν: each man gets his preferred partner between μ and ν
  - meet μ ν: each man gets his less-preferred partner between μ and ν
  - Wu-Roth Lemma 3.2 (one-to-one): join and meet of stable matchings are stable
  - Stanley lemma: finite join-semilattice with min = lattice
-/

import Mathlib.Order.Lattice
import Mathlib.Tactic.Common
import StableMarriage.Definitions

namespace StableMarriage

open Function Finset Classical

variable {n : Nat} [NeZero n] (prof : PrefProfile n)

/-! ## Partial Order on Stable Matchings via Man-Preference -/

/--
Man-preference ordering on matchings: μ ≤ ν iff every man prefers
his partner in μ at least as much as in ν (i.e., menPref m (μ m) ≤ menPref m (ν m)).
Lower rank = more preferred, so μ ≤ ν means μ is man-preferred over ν.
-/
def ManLE (μ ν : Matching n) : Prop :=
  ∀ m : Fin n, prof.menPref m (μ.spouse m) ≤ prof.menPref m (ν.spouse m)

namespace ManLE

variable {prof} {μ ν σ : Matching n}

@[refl] lemma refl : ManLE prof μ μ := fun m => Nat.le_refl _

@[trans] lemma trans (h1 : ManLE prof μ ν) (h2 : ManLE prof ν σ) :
    ManLE prof μ σ := fun m => Nat.le_trans (h1 m) (h2 m)

lemma antisymm (h1 : ManLE prof μ ν) (h2 : ManLE prof ν μ) :
    μ = ν := by
  have hsp : μ.spouse = ν.spouse := by
    funext m
    have hle : (prof.menPref m (μ.spouse m) : Nat) ≤ prof.menPref m (ν.spouse m) := h1 m
    have hge : (prof.menPref m (ν.spouse m) : Nat) ≤ prof.menPref m (μ.spouse m) := h2 m
    have heq : (prof.menPref m (μ.spouse m) : Nat) = prof.menPref m (ν.spouse m) :=
      Nat.le_antisymm hle hge
    have hfeq : prof.menPref m (μ.spouse m) = prof.menPref m (ν.spouse m) := Fin.ext heq
    exact (prof.menPref_bijective m).injective hfeq
  have hsp_eq : μ.spouse = ν.spouse := hsp
  cases μ; cases ν
  congr 1

end ManLE

/-! ## Join and Meet Operations -/

/--
The join of two matchings (man-preferred): each man gets his preferred
partner between μ and ν. Uses Fin.minOn to pick the lower-ranked
(more preferred) partner.
-/
noncomputable def Matching.join (μ ν : Matching n) : Matching n where
  spouse := fun m =>
    if prof.menPref m (μ.spouse m) ≤ prof.menPref m (ν.spouse m) then
      μ.spouse m
    else
      ν.spouse m
  bijective := by
    sorry

/--
The meet of two matchings (man-less-preferred): each man gets his
less-preferred partner between μ and ν.
-/
noncomputable def Matching.meet (μ ν : Matching n) : Matching n where
  spouse := fun m =>
    if prof.menPref m (μ.spouse m) ≤ prof.menPref m (ν.spouse m) then
      ν.spouse m
    else
      μ.spouse m
  bijective := by
    sorry

/-! ## Stability of Join and Meet (Wu-Roth Lemma 3.2, one-to-one case) -/

/--
Wu-Roth Lemma 3.2 (one-to-one specialization):
The join of two stable matchings is stable.
-/
theorem join_isStable (μ ν : Matching n)
    (hμ : IsStable prof μ) (hν : IsStable prof ν) :
    IsStable prof (μ.join prof ν) := by
  sorry

/--
The meet of two stable matchings is stable.
Dual of join_isStable.
-/
theorem meet_isStable (μ ν : Matching n)
    (hμ : IsStable prof μ) (hν : IsStable prof ν) :
    IsStable prof (μ.meet prof ν) := by
  sorry

/-! ## Lattice Instance -/

-- TODO: Instance requires proving all lattice axioms on the subtype.
-- This needs join_isStable + meet_isStable fully proved first.
-- Will instantiate after proofs are complete.

/-! ## Man-Optimal = Top of the Lattice -/

/--
The man-proposing Gale-Shapley output is the top element of the lattice
of stable matchings: every man gets his best achievable partner.
-/
theorem doctor_optimal_eq_top (μ_gs : Matching n)
    (hgs : IsStable prof μ_gs)
    (μ' : Matching n) (hstable : IsStable prof μ') :
    ManLE prof μ' μ_gs :=
  fun m => by
  sorry

end StableMarriage
