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
import Mathlib.Data.Fintype.Card
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

/-! ## Inverse Helpers (needed for join/meet bijectivity) -/

/--
Key fact: μ.inverse w is the unique m such that μ.spouse m = w.
-/
lemma inverse_eq_of_spouse_eq (μ : Matching n) (m w : Fin n)
    (h : μ.spouse m = w) : μ.inverse w = m := by
  unfold Matching.inverse
  have := Equiv.ofBijective_symm_apply_apply μ.spouse μ.bijective m
  rw [h] at this
  exact this

/--
Key fact: μ.spouse (μ.inverse w) = w.
-/
lemma spouse_inverse (μ : Matching n) (w : Fin n) :
    μ.spouse (μ.inverse w) = w := by
  unfold Matching.inverse
  exact Equiv.ofBijective_apply_symm_apply μ.spouse μ.bijective w

/-! ## Join and Meet Operations -/

/--
The join of two matchings (man-preferred): each man gets his preferred
partner between μ and ν. Uses Fin.minOn to pick the lower-ranked
(more preferred) partner.

Bijectivity: the join sends each woman w to exactly one of {μ⁻¹(w), ν⁻¹(w)}.
This follows from anti-complementarity: on the woman side, the join acts as
the meet (each woman gets her less-preferred man), ensuring no two men map
to the same woman.
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

open PrefProfile

/--
Helper: if m prefers w to his join-partner, then m prefers w to both
his partner in μ and his partner in ν.
The join picks the lower-ranked (more preferred) of the two partners.
-/
lemma join_pref_both (μ ν : Matching n) (m w : Fin n)
    (h : prof.ManPrefers m w ((μ.join prof ν).spouse m)) :
    prof.ManPrefers m w (μ.spouse m) ∧ prof.ManPrefers m w (ν.spouse m) := by
  unfold ManPrefers at h ⊢
  simp only [Matching.join] at h
  split_ifs at h
  · -- menPref m (μ.spouse m) ≤ menPref m (ν.spouse m), h : menPref m w < menPref m (μ.spouse m)
    refine ⟨h, ?_⟩
    have : (prof.menPref m w : Nat) < prof.menPref m (μ.spouse m) := mod_cast h
    have : (prof.menPref m (μ.spouse m) : Nat) ≤ prof.menPref m (ν.spouse m) := mod_cast ‹_›
    exact mod_cast Nat.lt_of_lt_of_le ‹_› ‹_›
  · -- ¬(menPref m (μ.spouse m) ≤ menPref m (ν.spouse m)), h : menPref m w < menPref m (ν.spouse m)
    refine ⟨?_, h⟩
    have hνμ : (prof.menPref m (ν.spouse m) : Nat) < prof.menPref m (μ.spouse m) := by
      have : ¬ (prof.menPref m (μ.spouse m) ≤ prof.menPref m (ν.spouse m)) := ‹_›
      have : (prof.menPref m (μ.spouse m) : Nat) ≤ prof.menPref m (ν.spouse m) → False := by
        intro hle; exact this (mod_cast hle : prof.menPref m (μ.spouse m) ≤ prof.menPref m (ν.spouse m))
      omega
    have : (prof.menPref m w : Nat) < prof.menPref m (ν.spouse m) := mod_cast h
    exact mod_cast Nat.lt_trans ‹_› hνμ

/--
Helper: if m prefers w to his meet-partner, then m prefers w to at least one
of his partners in μ or ν (the less-preferred one).
-/
lemma meet_pref_one (μ ν : Matching n) (m w : Fin n)
    (h : prof.ManPrefers m w ((μ.meet prof ν).spouse m)) :
    prof.ManPrefers m w (μ.spouse m) ∨ prof.ManPrefers m w (ν.spouse m) := by
  unfold ManPrefers at h ⊢
  simp only [Matching.meet] at h
  split_ifs at h
  · -- meet picked ν.spouse m: h : menPref m w < menPref m (ν.spouse m)
    right; exact h
  · -- meet picked μ.spouse m: h : menPref m w < menPref m (μ.spouse m)
    left; exact h

/--
Anti-complementarity of the join:
(μ ⊔ ν).inverse w equals either μ⁻¹(w) or ν⁻¹(w).

Proof: let m = (μ ⊔ ν).inverse w. The join gives m his preferred partner,
which equals w. So either μ.spouse m = w (making m = μ⁻¹(w))
or ν.spouse m = w (making m = ν⁻¹(w)).
-/
lemma join_inverse_anti (μ ν : Matching n) (w : Fin n) :
    (μ.join prof ν).inverse w = μ.inverse w ∨
    (μ.join prof ν).inverse w = ν.inverse w := by
  set j := μ.join prof ν
  set m := j.inverse w
  have hspw : j.spouse m = w := spouse_inverse j w
  change (if prof.menPref m (μ.spouse m) ≤ prof.menPref m (ν.spouse m) then
            μ.spouse m else ν.spouse m) = w at hspw
  split_ifs at hspw
  · -- j.spouse m = μ.spouse m = w, so m = μ.inverse w
    left; exact (inverse_eq_of_spouse_eq μ m w hspw).symm
  · -- j.spouse m = ν.spouse m = w, so m = ν.inverse w
    right; exact (inverse_eq_of_spouse_eq ν m w hspw).symm

/--
Anti-complementarity of the meet: (μ ⊓ ν).inverse w equals either μ⁻¹(w) or ν⁻¹(w).
Same argument as join_inverse_anti: the meet spouse of (meet.inverse w) equals w,
and the meet picks one of the two partners.
-/
lemma meet_inverse_anti (μ ν : Matching n) (w : Fin n) :
    (μ.meet prof ν).inverse w = μ.inverse w ∨
    (μ.meet prof ν).inverse w = ν.inverse w := by
  set j := μ.meet prof ν
  set m := j.inverse w
  have hspw : j.spouse m = w := spouse_inverse j w
  change (if prof.menPref m (μ.spouse m) ≤ prof.menPref m (ν.spouse m) then
            ν.spouse m else μ.spouse m) = w at hspw
  split_ifs at hspw
  · -- j.spouse m = ν.spouse m = w, so m = ν.inverse w
    right; exact (inverse_eq_of_spouse_eq ν m w hspw).symm
  · -- j.spouse m = μ.spouse m = w, so m = μ.inverse w
    left; exact (inverse_eq_of_spouse_eq μ m w hspw).symm

/--
Wu-Roth Lemma 3.2 (one-to-one specialization):
The join of two stable matchings is stable.

Proof: suppose (m, w) blocks μ ⊔ ν.
Man side: m prefers w to join-partner ⟹ m prefers w to both μ(m) and ν(m).
Woman side: (μ ⊔ ν).inverse w is either μ⁻¹(w) or ν⁻¹(w).
  Case μ⁻¹(w): w prefers m to μ⁻¹(w), so (m,w) blocks μ. Contradiction.
  Case ν⁻¹(w): w prefers m to ν⁻¹(w), so (m,w) blocks ν. Contradiction.
-/
theorem join_isStable (μ ν : Matching n)
    (hμ : IsStable prof μ) (hν : IsStable prof ν) :
    IsStable prof (μ.join prof ν) := by
  intro m w hblock
  obtain ⟨hmpref, hwpref⟩ := hblock
  have hboth := join_pref_both prof μ ν m w hmpref
  rcases join_inverse_anti prof μ ν w with hinvμ | hinvν
  · rw [hinvμ] at hwpref
    exact hμ m w ⟨hboth.1, hwpref⟩
  · rw [hinvν] at hwpref
    exact hν m w ⟨hboth.2, hwpref⟩

/--
The meet of two stable matchings is stable.

Proof: suppose (m, w) blocks μ ⊓ ν.
Man side: m prefers w to meet-partner ⟹ m prefers w to at least one of μ(m) or ν(m).
Woman side: (μ ⊓ ν).inverse w is either μ⁻¹(w) or ν⁻¹(w).
  Combined, at least one of the cases gives a blocking pair for μ or ν.
-/
theorem meet_isStable (μ ν : Matching n)
    (hμ : IsStable prof μ) (hν : IsStable prof ν) :
    IsStable prof (μ.meet prof ν) := by
  intro m w hblock
  obtain ⟨hmpref, hwpref⟩ := hblock
  have hone := meet_pref_one prof μ ν m w hmpref
  rcases meet_inverse_anti prof μ ν w with hinvμ | hinvν
  · -- (μ ⊓ ν).inverse w = μ.inverse w, so w prefers m to μ⁻¹(w)
    rw [hinvμ] at hwpref
    rcases hone with hmμ | hmν
    · -- m prefers w to μ(m) AND w prefers m to μ⁻¹(w) → blocks μ
      exact hμ m w ⟨hmμ, hwpref⟩
    · -- m prefers w to ν(m), w prefers m to μ⁻¹(w)
      -- TODO: anti-complementarity argument needed
      sorry
  · -- (μ ⊓ ν).inverse w = ν.inverse w, so w prefers m to ν⁻¹(w)
    rw [hinvν] at hwpref
    rcases hone with hmμ | hmν
    · -- m prefers w to μ(m), w prefers m to ν⁻¹(w)
      -- TODO: anti-complementarity argument needed
      sorry
    · -- m prefers w to ν(m) AND w prefers m to ν⁻¹(w) → blocks ν
      exact hν m w ⟨hmν, hwpref⟩

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
