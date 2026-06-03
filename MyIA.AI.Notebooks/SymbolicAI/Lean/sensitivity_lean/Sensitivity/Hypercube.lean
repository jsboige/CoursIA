/-
Copyright (c) 2019 Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Jesse Michael Han, Chris Hughes, Robert Y. Lewis,
  Patrick Massot

Port of mathlib4/Archive/Sensitivity.lean to standalone Lake workspace.
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FinCases

/-!
# The hypercube for Huang's sensitivity theorem

This file defines the hypercube `Q n = Fin n → Bool` and its adjacency relation.
-/

namespace Sensitivity

noncomputable section

open Bool Finset Fintype

/-!
### The hypercube

Notations:
- `ℕ` denotes natural numbers (including zero).
- `Fin n` = {0, ⋯ , n - 1}.
- `Bool` = {`true`, `false`}.
-/


/-- The hypercube in dimension `n`. -/
abbrev Q (n : ℕ) :=
  Fin n → Bool

/-- The projection from `Q n.succ` to `Q n` forgetting the first value
(i.e. the image of zero). -/
def π {n : ℕ} : Q n.succ → Q n := fun p => p ∘ Fin.succ

namespace Q

@[ext]
theorem ext {n} {f g : Q n} (h : ∀ x, f x = g x) : f = g := funext h

variable (n : ℕ)

/-- `Q 0` has a unique element. -/
instance : Unique (Q 0) :=
  ⟨⟨fun _ => true⟩, by intro; ext x; fin_cases x⟩

/-- `Q n` has 2^n elements. -/
theorem card : Fintype.card (Q n) = 2 ^ n := by simp

variable {n}

theorem succ_n_eq (p q : Q n.succ) : p = q ↔ p 0 = q 0 ∧ π p = π q := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h₀, h⟩
    ext x
    by_cases hx : x = 0
    · rwa [hx]
    · rw [← Fin.succ_pred x hx]
      convert congr_fun h (Fin.pred x hx)

/-- The adjacency relation defining the graph structure on `Q n`:
`p.adjacent q` if there is an edge from `p` to `q` in `Q n`. -/
def adjacent {n : ℕ} (p : Q n) : Set (Q n) := { q | ∃! i, p i ≠ q i }

/-- In `Q 0`, no two vertices are adjacent. -/
theorem not_adjacent_zero (p q : Q 0) : q ∉ p.adjacent := by rintro ⟨v, _⟩; apply finZeroElim v

/-- If `p` and `q` in `Q n.succ` have different values at zero then they are adjacent
iff their projections to `Q n` are equal. -/
theorem adj_iff_proj_eq {p q : Q n.succ} (h₀ : p 0 ≠ q 0) : q ∈ p.adjacent ↔ π p = π q := by
  constructor
  · rintro ⟨i, _, h_uni⟩
    ext x; by_contra hx
    apply Fin.succ_ne_zero x
    rw [h_uni _ hx, h_uni _ h₀]
  · intro heq
    use 0, h₀
    intro y hy
    contrapose! hy
    rw [← Fin.succ_pred _ hy]
    apply congr_fun heq

/-- If `p` and `q` in `Q n.succ` have the same value at zero then they are adjacent
iff their projections to `Q n` are adjacent. -/
theorem adj_iff_proj_adj {p q : Q n.succ} (h₀ : p 0 = q 0) :
    q ∈ p.adjacent ↔ π q ∈ (π p).adjacent := by
  constructor
  · rintro ⟨i, h_eq, h_uni⟩
    have h_i : i ≠ 0 := fun h_i => absurd h₀ (by rwa [h_i] at h_eq)
    use i.pred h_i,
      show p (Fin.succ (Fin.pred i _)) ≠ q (Fin.succ (Fin.pred i _)) by rwa [Fin.succ_pred]
    intro y hy
    simp [Eq.symm (h_uni _ hy)]
  · rintro ⟨i, h_eq, h_uni⟩
    use i.succ, h_eq
    intro y hy
    rw [← Fin.pred_inj (ha := (?ha : y ≠ 0)) (hb := (?hb : i.succ ≠ 0)),
      Fin.pred_succ]
    case ha =>
      contrapose hy
      rw [hy, h₀]
    case hb =>
      apply Fin.succ_ne_zero
    apply h_uni
    simp [π, hy]

@[symm]
theorem adjacent.symm {p q : Q n} : q ∈ p.adjacent ↔ p ∈ q.adjacent := by
  simp only [adjacent, ne_comm, Set.mem_setOf_eq]

end Q

end

end Sensitivity
