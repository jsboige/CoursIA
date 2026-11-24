import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Algebraic certificate at the quarter point

This layer derives the prefix identity from a local recurrence. The
identification `tᵢ = (2i+1)aᵢ` is built into the summand. It does not
formalize elliptic curves, Cartier operators or Frobenius.
-/

namespace CartierMiller_en

open Finset

variable {F : Type*} [Field F]

/-- The certificate follows from the local recurrence alone. -/
theorem telescoping_certificate (a b x : F)
    (recurrence : 4 * (x + 1) * b = (2 * x + 1) * a) :
    ((2 * x + 1)^2 - 8) * a =
      -4 * (x + 1) * (2 * x + 7) * b + 4 * x * (2 * x + 5) * a := by
  calc
    _ = -(2 * x + 7) * ((2 * x + 1) * a) + 4 * x * (2 * x + 5) * a := by ring
    _ = _ := by rw [← recurrence]; ring

/-- The prefix sums satisfy the telescoping identity for every sequence
satisfying the recurrence at the indices used. -/
theorem prefix_sum_identity (a : ℕ → F) (h : F) (L : ℕ)
    (half : 2 * h + 1 = 0)
    (recurrence : ∀ i < L, 4 * ((i : F) + 1) * a (i + 1) =
      (2 * (i : F) + 1) * a i) :
    (∑ i ∈ range L, (h + 1 + (i : F)) * ((2 * (i : F) + 1) * a i)) =
      4 * (∑ i ∈ range L, a i) - 2 * (L : F) * (2 * (L : F) + 5) * a L := by
  induction L with
  | zero => simp
  | succ L ih =>
    have prev := ih (fun i hi => recurrence i (Nat.lt_succ_of_lt hi))
    have cert := telescoping_certificate (a L) (a (L + 1)) (L : F)
      (recurrence L (Nat.lt_succ_self L))
    have hh := congrArg (fun y : F => y * ((2 * (L : F) + 1) * a L)) half
    rw [sum_range_succ, sum_range_succ]
    simp only [Nat.cast_succ]
    have two_ne : (2 : F) ≠ 0 := by
      intro h2
      simp [h2] at half
    apply (mul_left_cancel₀ two_ne)
    linear_combination 2 * prev + hh + cert

/-- At the quarter point, the boundary coefficient is nine quarters. -/
theorem quarter_point_coefficient (n : F) (quarter : 4 * n + 1 = 0)
    (four_ne : (4 : F) ≠ 0) : -2 * n * (2 * n + 5) = 9 / 4 := by
  field_simp
  linear_combination (-4 * n - 9) * quarter

/-- Specialization of the prefix identity at the quarter point. -/
theorem quarter_point_identity (a : ℕ → F) (h : F) (n : ℕ)
    (half : 2 * h + 1 = 0)
    (recurrence : ∀ i < n, 4 * ((i : F) + 1) * a (i + 1) =
      (2 * (i : F) + 1) * a i)
    (quarter : 4 * (n : F) + 1 = 0) (four_ne : (4 : F) ≠ 0) :
    (∑ i ∈ range n, (h + 1 + (i : F)) * ((2 * (i : F) + 1) * a i)) =
      4 * (∑ i ∈ range n, a i) + (9 / 4 : F) * a n := by
  have hp := prefix_sum_identity a h n half recurrence
  have hq := quarter_point_coefficient (n : F) quarter four_ne
  calc
    _ = 4 * (∑ i ∈ range n, a i) + (-2 * (n : F) * (2 * (n : F) + 5)) * a n := by
      rw [hp]; ring
    _ = _ := by rw [hq]

instance : Fact (Nat.Prime 97) := ⟨by decide⟩

/-- The binomial sequence of the repository oracle, reduced modulo 97. -/
def oracle97 (i : ℕ) : ZMod 97 :=
  ((Nat.factorial (2 * i) / (Nat.factorial i * Nat.factorial (2 * i - i)) : ℕ) : ZMod 97) * 85 ^ i

theorem oracle97_binomial (i : ℕ) :
    oracle97 i = (Nat.choose (2 * i) i : ZMod 97) / 8 ^ i := by
  rw [Nat.choose_eq_factorial_div_factorial (by omega : i ≤ 2 * i)]
  have inv8 : (8 : ZMod 97)⁻¹ = 85 := by
    apply inv_eq_of_mul_eq_one_left
    decide
  unfold oracle97
  rw [div_eq_mul_inv, ← inv_pow, inv8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The recurrence holds at the 24 required indices. -/
theorem oracle97_recurrence : ∀ i : Fin 24,
    4 * ((i.val : ZMod 97) + 1) * oracle97 (i.val + 1) =
      (2 * (i.val : ZMod 97) + 1) * oracle97 i.val := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Three computed values and a negative control. -/
theorem oracle97_values :
    oracle97 24 = 79 ∧ (∑ i ∈ range 24, oracle97 i) = 33 ∧
    (∑ i ∈ range 24, (48 + 1 + (i : ZMod 97)) *
      ((2 * (i : ZMod 97) + 1) * oracle97 i)) = 43 ∧
    (43 : ZMod 97) ≠ 4 * 33 := by
  decide

/-- The general specialization applies to a nonzero sequence. -/
theorem oracle97_quarter :
    (∑ i ∈ range 24, (48 + 1 + (i : ZMod 97)) *
      ((2 * (i : ZMod 97) + 1) * oracle97 i)) =
    4 * (∑ i ∈ range 24, oracle97 i) + (9 / 4 : ZMod 97) * oracle97 24 := by
  apply quarter_point_identity oracle97 48 24
  · decide
  · intro i hi
    exact oracle97_recurrence ⟨i, hi⟩
  · decide
  · decide

end CartierMiller_en
