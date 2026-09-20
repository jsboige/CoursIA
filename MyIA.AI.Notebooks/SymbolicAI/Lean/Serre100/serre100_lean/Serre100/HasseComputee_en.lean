import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Hasse computed by the kernel: counting points of an elliptic curve over F_p

Kernel pendant of the notebook `01-corps-finis-borne-hasse.ipynb` (series
*Serre 100*, EPIC #16334 — "kernel pendants" graduation path). The
notebook *measures* the Hasse bound in Python; this module has the Lean
*kernel verify it* on the same curves, and proves the identity relating
the Frobenius trace to the quadratic character (exercise 2 of the
notebook).

Plan, mirroring the notebook:

1. **Definitions** (`pointsAffines`, `nombrePoints`, `traceFrobenius`,
   `Lisse`) — over `ZMod p` as a ring: counting does not require
   primality, only the identity of §3 does.
2. **Kernel verifications**: the notebook's table (cell "The Frobenius
   trace", curve `y² = x³ + 2x + 3`) is reproduced exactly, and the
   bound `t² ≤ 4p` is verified over **all** smooth curves of `F_5`,
   `F_7` and `F_11` — the notebook's "Toutes sous la borne : True",
   proved rather than observed.
3. **The trace/character identity**: `t = -∑ x, χ (x³ + ax + b)`,
   where `χ` is the quadratic character of `ZMod p` — exercise 2 of
   the notebook, proved for every odd prime `p`.
-/

set_option autoImplicit false

namespace Serre100_en

/-! ## Definitions — the notebook's vocabulary, in Lean

An affine point of the curve `y² = x³ + ax + b` over `ZMod p` is a pair
satisfying the equation; the point at infinity counts for one. The
Frobenius trace is `t = p + 1 - #E`, non-singularity is `4a³ + 27b² ≠ 0`.
-/

/-- Affine points of `y² = x³ + ax + b` over `ZMod p` (without the point
at infinity). Defined over the ring `ZMod p`: counting does not require
`p` to be prime. -/
def pointsAffines (p : ℕ) [NeZero p] (a b : ZMod p) :
    Finset (ZMod p × ZMod p) :=
  Finset.univ.filter (fun xy => xy.2 ^ 2 = xy.1 ^ 3 + a * xy.1 + b)

/-- Number of points of the curve, point at infinity included
(notebook, `nombre_points`). -/
def nombrePoints (p : ℕ) [NeZero p] (a b : ZMod p) : ℕ :=
  1 + (pointsAffines p a b).card

/-- Frobenius trace `t = p + 1 - #E` (notebook, `trace_frobenius`). -/
def traceFrobenius (p : ℕ) [NeZero p] (a b : ZMod p) : ℤ :=
  (p : ℤ) + 1 - (nombrePoints p a b : ℤ)

/-- Non-singularity: `4a³ + 27b² ≠ 0` in `ZMod p` (notebook,
`est_lisse`). -/
@[reducible] def Lisse (p : ℕ) [NeZero p] (a b : ZMod p) : Prop :=
  4 * a ^ 3 + 27 * b ^ 2 ≠ 0

/-! ## The Hasse bound, verified by the kernel

The notebook observes (`Toutes sous la borne : True`, 1701 measured
curves); the kernel here proves the same counts, exactly. The integer
form of the bound `|t| ≤ 2√p` is `t² ≤ 4p`.
-/

/-- The notebook's flagship curve (`a = 2`, `b = 3`, `p = 7`): 5 affine
points, 6 with the point at infinity — cell "counting the points". -/
example : (pointsAffines 7 2 3).card = 5 := by decide

example : nombrePoints 7 2 3 = 6 := by decide

/-- The notebook's table (cell "The Frobenius trace"), curve
`y² = x³ + 2x + 3`, reproduced row by row. -/
example : traceFrobenius 5 2 3 = -1 := by decide
example : traceFrobenius 7 2 3 = 2 := by decide
example : traceFrobenius 11 2 3 = -1 := by decide
example : traceFrobenius 13 2 3 = -4 := by decide
example : traceFrobenius 17 2 3 = -4 := by decide
example : traceFrobenius 19 2 3 = 0 := by decide
example : traceFrobenius 23 2 3 = 0 := by decide
example : traceFrobenius 29 2 3 = -6 := by decide

/-- The Hasse bound, integer form `t² ≤ 4p`, over **all** smooth curves
of `F_5`. -/
example : ∀ a b : ZMod 5, Lisse 5 a b →
    (traceFrobenius 5 a b) ^ 2 ≤ (4 * 5 : ℤ) := by decide

/-- The Hasse bound over **all** smooth curves of `F_7`. -/
example : ∀ a b : ZMod 7, Lisse 7 a b →
    (traceFrobenius 7 a b) ^ 2 ≤ (4 * 7 : ℤ) := by decide

/-- The Hasse bound over **all** smooth curves of `F_11`. -/
example : ∀ a b : ZMod 11, Lisse 11 a b →
    (traceFrobenius 11 a b) ^ 2 ≤ (4 * 11 : ℤ) := by decide

/-! ## The trace/character identity — notebook exercise 2, proved

The notebook asks (exercise 2) to verify that
`∑ x, χ (x³ + ax + b) = -t`, where `χ` is the Legendre symbol. We prove
it here for every odd prime `p`, in three steps: each fibre of the
square counts `1 + χ v` solutions; summing over `x` counts the affine
points; rearranging yields the trace.
-/

section Identite

open Finset

variable {p : ℕ} [NeZero p] [Fact p.Prime]

omit [NeZero p] in
private theorem deux_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hp : p.Prime := Fact.out
  have h2le : 2 ≤ p := hp.two_le
  have hd : p ∣ (2 : ℕ) := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  have hple : p ≤ 2 := Nat.le_of_dvd two_pos hd
  omega

/-- Fibre of the square in odd characteristic: for every `v`, the
number of `y` with `y² = v` is exactly `1 + χ v` — the three regimes
(`v = 0`: one solution; nonzero square: two; non-square: none). -/
theorem card_fibre_carre (hp2 : p ≠ 2) (v : ZMod p) :
    ((Finset.univ.filter (fun y : ZMod p => y ^ 2 = v)).card : ℤ)
      = 1 + quadraticChar (ZMod p) v := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    have hsingleton :
        (Finset.univ.filter (fun y : ZMod p => y ^ 2 = 0)) = {(0 : ZMod p)} := by
      apply Finset.eq_singleton_iff_unique_mem.2
      refine ⟨by simp, ?_⟩
      intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      exact sq_eq_zero_iff.1 hy
    rw [hsingleton, Finset.card_singleton, quadraticChar_zero]
    norm_num
  · by_cases hsq : IsSquare v
    · obtain ⟨w, hw⟩ := hsq
      have hwm : w * w = v := hw.symm
      have hw0 : w ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hwm
        exact hv hwm.symm
      have hwneg : w ≠ -w := by
        intro h
        apply hw0
        have h2 : (2 : ZMod p) * w = 0 := by
          linear_combination h
        exact ((mul_eq_zero.1 h2).resolve_left (deux_ne_zero_zmod hp2))
      have hsol :
          (Finset.univ.filter (fun y : ZMod p => y ^ 2 = v)) = insert w {-w} := by
        ext y
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        constructor
        · intro hy
          have hprod : (y - w) * (y + w) = 0 := by
            linear_combination hy - hwm
          rcases mul_eq_zero.1 hprod with h | h
          · exact Or.inl (sub_eq_zero.1 h)
          · exact Or.inr (eq_neg_iff_add_eq_zero.2 h)
        · rintro (rfl | rfl)
          · rw [← hwm]; ring
          · rw [← hwm]; ring
      have hcard : (insert w {-w} : Finset (ZMod p)).card = 2 := by
        rw [Finset.card_insert_of_notMem, Finset.card_singleton]
        intro hmem
        exact hwneg (by simpa using hmem)
      have hchi : quadraticChar (ZMod p) v = 1 := by
        rw [← hwm, ← pow_two]
        exact quadraticChar_sq_one' hw0
      rw [hsol, hcard, hchi]
      norm_num
    · have hempty : (Finset.univ.filter (fun y : ZMod p => y ^ 2 = v)) = ∅ := by
        ext y
        simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
        intro hy
        exact hsq ⟨y, by simpa [pow_two] using hy.symm⟩
      have hchi : quadraticChar (ZMod p) v = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.2 hsq
      rw [hempty, Finset.card_empty, hchi]
      norm_num

/-- Counting by fibres: the affine points are counted by summing over
`x` the number of `y` in the fibre of the square. -/
theorem card_pointsAffines_eq_sum (a b : ZMod p) :
    (pointsAffines p a b).card
      = ∑ x : ZMod p, (Finset.univ.filter
          (fun y : ZMod p => y ^ 2 = x ^ 3 + a * x + b)).card := by
  unfold pointsAffines
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  show ∑ y ∈ (Finset.univ : Finset (ZMod p)),
      (if y ^ 2 = x ^ 3 + a * x + b then (1 : ℕ) else 0)
    = (Finset.univ.filter
          (fun y : ZMod p => y ^ 2 = x ^ 3 + a * x + b)).card
  rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]

/-- The identity of notebook exercise 2: the Frobenius trace is the
negated sum of the quadratic character over the abscissas,
`∑ x, χ (x³ + ax + b) = -t`, for every curve (even a singular one — the
identity is purely combinatorial). -/
theorem trace_eg_moins_somme_caractere (hp2 : p ≠ 2) (a b : ZMod p) :
    traceFrobenius p a b
      = -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b) := by
  have hfib : ∀ x : ZMod p,
      ((Finset.univ.filter
        (fun y : ZMod p => y ^ 2 = x ^ 3 + a * x + b)).card : ℤ)
        = 1 + quadraticChar (ZMod p) (x ^ 3 + a * x + b) :=
    fun x => card_fibre_carre hp2 _
  have hcard : ((pointsAffines p a b).card : ℤ)
      = (Fintype.card (ZMod p) : ℤ)
        + ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b) := by
    have h1 : ∑ x : ZMod p, ((1 : ℤ) + quadraticChar (ZMod p) (x ^ 3 + a * x + b))
        = ((pointsAffines p a b).card : ℤ) := by
      rw [card_pointsAffines_eq_sum, Nat.cast_sum]
      exact Finset.sum_congr rfl fun x _ => (hfib x).symm
    have hsu : (Fintype.card (ZMod p) : ℤ)
        = ∑ x : ZMod p, (1 : ℤ) := by
      simp [Finset.sum_const, Finset.card_univ]
    calc ((pointsAffines p a b).card : ℤ)
        = ∑ x : ZMod p, ((1 : ℤ) + quadraticChar (ZMod p) (x ^ 3 + a * x + b)) :=
          h1.symm
      _ = (Fintype.card (ZMod p) : ℤ)
            + ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x + b) := by
          rw [Finset.sum_add_distrib, ← hsu]
  rw [traceFrobenius, nombrePoints]
  push_cast
  rw [hcard, ZMod.card]
  ring

end Identite

end Serre100_en
