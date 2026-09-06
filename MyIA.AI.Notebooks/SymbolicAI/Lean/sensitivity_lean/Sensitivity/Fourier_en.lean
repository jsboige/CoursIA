import Sensitivity.Hypercube_en
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Boolean Fourier analysis on the hypercube

This module defines integer-valued Walsh characters, proves their two
orthogonality relations, and derives a reconstruction formula without division.
It also provides a finite spectral certificate for conjunction in dimension two.
-/

namespace Sensitivity_en

noncomputable section

open Bool Finset Fintype

/-- Signed encoding of a Boolean value. -/
def ξ (b : Bool) : ℤ :=
  if b then -1 else 1

@[simp] lemma ξ_false : ξ false = 1 := rfl
@[simp] lemma ξ_true : ξ true = -1 := rfl

@[simp] lemma ξ_mul_self (b : Bool) : ξ b * ξ b = 1 := by
  cases b <;> norm_num

lemma ξ_mul_eq (a b : Bool) :
    ξ a * ξ b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> norm_num

/-- Walsh character indexed by a subset of coordinates. -/
def χ {n : ℕ} (S : Finset (Fin n)) (x : Q n) : ℤ :=
  ∏ i, if i ∈ S then ξ (x i) else 1

lemma χ_eq_prod_subset {n : ℕ} (S : Finset (Fin n)) (x : Q n) :
    χ S x = ∏ i ∈ S, ξ (x i) := by
  classical
  simp [χ]

/-- Unnormalised Boolean Fourier coefficient. -/
def fourierCoeff {n : ℕ} (f : Q n → ℤ) (S : Finset (Fin n)) : ℤ :=
  ∑ x, f x * χ S x

/-- Distinct Walsh characters are orthogonal on the Boolean hypercube. -/
theorem orthogonality {n : ℕ} (S T : Finset (Fin n)) :
    (∑ x : Q n, χ S x * χ T x) =
      if S = T then (2 : ℤ) ^ n else 0 := by
  classical
  calc
    (∑ x : Q n, χ S x * χ T x) =
        ∏ i : Fin n, ∑ b : Bool,
          (if i ∈ S then ξ b else 1) * (if i ∈ T then ξ b else 1) := by
      simp only [χ, ← Finset.prod_mul_distrib]
      rw [Fintype.prod_sum]
    _ = ∏ i : Fin n, if (i ∈ S) = (i ∈ T) then (2 : ℤ) else 0 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;> simp [hiS, hiT, ξ]
    _ = if S = T then (2 : ℤ) ^ n else 0 := by
      by_cases hST : S = T
      · subst T
        simp
      · have hmem : ∃ i : Fin n, (i ∈ S) ≠ (i ∈ T) := by
          contrapose! hST
          exact Finset.ext fun i => iff_of_eq (hST i)
        obtain ⟨i, hi⟩ := hmem
        rw [if_neg hST]
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]

/-- Summing every Walsh character separates two hypercube vertices. -/
theorem dual_orthogonality {n : ℕ} (x y : Q n) :
    (∑ S : Finset (Fin n), χ S x * χ S y) =
      if x = y then (2 : ℤ) ^ n else 0 := by
  classical
  calc
    (∑ S : Finset (Fin n), χ S x * χ S y) =
        ∑ S : Finset (Fin n), ∏ i ∈ S, (ξ (x i) * ξ (y i)) := by
      apply Finset.sum_congr rfl
      intro S _
      simp only [χ_eq_prod_subset, ← Finset.prod_mul_distrib]
    _ = ∏ i : Fin n, ((ξ (x i) * ξ (y i)) + 1) := by
      simpa using
        (Fintype.prod_add (fun i : Fin n => ξ (x i) * ξ (y i)) (fun _ => (1 : ℤ))).symm
    _ = ∏ i : Fin n, if x i = y i then (2 : ℤ) else 0 := by
      apply Finset.prod_congr rfl
      intro i _
      rw [ξ_mul_eq]
      by_cases h : x i = y i <;> simp [h]
    _ = if x = y then (2 : ℤ) ^ n else 0 := by
      by_cases hxy : x = y
      · subst y
        simp
      · have hcoord : ∃ i : Fin n, x i ≠ y i := by
          contrapose! hxy
          exact funext hxy
        obtain ⟨i, hi⟩ := hcoord
        rw [if_neg hxy]
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]

/-- Fourier reconstruction without division, scaled by the hypercube cardinality. -/
theorem reconstruction {n : ℕ} (f : Q n → ℤ) (x : Q n) :
    (2 : ℤ) ^ n * f x =
      ∑ S : Finset (Fin n), fourierCoeff f S * χ S x := by
  classical
  symm
  calc
    (∑ S : Finset (Fin n), fourierCoeff f S * χ S x) =
        ∑ S : Finset (Fin n), ∑ y : Q n, (f y * χ S y) * χ S x := by
      simp [fourierCoeff, Finset.sum_mul]
    _ = ∑ y : Q n, ∑ S : Finset (Fin n), (f y * χ S y) * χ S x := by
      exact Finset.sum_comm
    _ = ∑ y : Q n, f y * (∑ S : Finset (Fin n), χ S y * χ S x) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = ∑ y : Q n, f y * (if y = x then (2 : ℤ) ^ n else 0) := by
      simp_rw [dual_orthogonality]
    _ = (2 : ℤ) ^ n * f x := by
      simp [mul_comm]

namespace WalshCertificate

/-- Ternary spectral weights for conjunction in dimension two. -/
def weight (S : Finset (Fin 2)) : ℤ :=
  if S = ∅ then 1
  else if S = {0} then 1
  else if S = {1} then 1
  else -1

/-- Every mask weight belongs to the ternary alphabet `{-1, 0, 1}`. -/
theorem weight_is_ternary (S : Finset (Fin 2)) :
    weight S = -1 ∨ weight S = 0 ∨ weight S = 1 := by
  decide +revert

/-- The ternary mask is exactly half the unnormalised spectrum of signed conjunction. -/
theorem fourierCoeff_signedAnd (S : Finset (Fin 2)) :
    fourierCoeff (fun x : Q 2 => ξ (x 0 && x 1)) S = 2 * weight S := by
  decide +revert

/-- Integer score reconstructed from the ternary Walsh mask. -/
def score (x : Q 2) : ℤ :=
  ∑ S : Finset (Fin 2), weight S * χ S x

/-- The finite certificate gives the complete truth table of conjunction. -/
theorem score_and (x : Q 2) :
    score x = if x 0 && x 1 then (-2 : ℤ) else 2 := by
  decide +revert

/-- Boolean gates used by the certified composition. -/
def gateAnd (a b : Bool) : Bool := a && b

def gateNot (a : Bool) : Bool := !a

def gateNand (a b : Bool) : Bool := gateNot (gateAnd a b)

/-- The gate composition computes NAND. -/
theorem gateNand_eq (a b : Bool) : gateNand a b = !(a && b) := by
  rfl

/-- The sign of the Walsh certificate agrees with conjunction. -/
theorem score_sign_is_and (x : Q 2) :
    decide (score x ≤ -1) = gateAnd (x 0) (x 1) := by
  decide +revert

/-- The complementary sign agrees with the NAND composition. -/
theorem score_sign_is_nand (x : Q 2) :
    decide (-1 < score x) = gateNand (x 0) (x 1) := by
  decide +revert

end WalshCertificate

end

end Sensitivity_en
