import Sensitivity.Hypercube_en
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Boolean Fourier analysis on the hypercube

This module defines integer-valued Walsh characters, proves their two
orthogonality relations, and derives reconstruction, Parseval, and the identity
between Boolean influence and spectral mass, without division. It also provides
a finite spectral certificate for conjunction in dimension two.
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

@[simp] lemma ξ_not (b : Bool) : ξ (!b) = -ξ b := by
  cases b <;> norm_num [ξ]

/-- Vertex obtained by flipping coordinate `i` of the hypercube. -/
def flip {n : ℕ} (x : Q n) (i : Fin n) : Q n :=
  Function.update x i !(x i)

@[simp] lemma flip_apply_self {n : ℕ} (x : Q n) (i : Fin n) :
    flip x i i = !(x i) := by
  simp [flip]

lemma flip_apply_ne {n : ℕ} (x : Q n) (i : Fin n)
    {j : Fin n} (hij : j ≠ i) : flip x i j = x j := by
  simp [flip, hij]

/-- Flipping the same coordinate twice restores the original vertex. -/
@[simp] theorem flip_flip {n : ℕ} (x : Q n) (i : Fin n) :
    flip (flip x i) i = x := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [flip_apply_ne _ _ hji]

/-- Flipping a coordinate modulates a Walsh character by its membership sign. -/
theorem χ_flip {n : ℕ} (S : Finset (Fin n)) (x : Q n) (i : Fin n) :
    χ S (flip x i) = χ S x * (if i ∈ S then -1 else 1) := by
  classical
  by_cases hi : i ∈ S
  · rw [if_pos hi, χ_eq_prod_subset, χ_eq_prod_subset]
    calc
      (∏ j ∈ S, ξ (flip x i j)) =
          ξ (flip x i i) * ∏ j ∈ S.erase i, ξ (flip x i j) := by
            rw [Finset.mul_prod_erase S (fun j => ξ (flip x i j)) hi]
      _ = (-ξ (x i)) * ∏ j ∈ S.erase i, ξ (x j) := by
            rw [flip_apply_self, ξ_not]
            congr 1
            apply Finset.prod_congr rfl
            intro j hj
            simp only [Finset.mem_erase] at hj
            rw [flip_apply_ne x i hj.1]
      _ = (∏ j ∈ S, ξ (x j)) * -1 := by
            have hp := Finset.mul_prod_erase S (fun j => ξ (x j)) hi
            calc
              (-ξ (x i)) * ∏ j ∈ S.erase i, ξ (x j) =
                  -(ξ (x i) * ∏ j ∈ S.erase i, ξ (x j)) := by ring
              _ = -(∏ j ∈ S, ξ (x j)) := by rw [hp]
              _ = (∏ j ∈ S, ξ (x j)) * -1 := by ring
  · rw [if_neg hi, χ_eq_prod_subset, χ_eq_prod_subset, mul_one]
    apply Finset.prod_congr rfl
    intro j hj
    rw [flip_apply_ne x i]
    exact fun hji => hi (hji ▸ hj)

/-- Flipping a coordinate changes exactly the spectral signs of sets containing it. -/
theorem fourierCoeff_flip {n : ℕ} (f : Q n → ℤ)
    (i : Fin n) (S : Finset (Fin n)) :
    fourierCoeff (fun x => f (flip x i)) S =
      if i ∈ S then -fourierCoeff f S else fourierCoeff f S := by
  classical
  let e : Q n ≃ Q n :=
    { toFun := fun x => flip x i
      invFun := fun x => flip x i
      left_inv := fun x => flip_flip x i
      right_inv := fun x => flip_flip x i }
  calc
    fourierCoeff (fun x => f (flip x i)) S =
        ∑ x : Q n, (fun y => f y * χ S (flip y i)) (e x) := by
          simp [fourierCoeff, e]
    _ = ∑ y : Q n, f y * χ S (flip y i) := by
          exact e.sum_comp (fun y => f y * χ S (flip y i))
    _ = if i ∈ S then -fourierCoeff f S else fourierCoeff f S := by
          rw [show (∑ y : Q n, f y * χ S (flip y i)) =
              ∑ y : Q n, (f y * χ S y) * (if i ∈ S then -1 else 1) by
                apply Finset.sum_congr rfl
                intro y _
                rw [χ_flip]
                ring]
          by_cases hi : i ∈ S <;> simp [hi, fourierCoeff]

/-- Unnormalised integer Parseval identity: `2^n · ⟨f,g⟩ = ⟨f̂,ĝ⟩`. -/
theorem parseval {n : ℕ} (f g : Q n → ℤ) :
    (2 : ℤ) ^ n * (∑ x, f x * g x) =
      ∑ S : Finset (Fin n), fourierCoeff f S * fourierCoeff g S := by
  classical
  calc
    (2 : ℤ) ^ n * (∑ x, f x * g x) =
        ∑ x : Q n, ((2 : ℤ) ^ n * f x) * g x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = ∑ x : Q n, (∑ S : Finset (Fin n), fourierCoeff f S * χ S x) * g x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [reconstruction]
    _ = ∑ S : Finset (Fin n), fourierCoeff f S * fourierCoeff g S := by
          rw [show (∑ x : Q n, (∑ S : Finset (Fin n), fourierCoeff f S * χ S x) * g x) =
              ∑ x : Q n, ∑ S : Finset (Fin n),
                fourierCoeff f S * (g x * χ S x) by
                  apply Finset.sum_congr rfl
                  intro x _
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro S _
                  ring]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro S _
          rw [← Finset.mul_sum]
          simp only [fourierCoeff]

/-- Quadratic form of the unnormalised integer Parseval identity. -/
theorem parseval_self {n : ℕ} (f : Q n → ℤ) :
    (2 : ℤ) ^ n * (∑ x, f x * f x) =
      ∑ S : Finset (Fin n), fourierCoeff f S * fourierCoeff f S :=
  parseval f f

lemma fourierCoeff_discreteDerivative {n : ℕ} (f : Q n → ℤ)
    (i : Fin n) (S : Finset (Fin n)) :
    fourierCoeff (fun x => f x - f (flip x i)) S =
      if i ∈ S then 2 * fourierCoeff f S else 0 := by
  classical
  rw [show fourierCoeff (fun x => f x - f (flip x i)) S =
      fourierCoeff f S - fourierCoeff (fun x => f (flip x i)) S by
        simp only [fourierCoeff]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring]
  rw [fourierCoeff_flip]
  by_cases hi : i ∈ S
  · simp [hi]
    ring
  · simp [hi]

/-- The energy of the discrete derivative is four times the spectral mass containing `i`. -/
theorem flip_energy {n : ℕ} (f : Q n → ℤ) (i : Fin n) :
    (2 : ℤ) ^ n *
        (∑ x, (f x - f (flip x i)) * (f x - f (flip x i))) =
      4 * ∑ S : Finset (Fin n),
        (if i ∈ S then fourierCoeff f S * fourierCoeff f S else 0) := by
  rw [parseval_self (fun x => f x - f (flip x i))]
  simp_rw [fourierCoeff_discreteDerivative]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hi : i ∈ S
  · simp [hi]
    ring
  · simp [hi]

/-- Integer number of vertices where flipping coordinate `i` changes the Boolean function. -/
def influence {n : ℕ} (F : Q n → Bool) (i : Fin n) : ℤ :=
  ∑ x, if F (flip x i) ≠ F x then (1 : ℤ) else 0

lemma ξ_sub_sq (a b : Bool) :
    (ξ a - ξ b) * (ξ a - ξ b) = if a ≠ b then (4 : ℤ) else 0 := by
  cases a <;> cases b <;> norm_num [ξ]

lemma signed_flip_energy {n : ℕ} (F : Q n → Bool) (i : Fin n) :
    ∑ x, (ξ (F x) - ξ (F (flip x i))) *
        (ξ (F x) - ξ (F (flip x i))) = 4 * influence F i := by
  simp_rw [ξ_sub_sq]
  rw [show (∑ x : Q n, if F x ≠ F (flip x i) then (4 : ℤ) else 0) =
      ∑ x : Q n, 4 * (if F (flip x i) ≠ F x then (1 : ℤ) else 0) by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : F (flip x i) = F x
        · simp [h]
        · have hsymm : F x ≠ F (flip x i) := Ne.symm h
          simp [h, hsymm]]
  rw [← Finset.mul_sum]
  rfl

/-- Integer identity between local influence and spectral mass containing the coordinate. -/
theorem influence_spectral_mass {n : ℕ} (F : Q n → Bool) (i : Fin n) :
    (2 : ℤ) ^ n * influence F i =
      ∑ S : Finset (Fin n),
        (if i ∈ S then
          fourierCoeff (fun x => ξ (F x)) S * fourierCoeff (fun x => ξ (F x)) S
        else 0) := by
  have h := flip_energy (fun x => ξ (F x)) i
  rw [signed_flip_energy] at h
  have h4 : (4 : ℤ) * ((2 : ℤ) ^ n * influence F i) =
      4 * ∑ S : Finset (Fin n),
        (if i ∈ S then
          fourierCoeff (fun x => ξ (F x)) S * fourierCoeff (fun x => ξ (F x)) S
        else 0) := by
    calc
      (4 : ℤ) * ((2 : ℤ) ^ n * influence F i) =
          (2 : ℤ) ^ n * (4 * influence F i) := by ring
      _ = 4 * ∑ S : Finset (Fin n),
          (if i ∈ S then
            fourierCoeff (fun x => ξ (F x)) S * fourierCoeff (fun x => ξ (F x)) S
          else 0) := h
  exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4

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
