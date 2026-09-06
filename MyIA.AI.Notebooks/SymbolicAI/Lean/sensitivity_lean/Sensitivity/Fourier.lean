import Sensitivity.Hypercube
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Analyse de Fourier booléenne sur l'hypercube

Ce module définit les caractères de Walsh à valeurs entières, prouve leurs deux
relations d'orthogonalité et en déduit une formule de reconstruction sans division.
Il fournit aussi un certificat spectral fini pour la conjonction en dimension deux.
-/

namespace Sensitivity

noncomputable section

open Bool Finset Fintype

/-- Encodage signé d'une valeur booléenne. -/
def ξ (b : Bool) : ℤ :=
  if b then -1 else 1

@[simp] lemma ξ_false : ξ false = 1 := rfl
@[simp] lemma ξ_true : ξ true = -1 := rfl

@[simp] lemma ξ_mul_self (b : Bool) : ξ b * ξ b = 1 := by
  cases b <;> norm_num

lemma ξ_mul_eq (a b : Bool) :
    ξ a * ξ b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> norm_num

/-- Caractère de Walsh indexé par un sous-ensemble de coordonnées. -/
def χ {n : ℕ} (S : Finset (Fin n)) (x : Q n) : ℤ :=
  ∏ i, if i ∈ S then ξ (x i) else 1

lemma χ_eq_prod_subset {n : ℕ} (S : Finset (Fin n)) (x : Q n) :
    χ S x = ∏ i ∈ S, ξ (x i) := by
  classical
  simp [χ]

/-- Coefficient de Fourier booléen non normalisé. -/
def fourierCoeff {n : ℕ} (f : Q n → ℤ) (S : Finset (Fin n)) : ℤ :=
  ∑ x, f x * χ S x

/-- Deux caractères de Walsh distincts sont orthogonaux sur l'hypercube booléen. -/
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

/-- La somme sur tous les caractères de Walsh sépare deux sommets de l'hypercube. -/
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

/-- Reconstruction de Fourier sans division, multipliée par le cardinal de l'hypercube. -/
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

/-- Poids spectraux ternaires de la conjonction en dimension deux. -/
def weight (S : Finset (Fin 2)) : ℤ :=
  if S = ∅ then 1
  else if S = {0} then 1
  else if S = {1} then 1
  else -1

/-- Chaque poids du masque appartient à l'alphabet ternaire `{-1, 0, 1}`. -/
theorem weight_is_ternary (S : Finset (Fin 2)) :
    weight S = -1 ∨ weight S = 0 ∨ weight S = 1 := by
  decide +revert

/-- Le masque ternaire est exactement la moitié du spectre non normalisé de la conjonction signée. -/
theorem fourierCoeff_signedAnd (S : Finset (Fin 2)) :
    fourierCoeff (fun x : Q 2 => ξ (x 0 && x 1)) S = 2 * weight S := by
  decide +revert

/-- Score entier reconstruit à partir du masque ternaire de Walsh. -/
def score (x : Q 2) : ℤ :=
  ∑ S : Finset (Fin 2), weight S * χ S x

/-- Le certificat fini donne la table de vérité complète de la conjonction. -/
theorem score_and (x : Q 2) :
    score x = if x 0 && x 1 then (-2 : ℤ) else 2 := by
  decide +revert

/-- Portes booléennes utilisées par la composition certifiée. -/
def gateAnd (a b : Bool) : Bool := a && b

def gateNot (a : Bool) : Bool := !a

def gateNand (a b : Bool) : Bool := gateNot (gateAnd a b)

/-- La composition de portes calcule NAND. -/
theorem gateNand_eq (a b : Bool) : gateNand a b = !(a && b) := by
  rfl

/-- Le signe du certificat de Walsh coïncide avec la conjonction. -/
theorem score_sign_is_and (x : Q 2) :
    decide (score x ≤ -1) = gateAnd (x 0) (x 1) := by
  decide +revert

/-- Le signe complémentaire coïncide avec la composition NAND. -/
theorem score_sign_is_nand (x : Q 2) :
    decide (-1 < score x) = gateNand (x 0) (x 1) := by
  decide +revert

end WalshCertificate

end

end Sensitivity
