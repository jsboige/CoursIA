import Sensitivity.Fourier_en
/-!
Exponent three and a Walsh certificate in dimension three.

This module establishes the formal link between the Fourier degree of a Boolean
hypercube function, the influence of its coordinates and its spectrum: the
spectral support determines exactly the influential coordinates, the total
influence is the spectral mass weighted by the size of the indices, and a zero
spectral degree characterizes the constant functions. It finally extends the
finite spectral certificate from dimension two to dimension three: the signed
majority admits an exactly ternary Walsh mask there, and its spectral degree is
exactly three.
-/
namespace Sensitivity_en

noncomputable section

open Bool Finset Fintype

/-! ### Spectral support and degree -/
/--
Set of spectral indices with nonzero coefficient.
-/def fourierSupport {n : ℕ} (f : Q n → ℤ) : Finset (Finset (Fin n)) :=
  univ.filter (fun S => fourierCoeff f S ≠ 0)
/--
Membership in the spectral support: nonzero Fourier coefficient.
-/lemma fourierSupport_mem {n : ℕ} (f : Q n → ℤ) (S : Finset (Fin n)) :
    S ∈ fourierSupport f ↔ fourierCoeff f S ≠ 0 := by
  simp [fourierSupport]
/--
Spectral degree: largest size of a support index.
-/def spectralDegree {n : ℕ} (f : Q n → ℤ) : ℕ :=
  (fourierSupport f).sup (fun S => S.card)
/--
The size of a support index is bounded by the spectral degree.
-/lemma card_le_spectralDegree {n : ℕ} (f : Q n → ℤ) {S : Finset (Fin n)}
    (hS : fourierCoeff f S ≠ 0) : S.card ≤ spectralDegree f :=
  Finset.le_sup (f := fun S => S.card) ((fourierSupport_mem f S).mpr hS)
/--
The character of the empty index is one everywhere.
-/lemma χ_empty {n : ℕ} (x : Q n) : χ ∅ x = 1 := by
  simp [χ_eq_prod_subset]
/--
On a constant function, every coefficient at a nonempty index is zero.
-/theorem fourierCoeff_eq_zero_of_const {n : ℕ} (f : Q n → ℤ)
    (hconst : ∀ x y : Q n, f x = f y) {S : Finset (Fin n)}
    (hS : S ≠ ∅) : fourierCoeff f S = 0 := by
  have hsum : (∑ x : Q n, χ S x) = 0 := by
    have h := orthogonality S ∅
    calc (∑ x : Q n, χ S x) = ∑ x : Q n, χ S x * χ ∅ x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [χ_empty, mul_one]
      _ = if S = ∅ then (2 : ℤ) ^ n else 0 := h
      _ = 0 := if_neg hS
  calc fourierCoeff f S = ∑ x : Q n, f x * χ S x := rfl
    _ = ∑ x : Q n, f default * χ S x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hconst x default]
    _ = f default * (∑ x : Q n, χ S x) := by
        rw [Finset.mul_sum]
    _ = 0 := by rw [hsum, mul_zero]
/--
If every coefficient at a nonempty index is zero, the function is constant.
-/theorem constant_of_fourierCoeff_eq_zero {n : ℕ} (f : Q n → ℤ)
    (h : ∀ S : Finset (Fin n), S ≠ ∅ → fourierCoeff f S = 0)
    (x y : Q n) : f x = f y := by
  have key : ∀ z : Q n, (2 : ℤ) ^ n * f z = fourierCoeff f ∅ := by
    intro z
    rw [reconstruction,
      Finset.sum_eq_single (∅ : Finset (Fin n))
        (fun S _ hS => by rw [h S hS, zero_mul])
        (fun hmem => by exact absurd (Finset.mem_univ ∅) hmem)]
    rw [χ_empty, mul_one]
  exact mul_left_cancel₀ (pow_ne_zero n (by norm_num))
    ((key x).trans (key y).symm)
/--
A function is constant if and only if its spectral degree is zero.
-/theorem constant_iff_spectralDegree_zero {n : ℕ} (f : Q n → ℤ) :
    (∀ x y : Q n, f x = f y) ↔ spectralDegree f = 0 := by
  constructor
  · intro hconst
    refine le_antisymm ?_ (Nat.zero_le _)
    apply Finset.sup_le
    intro S hS
    have hSne : S = ∅ := by
      by_contra hne
      exact (fourierSupport_mem f S).mp hS
        (fourierCoeff_eq_zero_of_const f hconst hne)
    rw [hSne]
    simp
  · intro hdeg x y
    refine constant_of_fourierCoeff_eq_zero f (fun S hS => ?_) x y
    by_contra hc
    have hmem : S ∈ fourierSupport f := (fourierSupport_mem f S).mpr hc
    have hle : S.card ≤ spectralDegree f :=
      Finset.le_sup (f := fun S : Finset (Fin n) => S.card) hmem
    rw [hdeg] at hle
    exact hS (Finset.card_eq_zero.mp (Nat.le_zero.mp hle))

/-! ### Influence, sensitivity and spectrum -/
/--
Influential coordinates of a function: the union of its spectral support indices.
-/def influentialCoords {n : ℕ} (f : Q n → ℤ) : Finset (Fin n) :=
  (fourierSupport f).biUnion id
/--
A coordinate absent from the spectral support has no influence.
-/theorem influence_eq_zero_of_not_mem {n : ℕ} (F : Q n → Bool) {i : Fin n}
    (h : i ∉ influentialCoords (fun x => ξ (F x))) : influence F i = 0 := by
  have hsum : (∑ S : Finset (Fin n),
      (if i ∈ S then
        fourierCoeff (fun x => ξ (F x)) S * fourierCoeff (fun x => ξ (F x)) S
      else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro S _
    by_cases hiS : i ∈ S
    · have hS : fourierCoeff (fun x => ξ (F x)) S = 0 := by
        by_contra hc
        exact h (Finset.mem_biUnion.mpr
          ⟨S, (fourierSupport_mem _ S).mpr hc, hiS⟩)
      rw [if_pos hiS, hS, mul_zero]
    · rw [if_neg hiS]
  have hmass := influence_spectral_mass F i
  rw [hsum] at hmass
  rw [mul_eq_zero] at hmass
  exact hmass.resolve_left (pow_ne_zero n (by norm_num))
/--
Every coordinate of a support index is influential.
-/theorem influence_ne_zero_of_mem {n : ℕ} (F : Q n → Bool) {i : Fin n}
    {S : Finset (Fin n)} (hS : S ∈ fourierSupport (fun x => ξ (F x)))
    (hiS : i ∈ S) : influence F i ≠ 0 := by
  intro hzero
  have hmass := influence_spectral_mass F i
  rw [hzero, mul_zero] at hmass
  have hpos : 0 < (∑ S' : Finset (Fin n),
      (if i ∈ S' then
        fourierCoeff (fun x => ξ (F x)) S' * fourierCoeff (fun x => ξ (F x)) S'
      else 0)) := by
    apply Finset.sum_pos'
    · intro S' _
      by_cases h : i ∈ S' <;> simp [h, mul_self_nonneg]
    · exact ⟨S, Finset.mem_univ S, by
        rw [if_pos hiS]
        exact mul_self_pos.mpr ((fourierSupport_mem _ S).mp hS)⟩
  exact hpos.ne hmass
/--
The influence of a coordinate is zero if and only if it appears in no index of
the spectral support.
-/theorem influence_eq_zero_iff_not_mem {n : ℕ} (F : Q n → Bool) (i : Fin n) :
    influence F i = 0 ↔ i ∉ influentialCoords (fun x => ξ (F x)) := by
  constructor
  · intro hzero hmem
    obtain ⟨S, hS, hiS⟩ := Finset.mem_biUnion.mp hmem
    exact influence_ne_zero_of_mem F hS hiS hzero
  · exact influence_eq_zero_of_not_mem F
/--
The total influence is the spectral mass weighted by the size of the indices.
-/theorem total_influence_spectral_degree {n : ℕ} (F : Q n → Bool) :
    (2 : ℤ) ^ n * (∑ i, influence F i) =
      ∑ S : Finset (Fin n),
        (S.card : ℤ) *
          (fourierCoeff (fun x => ξ (F x)) S * fourierCoeff (fun x => ξ (F x)) S) := by
  have key : ∀ i : Fin n, (2 : ℤ) ^ n * influence F i =
      ∑ S : Finset (Fin n),
        (if i ∈ S then
          fourierCoeff (fun x => ξ (F x)) S * fourierCoeff (fun x => ξ (F x)) S
        else 0) :=
    fun i => influence_spectral_mass F i
  have hone : ∀ S : Finset (Fin n),
      (∑ i ∈ S,
          fourierCoeff (fun x => ξ (F x)) S * fourierCoeff (fun x => ξ (F x)) S)
        = (S.card : ℤ) *
          (fourierCoeff (fun x => ξ (F x)) S * fourierCoeff (fun x => ξ (F x)) S) := by
    intro S
    have hones : (S.card : ℤ) = ∑ i ∈ S, (1 : ℤ) := by
      exact_mod_cast Finset.card_eq_sum_ones S
    rw [hones, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact (one_mul _).symm
  calc (2 : ℤ) ^ n * (∑ i, influence F i)
      = ∑ i : Fin n, (2 : ℤ) ^ n * influence F i := by
        rw [Finset.mul_sum]
    _ = ∑ i : Fin n, ∑ S : Finset (Fin n),
          (if i ∈ S then
            fourierCoeff (fun x => ξ (F x)) S * fourierCoeff (fun x => ξ (F x)) S
          else 0) :=
        Finset.sum_congr rfl (fun i _ => key i)
    _ = ∑ S : Finset (Fin n), ∑ i : Fin n,
          (if i ∈ S then
            fourierCoeff (fun x => ξ (F x)) S * fourierCoeff (fun x => ξ (F x)) S
          else 0) :=
        Finset.sum_comm
    _ = ∑ S : Finset (Fin n),
          ∑ i ∈ (univ.filter (fun i => i ∈ S) : Finset (Fin n)),
            fourierCoeff (fun x => ξ (F x)) S * fourierCoeff (fun x => ξ (F x)) S := by
        apply Finset.sum_congr rfl
        intro S _
        rw [Finset.sum_filter]
    _ = ∑ S : Finset (Fin n),
          (S.card : ℤ) *
            (fourierCoeff (fun x => ξ (F x)) S * fourierCoeff (fun x => ξ (F x)) S) := by
        apply Finset.sum_congr rfl
        intro S _
        rw [show ((univ.filter (fun i => i ∈ S) : Finset (Fin n))) = S from
          Finset.ext fun i => by simp,
          hone S]
/--
The signed encoding is injective.
-/theorem ξ_injective : Function.Injective ξ := by
  decide
/--
A Boolean function is constant if and only if no coordinate is influential.
-/theorem constant_iff_all_influence_zero {n : ℕ} (F : Q n → Bool) :
    (∀ x y : Q n, F x = F y) ↔ ∀ i, influence F i = 0 := by
  constructor
  · intro hconst i
    refine influence_eq_zero_of_not_mem F fun hmem => ?_
    obtain ⟨S, hS, hiS⟩ := Finset.mem_biUnion.mp hmem
    have hne : S ≠ ∅ := fun h => absurd (h ▸ hiS) (by simp)
    exact (fourierSupport_mem _ S).mp hS
      (fourierCoeff_eq_zero_of_const _ (fun x y => by rw [hconst x y]) hne)
  · intro h x y
    refine ξ_injective ?_
    refine constant_of_fourierCoeff_eq_zero (fun x => ξ (F x))
      (fun S hS => ?_) x y
    by_contra hc
    obtain ⟨i, hi⟩ := (Finset.nonempty_iff_ne_empty).mpr hS
    exact (influence_ne_zero_of_mem F ((fourierSupport_mem _ S).mpr hc) hi) (h i)

/-! ### Walsh certificate in dimension three -/

namespace WalshCertificate3
/--
Three-input Boolean majority gate.
-/def gateMaj (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)
/--
Signed majority in dimension three.
-/def signedMaj3 (x : Q 3) : ℤ :=
  ξ (gateMaj (x 0) (x 1) (x 2))
/--
Ternary mask of the majority: plus one on singletons, minus one on the full
index.
-/def weight3 (S : Finset (Fin 3)) : ℤ :=
  if S.card = 1 then 1 else if S = univ then -1 else 0
/--
Every mask weight belongs to the ternary alphabet `{-1, 0, 1}`.
-/theorem weight3_is_ternary (S : Finset (Fin 3)) :
    weight3 S = -1 ∨ weight3 S = 0 ∨ weight3 S = 1 := by
  decide +revert
/--
The unnormalized spectrum of the signed majority is exactly four times the
ternary mask.
-/theorem fourierCoeff_signedMaj3 (S : Finset (Fin 3)) :
    fourierCoeff signedMaj3 S = 4 * weight3 S := by
  decide +revert
/--
Integer score reconstructed from the ternary Walsh mask.
-/def score3 (x : Q 3) : ℤ :=
  ∑ S : Finset (Fin 3), weight3 S * χ S x
/--
The finite certificate yields the complete truth table of the majority.
-/theorem score3_maj3 (x : Q 3) :
    score3 x = 2 * ξ (gateMaj (x 0) (x 1) (x 2)) := by
  decide +revert
/--
The sign of the Walsh certificate coincides with the majority.
-/theorem score3_sign_is_maj (x : Q 3) :
    decide (score3 x ≤ -1) = gateMaj (x 0) (x 1) (x 2) := by
  decide +revert
/--
The spectral support of the signed majority is exactly the nonzero mask.
-/theorem fourierSupport_iff_weight3 (S : Finset (Fin 3)) :
    S ∈ fourierSupport signedMaj3 ↔ weight3 S ≠ 0 := by
  rw [fourierSupport_mem, fourierCoeff_signedMaj3]
  constructor
  · intro h h0
    rw [h0, mul_zero] at h
    exact h (by norm_num)
  · exact mul_ne_zero (by norm_num)
/--
The signed majority has spectral degree exactly three.
-/theorem spectralDegree_signedMaj3 : spectralDegree signedMaj3 = 3 := by
  apply le_antisymm
  · rw [show spectralDegree signedMaj3 =
        (fourierSupport signedMaj3).sup (fun S => S.card) from rfl,
      Finset.sup_le_iff]
    intro S hS
    exact S.card_le_univ.trans_eq (by simp)
  · have h := card_le_spectralDegree signedMaj3
        (S := (univ : Finset (Fin 3))) (by
      rw [fourierCoeff_signedMaj3]
      decide)
    simpa using h
/--
The spectral degree of the signed conjunction in dimension two is maximal.
-/theorem spectralDegree_signedAnd2 :
    spectralDegree (fun x : Q 2 => ξ (x 0 && x 1)) = 2 := by
  apply le_antisymm
  · rw [show spectralDegree (fun x : Q 2 => ξ (x 0 && x 1)) =
        (fourierSupport (fun x : Q 2 => ξ (x 0 && x 1))).sup (fun S => S.card)
          from rfl,
      Finset.sup_le_iff]
    intro S hS
    exact S.card_le_univ.trans_eq (by simp)
  · have h := card_le_spectralDegree (fun x : Q 2 => ξ (x 0 && x 1))
        (S := (univ : Finset (Fin 2))) (by
      rw [WalshCertificate.fourierCoeff_signedAnd]
      decide)
    simpa using h

end WalshCertificate3

end

end Sensitivity_en
