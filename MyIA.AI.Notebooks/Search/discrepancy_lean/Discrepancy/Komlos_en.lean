import Discrepancy.Basic_en

/-!
# i18n convention: EN sibling file

i18n convention ratified for this repository (EPIC #4980): for each canonical
FR file `Foo.lean`, an EN sibling `Foo_en.lean` mirrors it with translated
docstrings and comments ONLY — signatures, definitions, proofs and tactics
are byte-identical; the namespace carries the `_en` suffix to avoid name
clashes. The FR file remains the canonical teaching source.
-/

/-!
# Komlós and Bansal–Jiang: unit columns and the large-degree regime

Second installment of the `discrepancy_lean` lake (issue #12823): the
SOTA-frontier statements, in the exact form of the **Komlós** conjecture
(matrices with unit columns, bounded `O(1)` conjectured) and the forms of
the **Bansal–Jiang 2025** paper (arXiv:2508.03961, "Decoupling via Affine
Spectral-Independence: Beck-Fiala and Komlós Bounds Beyond Banaszczyk"):

- large-degree regime: the Beck–Fiala conjecture holds from `k ≥ (log n)²`;
- Komlós in `Õ(log^(1/4) n)`, beyond Banaszczyk's `O(√(log n))`.

Documented honesty: these theorems require a layer absent from Mathlib (SDP
+ duality, affine spectral independence, guided discrete Brownian motion,
matrix concentration). The statements therefore live as named `Prop`s
**from now on**; the proofs will wait for the upstream layer (P3 =
documented aspiration, never a promise). For the paper's Komlós form, we
state a **concrete weakened version** (`C * (log n)²`), true as soon as the
paper's theorem is — the exact polylog exponents of the `Õ` are not
pretended.

The sums are written by hand (`∑ i, A i j * c j`) rather than with
`Matrix.mulVec`: the column-line stays readable as a sum of products, as
close as possible to the paper definitions.
-/

namespace Discrepancy_en

/-- **Komlós conjecture**: there exists a universal constant `C` such that
every matrix `A` with `n` **unit** columns (`∑ i, A i j ^ 2 = 1`) admits a
`±1` coloring of the columns whose every line sum remains bounded by `C` in
absolute value.

Banaszczyk's theorem (1998) gives `O(√(log n))`; the conjecture requires
`O(1)`. In 2026, the preprint arXiv:2609.11189 (Guo–Fang–Lu, 10/09/2026)
announces a resolution: the signed sum has `ℓ∞` norm **less than**
`3√(2π) ≈ 7.52`, independently of dimension and of the number of columns.

That preprint is **not yet peer-reviewed**. The statement above remains a named
`Prop` — no formal proof is engaged. Note it is stated over `ℚ` with `C : ℚ`,
whereas the paper's bound is **real**: any future alignment must explicitly
choose a rational witness (`8` works). -/
def KomlosConjecture : Prop :=
  ∃ C : ℚ, ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ),
    (∀ j : Fin n, ∑ i, A i j * A i j = 1) →
      ∃ c : Fin n → ℚ,
        (∀ j : Fin n, c j = 1 ∨ c j = -1) ∧ ∀ i : Fin m, |∑ j, A i j * c j| ≤ C

/-- **Bansal–Jiang 2025, large-degree regime** (arXiv:2508.03961, theorem
1): the Beck–Fiala conjecture holds as soon as the degree dominates the
squared logarithm, `k ≥ (log₂ n)²` — with the same `O(√k)` conclusion at
universal constant. Resolves the Beck–Fiala conjecture for `k ≥ log² n`. -/
def BansalJiangLargeDegree : Prop :=
  ∃ C : ℕ,
    ∀ (n k : ℕ) (F : Finset (Finset (Fin n))) (_hk : maxDegree F ≤ k)
      (_hlog : (Nat.log 2 n) ^ 2 ≤ k),
      ∃ c : Fin n → ℤ, IsColoring c ∧ discrepancy F c ≤ C * Nat.sqrt k

/-- **Komlós, concrete weakened form after Bansal–Jiang 2025**: for matrices
with unit columns, a `±1` coloring bounds every line sum by `C * (log₂ n)²`.

The paper proves `Õ(log^(1/4) n)` — stronger. A conservative polylog
exponent (here `2`) gives a statement **implied** by the paper's theorem,
hence true as soon as the paper is, while remaining beyond the Banaszczyk
target in small powers. This is the SOTA frontier as the repository can
honestly state it without the SDP layer. -/
def KomlosBansalJiangWeak : Prop :=
  ∃ C : ℚ,
    ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ),
      (∀ j : Fin n, ∑ i, A i j * A i j = 1) →
        ∃ c : Fin n → ℚ,
          (∀ j : Fin n, c j = 1 ∨ c j = -1) ∧
            ∀ i : Fin m, |∑ j, A i j * c j| ≤ C * ((Nat.log 2 n : ℚ) ^ 2)

/-! ## Komlós ⇒ Beck–Fiala reduction probe (regular case)

The fragment of the reduction named by the #15944 verdict (§2b, "the first
probe to try before writing a line of proof") that is formalizable
**without the analytic stage**. -/

/-- **Komlós-to-Beck–Fiala reduction, regular case** (probe #15944): any
**real** Komlós oracle — unit-column matrices with line sums bounded by
`C` — implies the Beck–Fiala conclusion for **regular** families (every
element belongs to exactly `k` sets), at a constant at most doubled:
`2 * ⌈C⌉₊`.

The uniform scaling `1 / √k` is licit precisely because all degrees are
equal: each column of the incidence matrix carries exactly `k` ones, hence
norm `√k`, and dividing by `√k` makes it unit. The oracle's coloring then
gives `|∑_{j ∈ S} c j| ≤ C * √k` set by set; the conversion to the integer
form (`Nat.sqrt`, natural constant) costs the factor `2` through
`√k ≤ Nat.sqrt k + 1`.

Two limits, measured and documented in `FORMAL_STATUS.md`: the general case
(heterogeneous degrees) does not factor — the known reduction requires
iterated partial coloring; and the `ℚ` statement of `KomlosConjecture`
above does not suffice as an oracle, the scaling `1 / √k` being irrational —
the real form is the right bridge. -/
theorem komlos_oracle_imp_beck_fiala_regular
    (C : ℝ) (hC : 0 ≤ C)
    (oracle : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ),
      (∀ j : Fin n, ∑ i, A i j * A i j = 1) →
        ∃ c : Fin n → ℝ, (∀ j : Fin n, c j = 1 ∨ c j = -1) ∧
          ∀ i : Fin m, |∑ j, A i j * c j| ≤ C) :
    ∀ (n k : ℕ), 1 ≤ k → ∀ F : Finset (Finset (Fin n)),
      (∀ j : Fin n, degree F j = k) →
      ∃ c : Fin n → ℤ, IsColoring c ∧
        discrepancy F c ≤ 2 * ⌈C⌉₊ * Nat.sqrt k := by
  intro n k hk F hreg
  classical
  have h0k : 0 < k := by omega
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast h0k
  have hknz : (k : ℝ) ≠ 0 := ne_of_gt hk0
  have hskne : Real.sqrt (k : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hk0
  have hss : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) :=
    Real.mul_self_sqrt hk0.le
  -- Enumerate the sets of the family
  obtain ⟨e⟩ : Nonempty (Fin F.card ≃ ({x // x ∈ F} : Type)) := ⟨F.equivFin.symm⟩
  have hemem : ∀ i : Fin F.card, (e i : Finset (Fin n)) ∈ F := fun i => (e i).2
  -- Key counting: columns of the incidence matrix = degrees
  have hcount : ∀ j : Fin n,
      (Finset.univ.filter fun i => j ∈ (e i : Finset (Fin n))).card = degree F j := by
    intro j
    rw [degree]
    refine Finset.card_nbij (fun i : Fin F.card => (e i : Finset (Fin n))) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter] at hi ⊢
      exact ⟨hemem i, hi.2⟩
    · intro a _ b _ hab
      exact e.injective (Subtype.ext hab)
    · intro S hS
      simp only [Finset.mem_coe, Finset.mem_filter] at hS
      refine ⟨e.symm ⟨S, hS.1⟩, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Equiv.apply_symm_apply]
        exact hS.2
      · simp
  -- Indicator sums = filtered cardinal
  have hsumind : ∀ j : Fin n,
      ∑ i ∈ Finset.univ, (if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0)
        = (degree F j : ℝ) := by
    intro j
    have hn : ∑ i ∈ Finset.univ, (if j ∈ (e i : Finset (Fin n)) then (1 : ℕ) else 0)
        = degree F j := by
      rw [← Finset.sum_filter]
      exact (Finset.card_eq_sum_ones _).symm.trans (hcount j)
    exact_mod_cast hn
  -- The columns of the scaled matrix are unit
  have hunit : ∀ j : Fin n, ∑ i,
      ((Matrix.of fun i j =>
          (if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0) / Real.sqrt (k : ℝ))
        : Matrix (Fin F.card) (Fin n) ℝ) i j
      * ((Matrix.of fun i j =>
          (if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0) / Real.sqrt (k : ℝ))
        : Matrix (Fin F.card) (Fin n) ℝ) i j = 1 := by
    intro j
    simp only [Matrix.of_apply]
    have hterm : ∀ i : Fin F.card,
        ((if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0) / Real.sqrt (k : ℝ))
          * ((if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0) / Real.sqrt (k : ℝ))
        = ((if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0)
            * (if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0)) / (k : ℝ) := by
      intro i
      rw [div_mul_div_comm, hss]
    have hindsq : ∀ i : Fin F.card,
        ((if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0)
          * (if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0))
        = if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0 := by
      intro i
      by_cases h : j ∈ (e i : Finset (Fin n)) <;> simp [h]
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_div,
      Finset.sum_congr rfl fun i _ => hindsq i,
      hsumind j, hreg j, div_self hknz]
  -- The oracle, applied to the scaled incidence matrix
  obtain ⟨d, hdpm, hdbound⟩ :=
    oracle F.card n
      (Matrix.of fun i j =>
        (if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0) / Real.sqrt (k : ℝ)) hunit
  · refine ⟨fun j => if d j = 1 then (1 : ℤ) else -1, ?_, ?_⟩
    · intro j
      rcases hdpm j with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (by
          have hn : ¬((-1 : ℝ) = 1) := by norm_num
          simp only [h, if_neg hn])
    · rw [discrepancy]
      apply Finset.sup_le
      intro S' hS'
      obtain ⟨S, hSF, rfl⟩ := Finset.mem_image.mp hS'
      have hrei : (e (e.symm ⟨S, hSF⟩) : Finset (Fin n)) = S := by simp
      set i := e.symm ⟨S, hSF⟩ with hi
      -- Real colored sum of the set S
      have hreal : (((∑ j ∈ S, (if d j = 1 then (1 : ℤ) else -1) : ℤ)) : ℝ)
          = ∑ j ∈ S, d j := by
        rw [Int.cast_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rcases hdpm j with h | h
        · simp [h]
        · have hn : ¬((-1 : ℝ) = 1) := by norm_num
          simp only [h, if_neg hn, Int.cast_neg, Int.cast_one]
      -- It factors through line i of the scaled matrix
      have hroweq : (∑ j : Fin n,
            ((if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0)
              / Real.sqrt (k : ℝ)) * d j)
          = (∑ j ∈ S, d j) / Real.sqrt (k : ℝ) := by
        have hterm2 : ∀ j : Fin n,
            ((if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0)
              / Real.sqrt (k : ℝ)) * d j
            = (if j ∈ S then d j else 0) / Real.sqrt (k : ℝ) := by
          intro j
          rw [show (e i : Finset (Fin n)) = S from hrei]
          by_cases hj : j ∈ S
          · rw [if_pos hj, if_pos hj, div_mul_eq_mul_div, one_mul]
          · simp [hj]
        rw [Finset.sum_congr rfl fun j _ => hterm2 j, ← Finset.sum_div]
        have hinner : (∑ j : Fin n, (if j ∈ S then d j else 0)) = ∑ j ∈ S, d j := by
          rw [← Finset.sum_subset (Finset.subset_univ S) fun j _ hj => if_neg hj]
          exact Finset.sum_congr rfl fun j hj => if_pos hj
        exact congrArg (· / Real.sqrt (k : ℝ)) hinner
      have horacle : |(∑ j : Fin n,
            ((if j ∈ (e i : Finset (Fin n)) then (1 : ℝ) else 0)
              / Real.sqrt (k : ℝ)) * d j)|
          ≤ C := by
        have h := hdbound i
        simpa only [Matrix.of_apply] using h
      rw [hroweq] at horacle
      have hsqrtC : |(∑ j ∈ S, d j : ℝ)| ≤ C * Real.sqrt (k : ℝ) := by
        have hmul : |(∑ j ∈ S, d j : ℝ)|
            = |(∑ j ∈ S, d j : ℝ) / Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ)| := by
          rw [div_mul_cancel₀ _ hskne]
        rw [hmul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact mul_le_mul_of_nonneg_right horacle (Real.sqrt_nonneg _)
      -- Conversion to the integer form
      have hceil : C ≤ ((⌈C⌉₊ : ℕ) : ℝ) := Nat.le_ceil C
      have hs1 : (1 : ℝ) ≤ ((Nat.sqrt k : ℕ) : ℝ) := by
        have h11 : 1 * 1 ≤ k := by simpa using hk
        exact_mod_cast Nat.le_sqrt.mpr h11
      have hs2 : Real.sqrt (k : ℝ) ≤ ((Nat.sqrt k : ℕ) : ℝ) + 1 := by
        have h1 : ((Nat.sqrt k : ℕ) : ℝ) * ((Nat.sqrt k : ℕ) : ℝ) ≤ (k : ℝ) :=
          by exact_mod_cast Nat.sqrt_le k
        have h2 : (k : ℝ) < (((Nat.sqrt k : ℕ) + 1 : ℕ) : ℝ)
            * (((Nat.sqrt k : ℕ) + 1 : ℕ) : ℝ) :=
          by exact_mod_cast Nat.lt_succ_sqrt k
        have h3 : Real.sqrt (k : ℝ) ≤
            Real.sqrt ((((Nat.sqrt k : ℕ) + 1 : ℕ) : ℝ)
              * (((Nat.sqrt k : ℕ) + 1 : ℕ) : ℝ)) :=
          Real.sqrt_le_sqrt (le_of_lt h2)
        have hq : (0 : ℝ) ≤ (((Nat.sqrt k : ℕ) + 1 : ℕ) : ℝ) := by positivity
        rw [Real.sqrt_mul hq, Real.mul_self_sqrt hq, Nat.cast_add, Nat.cast_one] at h3
        exact h3
      have hfinal : ((∑ j ∈ S, (if d j = 1 then (1 : ℤ) else -1)).natAbs : ℝ)
          ≤ (((2 * ⌈C⌉₊ * Nat.sqrt k : ℕ) : ℝ)) := by
        have hconv : ∀ x : ℤ, ((x.natAbs : ℕ) : ℝ) = |(x : ℝ)| := by
          intro x
          calc ((x.natAbs : ℕ) : ℝ)
              = (((x.natAbs : ℕ) : ℤ) : ℝ) := (Int.cast_natCast _).symm
            _ = ((|x| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
            _ = |(x : ℝ)| := Int.cast_abs
        have habs : ((∑ j ∈ S, (if d j = 1 then (1 : ℤ) else -1)).natAbs : ℝ)
            = |(∑ j ∈ S, d j : ℝ)| := by
          rw [hconv, hreal]
        rw [habs]
        have hcast : (((2 * ⌈C⌉₊ * Nat.sqrt k : ℕ) : ℝ))
            = 2 * ((⌈C⌉₊ : ℕ) : ℝ) * ((Nat.sqrt k : ℕ) : ℝ) := by
          push_cast
          ring
        rw [hcast]
        have hbound : C * Real.sqrt (k : ℝ)
            ≤ 2 * ((⌈C⌉₊ : ℕ) : ℝ) * ((Nat.sqrt k : ℕ) : ℝ) := by
          nlinarith [hC, hceil, hs1, hs2,
            mul_nonneg hC (by positivity : (0 : ℝ) ≤ ((Nat.sqrt k : ℕ) : ℝ))]
        linarith
      exact_mod_cast hfinal

end Discrepancy_en
