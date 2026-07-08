import Mathlib
import PacLearning.Data_en
import PacLearning.Sample_en
import PacLearning.Concentration_en
import PacLearning.SampleExpect_en
import PacLearning.UnionBound_en

set_option maxHeartbeats 4000000

/-!
# PacLearning.PacFiniteBound — sample complexity bound (PAC flagship)

Submodule of `PacLearning`: the **flagship theorem** `pac_finite_class_bound`
(sample complexity for a finite class, Valiant 1984). For a finite hypothesis
class `H` and a target concept `f`, if the sample size `n` exceeds
`(1/ε)·(ln|H| + ln(1/δ))`, then with probability `≥ 1 − δ` over `S ∼ D^n`,
**every** hypothesis consistent on `S` has true error `≤ ε`:

    n ≥ (1/ε)·(ln|H| + ln(1/δ))  ⟹
    ℙ_S [ ∃ hyp ∈ H, empError(hyp) = 0 ∧ ε < trueError(hyp) ] ≤ δ.

## Setting: realizable case (Valiant 1984, original form)

This is the canonical **realizable** bound (the learner returns a hypothesis
consistent with the sample, ERM-realizable setting). It combines three
ingredients, two of which are already proven in earlier bricks:

1. **i.i.d. independence factorization** (`sampleExpect_prod_coord`, brick 3/5)
   via the key lemma `sampleProb_consistent_le`: the probability that a
   hypothesis `hyp` (of true error `μ`) is consistent on the sample equals
   `∏_i E_D[𝟙{hyp=f}] = (1 − μ)^n` — the draws being i.i.d. by construction of
   the product measure `D^n`. This is the bridge between independence (brick 3/5)
   and concentration.
2. **Geometric bound** `one_sub_pow_le_exp`: `(1 − x)^n ≤ exp(−ε·n)` whenever
   `ε ≤ x ≤ 1` (via `log(1−x) ≤ −x`, lemma `Real.log_le_sub_one_of_pos`). Since
   `μ_h ≥ ε` for a "bad" hypothesis, we get `(1−μ_h)^n ≤ exp(−ε·n)`.
3. **Union bound** (`sampleProb_union_bound`, brick 3/3) over the finite class:
   `ℙ[∃ hyp, consistent ∧ μ_h > ε] ≤ ∑_hyp exp(−ε·n) = |H|·exp(−ε·n) ≤ δ`, the
   last inequality rewriting exactly to `n ≥ (1/ε)(ln|H| + ln(1/δ))`.

## OPEN — agnostic case (Hoeffding)

The **agnostic** bound `n ≥ (1/(2ε²))·(ln(2|H|/δ))` (Shalev-Shwartz–Ben-David,
*Understanding Machine Learning* §2.4) requires Hoeffding-for-Bernoulli
concentration `ℙ[|empError − trueError| > ε] ≤ 2·exp(−2nε²)`, itself blocked on
the general MGF analytic bound (brick 2b/5, `bernoulli_mgf_le` — convexity route
documented as OPEN in `BernoulliMGF.lean`). The present module delivers the
**realizable case** (which is the original `1/ε` bound of Valiant 1984, exactly
the one stated in the module docstring of `Data.lean`); the agnostic case will
follow once 2b/5 is closed.

Pedagogical **ℝ-weight style** (no `ℝ≥0∞` / `Measure`), consistent with `Data.lean`.
-/

namespace PacLearning_en

open Finset
-- NOTE: no `open scoped Classical` here. Reason: it enables `Classical.propDecidable`
-- globally, which would make the synthesis of the `Decidable` instance for the existential
-- predicate `∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp` of the flagship
-- prefer `Classical.decPred` over the explicit parameter `hDec` (→ non-defeq).
-- Without `open scoped Classical`, all `by_cases`/`if` of the module — which range over
-- *constructively* decidable Props (ℝ `=`, ℝ `<`, Bool `≠`, conjunctions, ∃ over Finset
-- via the `hDec` parameter) — synthesize exactly `hDec` for the ∃, without blowup of the
-- `decidableExistsAndFinsetCoe` enumeration (hDec takes priority over Finset synthesis).
variable {X : Type*} [Fintype X]
variable (D : Distribution X)

/-- **Characterization of consistency**: the empirical error is zero iff `hyp`
classifies **all** examples of `S` correctly. This is the bridge between the
numerical definition `empError = (∑ indicators)/n` and the boolean event
"consistent on `S`".

Proof: `empError = 0 ⟺ (∑ ind)/n = 0` then (n > 0) `⟺ ∑ ind = 0`
(`div_eq_zero_iff`: `a/b = 0 ↔ a = 0 ∨ b = 0`, and `n > 0` rules out `b = 0`)
`⟺ ∀ i, ind(S_i) = 0` (`sum_eq_zero_iff_of_nonneg`: a sum of terms `≥ 0` is zero
iff all its terms are — **contrapositive**, no lower bound needed)
`⟺ ∀ i, hyp(S_i) = f(S_i)`. -/
theorem empError_eq_zero_iff {n : ℕ} (f hyp : Hypothesis X) (S : Fin n → X) (hn : 0 < n) :
    empError f hyp S = 0 ↔ ∀ i : Fin n, hyp (S i) = f (S i) := by
  dsimp only [empError]
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnonneg : ∀ i, 0 ≤ (if hyp (S i) ≠ f (S i) then (1 : ℝ) else 0) := by
    intro i
    by_cases hsi : hyp (S i) ≠ f (S i) <;> simp [hsi]
  constructor
  · -- (→) each indicator is zero (zero sum of terms ≥ 0).
    intro h i
    have hsum0 : ∑ j, (if hyp (S j) ≠ f (S j) then (1 : ℝ) else 0) = 0 := by
      rcases (div_eq_zero_iff).mp h with h0 | hn0
      · exact h0
      · exact absurd hn0 (by exact_mod_cast (ne_of_gt hn))
    have hall : ∀ i, (if hyp (S i) ≠ f (S i) then (1 : ℝ) else 0) = 0 := by
      intro i
      exact (sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum0 i (mem_univ i)
    by_cases hsi : hyp (S i) = f (S i)
    · exact hsi
    · -- hsi : hyp(S_i) ≠ f(S_i): the indicator is 1, contradicting `hall` (= 0).
      exfalso
      have h1 : (if hyp (S i) ≠ f (S i) then (1 : ℝ) else 0) = 1 := if_pos hsi
      linarith [hall i]
  · -- (←) all correct ⟹ all indicators zero ⟹ zero sum ⟹ empError = 0.
    intro h
    have hsum0 : ∑ i, (if hyp (S i) ≠ f (S i) then (1 : ℝ) else 0) = 0 := by
      apply (sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mpr
      intro i _
      have hi : hyp (S i) = f (S i) := h i
      simp [hi]
    -- (∑ indicators)/n = 0 via ∑ = 0 (`a = 0` branch of `div_eq_zero_iff`).
    exact (div_eq_zero_iff).mpr (Or.inl hsum0)

/-- **Geometric → exponential bound**: for `ε ≤ x ≤ 1`, `(1 − x)^n ≤ exp(−ε·n)`.
Generic analytic lemma (not PAC-specific). Proof via the logarithm route:
`log(1 − x) ≤ (1 − x) − 1 = −x` (`Real.log_le_sub_one_of_pos`), hence
`log((1−x)^n) = n·log(1−x) ≤ −(x·n) ≤ −(ε·n)`, and `(1−x)^n = exp(log((1−x)^n))
≤ exp(−ε·n)` by monotonicity of `exp`. The case `x = 1` (`(1−x) = 0`) is handled
separately. -/
theorem one_sub_pow_le_exp (x : ℝ) (n : ℕ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ε : ℝ)
    (hxe : ε ≤ x) : (1 - x) ^ n ≤ Real.exp (-(ε * n)) := by
  have h1mx : 0 ≤ 1 - x := by linarith
  by_cases hz : 1 - x = 0
  · -- x = 1 : (1-x)^n = 0^n. n = 0 ⟹ 0^0 = 1 ≤ exp(0) = 1 ; n > 0 ⟹ 0 ≤ exp(−εn).
    have hx1' : x = 1 := by linarith
    subst hx1'
    by_cases hn : n = 0
    · simp [hn, Real.exp_zero]
    · have h0n : (1 - 1 : ℝ) ^ n = 0 := by
        have h11 : (1 - 1 : ℝ) = 0 := by norm_num
        rw [h11]
        exact zero_pow (by omega)
      rw [h0n]
      exact (le_of_lt (Real.exp_pos _))
  · have hpos : 0 < 1 - x := lt_of_le_of_ne h1mx (Ne.symm hz)
    have hpospow : 0 < (1 - x) ^ n := pow_pos hpos n
    have hlog : Real.log (1 - x) ≤ -x := by
      have := Real.log_le_sub_one_of_pos hpos
      linarith
    -- (1-x)^n = exp(n · log(1-x)).
    have heq : (1 - x) ^ n = Real.exp (n * Real.log (1 - x)) := by
      rw [← Real.exp_log hpospow, Real.log_pow]
    rw [heq]
    refine Real.exp_le_exp.mpr ?_
    -- n · log(1-x) ≤ -(x·n) (via log(1-x) ≤ -x), then -(x·n) ≤ -(ε·n) (via ε ≤ x).
    have hstep : (n : ℝ) * Real.log (1 - x) ≤ -(x * (n : ℝ)) := by
      calc (n : ℝ) * Real.log (1 - x)
          ≤ (n : ℝ) * (-x) := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (n := n))
        _ = -(x * (n : ℝ)) := by ring
    have hen : -(x * (n : ℝ)) ≤ -(ε * (n : ℝ)) := by
      have hle : ε * (n : ℝ) ≤ x * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hxe (Nat.cast_nonneg (n := n))
      linarith [hle]
    linarith [hstep, hen]

/-- **Consistency probability** of a hypothesis `hyp` on `S ∼ D^n`:
`ℙ_S[empError(hyp) = 0] ≤ (1 − trueError(hyp))^n`. This is the **pivot lemma** of
the realizable case: it turns the i.i.d. factorization (brick 3/5) into a concrete
bound.

Proof: the indicator `𝟙{empError=0}` coincides pointwise with the product of the
per-coordinate correct-classification indicators `∏_i cc(S_i)` (`cc = 𝟙{hyp=f}`) —
via `empError_eq_zero_iff` (a product of `{0,1}` values equals `1` iff all equal
`1`). We then move to `sampleExpect`: `E_S[∏_i cc(S_i)] = ∏_i E_D[cc]`
(i.i.d. factorization `sampleExpect_prod_coord`, brick 3/5), and `E_D[cc] =
1 − trueError` (the expectation of the complement of the error indicator, via
`expect_linear` + `trueError_eq_expect`). -/
theorem sampleProb_consistent_le {n : ℕ} (f hyp : Hypothesis X) (hn : 0 < n) :
    sampleProb D (fun S : Fin n → X => empError f hyp S = 0) ≤
      (1 - trueError D f hyp) ^ n := by
  -- (1) `𝟙{empError=0} = ∏_i cc(S_i)` pointwise, cc(x) = 𝟙{hyp x = f x}.
  have hind : ∀ S : Fin n → X,
      (if empError f hyp S = 0 then (1 : ℝ) else 0) =
        ∏ i : Fin n, (if hyp (S i) = f (S i) then (1 : ℝ) else 0) := by
    intro S
    by_cases hS : empError f hyp S = 0
    · -- All correct ⟹ ∏ cc(S_i) = 1 (each cc = 1).
      rw [if_pos hS]
      have hall := (empError_eq_zero_iff f hyp S hn).mp hS
      have hcc1 : ∀ i : Fin n, (if hyp (S i) = f (S i) then (1 : ℝ) else 0) = 1 :=
        fun i => if_pos (hall i)
      simp [hcc1]
    · -- At least one wrong ⟹ ∏ cc(S_i) = 0 (one factor cc = 0).
      rw [if_neg hS]
      have hnot : ¬ ∀ i : Fin n, hyp (S i) = f (S i) := by
        intro hall
        exact hS ((empError_eq_zero_iff f hyp S hn).mpr hall)
      obtain ⟨i₀, hi₀⟩ := not_forall.mp hnot
      have hprod : ∏ i : Fin n, (if hyp (S i) = f (S i) then (1 : ℝ) else 0) = 0 := by
        rw [Finset.prod_eq_zero_iff]
        exact ⟨i₀, mem_univ i₀, if_neg hi₀⟩
      rw [hprod]
  -- expect D cc = 1 − trueError (cc = 1 − error indicator).
  have hbase : expect D (fun x => if hyp x = f x then (1 : ℝ) else 0) = 1 - trueError D f hyp := by
    rw [show (fun x => (if hyp x = f x then (1 : ℝ) else 0)) =
          (fun x => (1 : ℝ) * ((fun _ : X => (1 : ℝ)) x) + (-(1 : ℝ)) *
            ((fun x => if hyp x ≠ f x then (1 : ℝ) else 0) x)) from
        by funext x; by_cases hx : hyp x = f x <;> simp [hx]]
    rw [expect_linear (1 : ℝ) (-1 : ℝ), expect_const (1 : ℝ),
        ← trueError_eq_expect f hyp]
    ring
  -- (2) Chain of EQUALITIES: sampleProb = sampleExpect(ind) = sampleExpect(∏ cc)
  --     = ∏ E_D[cc] = (1-trueError)^n (the indicator = the cc product, pointwise).
  have key : sampleProb D (fun S : Fin n → X => empError f hyp S = 0) =
      (1 - trueError D f hyp) ^ n := by
    calc sampleProb D (fun S : Fin n → X => empError f hyp S = 0)
        = sampleExpect D (fun S => (if empError f hyp S = 0 then (1 : ℝ) else 0)) :=
            sampleProb_eq_sampleExpect _
      _ = sampleExpect D (fun S => ∏ i : Fin n, (if hyp (S i) = f (S i) then (1 : ℝ) else 0)) := by
            simp only [hind]
      _ = ∏ _ : Fin n, expect D (fun x => if hyp x = f x then (1 : ℝ) else 0) :=
            sampleExpect_prod_coord (fun x => if hyp x = f x then (1 : ℝ) else 0)
      _ = (expect D (fun x => if hyp x = f x then (1 : ℝ) else 0)) ^ n := by
            rw [prod_const, Finset.card_univ, Fintype.card_fin]
      _ = (1 - trueError D f hyp) ^ n := by rw [hbase]
  exact key.le

/-! ## Shared decidable instance (defeq guarantee)

Two distinct `Classical.decPred _` literals are **non-defeq** because
`Classical.choice` is opaque (axiomatic): the `hDec` of `@sampleProb ...` in the
*statement* does not unify with the one passed to `_aux`. We therefore factor the
instance into a **single symbol** `pacDecidable` (`@[reducible]` to satisfy the
class-types linter), referenced identically on both sides → defeq guaranteed by
construction (the predicate being fixed by the signature of `pacDecidable`, both
occurrences unfold to the *same* term `Classical.decPred P`, defeq — unlike two
separate `_`). -/

@[reducible] noncomputable def pacDecidable {n : ℕ} (Hs : Finset (Hypothesis X)) (f : Hypothesis X)
    (ε : ℝ) (D : Distribution X) :
    DecidablePred (fun S : Fin n → X =>
      ∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) :=
  Classical.decPred _

/-! ## Flagship theorem — PAC sample complexity (realizable case)

Valiant's bound (1984): for a finite class `Hs`, a target concept `f`, and
`n ≥ (1/ε)·(ln|Hs| + ln(1/δ))`, the probability that there exists a hypothesis
**consistent** on the sample `S` but of true error `> ε` is bounded by `δ`.
Proof (3 ingredients):

1. **Per-hypothesis bound** (`sampleProb_consistent_le` + `one_sub_pow_le_exp`): for
   each "bad" `hyp` (`trueError > ε`), `ℙ[consistent ∧ bad] ≤ ℙ[consistent] ≤
   (1−μ)^n ≤ exp(−εn)` (i.i.d. via `sampleExpect_prod_coord`). If `hyp` is good, empty.
2. **Union bound** (Boole's inequality) at the `sampleExpect` level: pointwise
   `𝟙{∃ hyp ∈ Hs, consistent ∧ bad} ≤ ∑_hyp 𝟙{consistent ∧ bad}` (via
   `Finset.single_le_sum`), then monotonicity + Finset linearity ⟹ `ℙ[∃ bad consistent
   hyp] ≤ ∑_hyp ℙ[hyp] ≤ |Hs|·exp(−εn)`.
3. **Final algebra**: `|Hs|·exp(−εn) ≤ δ ⟺ ln|Hs| + ln(1/δ) ≤ εn ⟺ n ≥ (1/ε)(ln|Hs| +
   ln(1/δ))` (hypothesis `hm`), via `Real.exp_add` + `Real.exp_log`.

**Technical note** (`_aux`): this lemma takes the `DecidablePred` instance
**explicit** (parameter `hDec`), put in local scope via `haveI := hDec`. Required
because the default synthesis of the existential predicate `∃ hyp ∈ Hs, …` hits
`decidableExistsAndFinsetCoe` which **enumerates** the function class
`Hypothesis X = X → Bool` (~12.7M reductions, timeout). The annotation
`@ite ℝ (∃ hyp ∈ Hs, …) (hDec S)` forces the instance without synthesis.
The public wrapper `pac_finite_class_bound` (below) instantiates `hDec` via `pacDecidable`.
-/
theorem pac_finite_class_bound_aux {n : ℕ} (Hs : Finset (Hypothesis X)) (f : Hypothesis X)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hH : 0 < (Hs.card : ℝ)) (hn : 0 < n)
    (hm : (1 / ε) * (Real.log (Hs.card : ℝ) + Real.log (1 / δ)) ≤ n)
    (hDec : DecidablePred (fun S : Fin n → X =>
      ∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp)) :
    @sampleProb X _ D n (fun S : Fin n → X =>
      ∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) hDec ≤ δ := by
  haveI := hDec
  let P (hyp : Hypothesis X) (S : Fin n → X) : Prop :=
    empError f hyp S = 0 ∧ ε < trueError D f hyp
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  -- Step 1: per-hypothesis bound `ℙ[P hyp] ≤ exp(−εn)`.
  have hPhyp : ∀ hyp ∈ Hs, sampleProb D (P hyp) ≤ Real.exp (-(ε * n)) := by
    intro hyp hhyp
    by_cases hbad : ε < trueError D f hyp
    · -- `P hyp ⊆ {empError=0}` (monotonicity of probabilities for inclusion).
      have hsub : sampleProb D (P hyp) ≤ sampleProb D (fun S : Fin n → X => empError f hyp S = 0) := by
        rw [sampleProb_eq_sampleExpect, sampleProb_eq_sampleExpect]
        apply sampleExpect_mono
        intro S
        by_cases hS : empError f hyp S = 0
        · -- empError=0 ∧ hbad ⟹ P hyp S, both indicators = 1 ⟹ 1 ≤ 1.
          rw [if_pos ⟨hS, hbad⟩, if_pos hS]
        · -- empError≠0 ⟹ ind(E=0)=0 and P=False ⟹ ind(P)=0 ⟹ 0 ≤ 0.
          rw [if_neg (fun h => hS h.1), if_neg hS]
      calc sampleProb D (P hyp)
          ≤ sampleProb D (fun S : Fin n → X => empError f hyp S = 0) := hsub
        _ ≤ (1 - trueError D f hyp) ^ n := sampleProb_consistent_le D f hyp hn
        _ ≤ Real.exp (-(ε * n)) :=
            one_sub_pow_le_exp (trueError D f hyp) n
              (trueError_nonneg (D := D) (f := f) (h := hyp))
              (trueError_le_one (D := D) (f := f) (h := hyp)) ε (le_of_lt hbad)
    · -- `hyp` is good: `P hyp` is empty, probability `0`.
      have h0 : sampleProb D (P hyp) = 0 := by
        dsimp only [sampleProb]
        apply sum_eq_zero
        intro S _
        rw [if_neg (fun h => hbad h.2), mul_zero]
      rw [h0]
      exact (le_of_lt (Real.exp_pos _))
  -- Step 2: union bound over finite `Hs`, at the `sampleExpect` level (avoids the whnf
  -- blowup of default Decidable synthesis, which enumerates `Hypothesis X = X → Bool`
  -- via `decidableExistsAndFinsetCoe` — ~12.7M reductions). The `DecidablePred` instance
  -- for `∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp` is provided by the
  -- `hDec` parameter (put in local scope via `haveI := hDec`): every `if (∃ hyp ∈ Hs, ...)`
  -- then synthesizes `hDec` (without enumerating the function class). The union bound is
  -- proved pointwise `𝟙{∃ hyp ∈ Hs, P hyp S} ≤ ∑_hyp 𝟙{P hyp S}` (via
  -- `Finset.single_le_sum`), then lifted to `sampleExpect` (monotonicity + Finset
  -- linearity). This avoids `sampleProb_union_bound` (whose LHS `sampleProb D (∃ hyp
  -- ∈ Hs, ...)` would synthesize its Finset instance and be non-defeq with `hDec`).
  have hind_le : ∀ S : Fin n → X,
      @ite ℝ (∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) (hDec S) (1:ℝ) 0 ≤
        ∑ hyp ∈ Hs, (if empError f hyp S = 0 ∧ ε < trueError D f hyp then (1:ℝ) else 0) := by
    intro S
    -- `Classical.em` avoids `Decidable` synthesis (which would hit `decidableExist-
    -- sAndFinsetCoe` → enumeration of `Hypothesis X`). The instance is provided by `hDec`.
    rcases Classical.em (∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) with h | h
    · -- witness `hyp₀`: its indicator is `1`, and the others are `≥ 0`.
      obtain ⟨hyp₀, hhyp₀, hP₀⟩ := h
      have hge : ∀ hyp ∈ Hs, 0 ≤ (if empError f hyp S = 0 ∧ ε < trueError D f hyp then (1:ℝ) else 0) := by
        intro hyp _; by_cases hp : empError f hyp S = 0 ∧ ε < trueError D f hyp <;> simp [hp]
      calc @ite ℝ (∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) (hDec S) (1:ℝ) 0
          = 1 := if_pos ⟨hyp₀, hhyp₀, hP₀⟩
        _ = (if empError f hyp₀ S = 0 ∧ ε < trueError D f hyp₀ then 1 else 0) := (if_pos hP₀).symm
        _ ≤ ∑ hyp ∈ Hs, (if empError f hyp S = 0 ∧ ε < trueError D f hyp then (1:ℝ) else 0) :=
              Finset.single_le_sum hge hhyp₀
    · -- no witness: indicator(`∃`) = 0 ≤ sum (of terms `≥ 0`).
      simp only [if_neg h]
      exact Finset.sum_nonneg (fun hyp _ =>
        by by_cases hp : empError f hyp S = 0 ∧ ε < trueError D f hyp <;> simp [hp])
  calc @sampleProb X _ D n (fun S : Fin n → X =>
        ∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) hDec
      = sampleExpect D (fun S =>
          @ite ℝ (∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) (hDec S) (1:ℝ) 0) :=
          @sampleProb_eq_sampleExpect X _ D n
            (fun S : Fin n → X => ∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) hDec
    _ ≤ sampleExpect D (fun S =>
          ∑ hyp ∈ Hs, (if empError f hyp S = 0 ∧ ε < trueError D f hyp then (1:ℝ) else 0)) :=
          sampleExpect_mono hind_le
    _ = ∑ hyp ∈ Hs, sampleExpect D (fun S =>
          (if empError f hyp S = 0 ∧ ε < trueError D f hyp then (1:ℝ) else 0)) := by
        dsimp only [sampleExpect]
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ hyp ∈ Hs, sampleProb D (P hyp) := by
          refine Finset.sum_congr rfl (fun hyp _ => (sampleProb_eq_sampleExpect (P hyp)).symm)
    _ ≤ ∑ hyp ∈ Hs, Real.exp (-(ε * n)) := sum_le_sum (fun hyp hh => hPhyp hyp hh)
    _ = (Hs.card : ℝ) * Real.exp (-(ε * n)) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          -- `ring` omitted: `simp` already reduces `∑_hyp exp = ↑card · exp` to `rfl`.
    _ ≤ δ := by
        -- `|Hs|·exp(−εn) ≤ δ` from `n ≥ (1/ε)(ln|Hs| + ln(1/δ))`.
        -- (a) log|Hs| + log(1/δ) ≤ ε·n.
        have hL : Real.log (Hs.card : ℝ) + Real.log (1 / δ) ≤ ε * n := by
          have hm' : (Real.log (Hs.card : ℝ) + Real.log (1 / δ)) / ε ≤ n := by
            rw [show (Real.log (Hs.card : ℝ) + Real.log (1 / δ)) / ε =
                    (1 / ε) * (Real.log (Hs.card : ℝ) + Real.log (1 / δ)) from by ring]
            exact hm
          linarith [(div_le_iff₀ hε).mp hm']
        -- (b) exp(log|Hs| + log(1/δ)) ≤ exp(ε·n)  ⟹  |Hs| · (1/δ) ≤ exp(εn).
        have hexp := Real.exp_le_exp.mpr hL
        rw [Real.exp_add, Real.exp_log hH, Real.exp_log (one_div_pos.mpr hδ)] at hexp
        -- hexp : (Hs.card : ℝ) * (1/δ) ≤ exp(ε·n).
        -- (c) |Hs| ≤ δ · exp(εn) (multiply hexp by δ > 0).
        have hcard : (Hs.card : ℝ) ≤ δ * Real.exp (ε * n) := by
          calc (Hs.card : ℝ)
              = (Hs.card : ℝ) * ((1 / δ) * δ) := by
                  rw [div_mul_cancel₀ (1 : ℝ) (ne_of_gt hδ), mul_one]
            _ = ((Hs.card : ℝ) * (1 / δ)) * δ := by ring
            _ ≤ Real.exp (ε * n) * δ := mul_le_mul_of_nonneg_right hexp hδ.le
            _ = δ * Real.exp (ε * n) := by ring
        -- (d) |Hs| · exp(−εn) = |Hs| · exp(εn)⁻¹ ≤ (δ · exp(εn)) · exp(εn)⁻¹ = δ.
        rw [Real.exp_neg]
        calc (Hs.card : ℝ) * (Real.exp (ε * n))⁻¹
            ≤ (δ * Real.exp (ε * n)) * (Real.exp (ε * n))⁻¹ :=
                mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr (Real.exp_pos _).le)
          _ = δ := by
                rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.exp_pos _)), mul_one]

/-- **Flagship theorem — PAC sample complexity (realizable case, Valiant 1984)**:
public wrapper of the auxiliary lemma `pac_finite_class_bound_aux`, instantiated
with `pacDecidable` (classical decidable instance of the existence predicate over
finite `Hs`, factored into a single symbol to guarantee the statement↔call defeq).
See `pac_finite_class_bound_aux` for the proof body and the justification of the
explicit instance threading (workaround for the non-defeq of `Classical.choice`). -/
theorem pac_finite_class_bound {n : ℕ} (Hs : Finset (Hypothesis X)) (f : Hypothesis X)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hH : 0 < (Hs.card : ℝ)) (hn : 0 < n)
    (hm : (1 / ε) * (Real.log (Hs.card : ℝ) + Real.log (1 / δ)) ≤ n) :
    @sampleProb X _ D n (fun S : Fin n → X =>
      ∃ hyp ∈ Hs, empError f hyp S = 0 ∧ ε < trueError D f hyp) (pacDecidable Hs f ε D) ≤ δ :=
  pac_finite_class_bound_aux D Hs f ε δ hε hδ hH hn hm (pacDecidable Hs f ε D)

end PacLearning_en
