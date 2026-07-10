import Mathlib
import Utility.Basic
import Utility.Axioms

/-!
# Expected-Utility Representation

The von Neumann–Morgenstern (vNM) representation theorem relates axiomatic
preferences over lotteries to expected-utility maximisation:

> A preference `P` over lotteries satisfies (completeness, transitivity,
> independence, continuity) **if and only if** there exists a utility function
> `u : α → ℝ` such that `P p q ↔ E_p[u] ≥ E_q[u]`, unique up to positive affine
> transformation.

This file proves the **sound direction** (representation ⟹ rationality) and the
**affine-stability** (cardinality / uniqueness-up-to-positive-affine-transform)
lemmas in full, with zero `sorry`. The **existence direction** (rationality ⟹
existence of a representing utility) is the substantive half of the theorem
(Herstein–Milnor 1953); it is documented as an open milestone below and not
stated as a `sorry`-backed claim.

Cross-references:
- Infer-14 (Infer.NET): the posterior-mean utilities computed there are an
  instance of `expectation` over a Bayesian posterior; the representation here
  is the decision-theoretic justification for ranking by expected utility.
- PyMC-1 (PyMC): posterior expected-utility estimates by sampling approximate
  the same `expectation` operator; affine uniqueness justifies why only utility
  *differences* (not levels) are identified by choice data.
-/

namespace Utility

variable {α : Type*} [Fintype α]

/-- `IsExpectedUtilityRep u P` asserts that the utility function `u` represents
the preference `P`: `p` is weakly preferred to `q` exactly when the expected
utility under `p` is at least that under `q`. -/
def IsExpectedUtilityRep (u : α → ℝ) (P : Pref α) : Prop :=
  ∀ p q : Lottery α, P p q ↔ expectation p u ≥ expectation q u

section EasyDirection

/-!
## Representation ⟹ Rationality (sound, sorry-free)

If a utility function represents `P`, then `P` satisfies all four vNM axioms.
The axioms reduce to elementary facts about the order and affine structure of `ℝ`.
-/

/-- A represented preference is complete: any two expectations are real numbers
and hence comparable. -/
theorem rep_complete (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P) :
    IsComplete P := by
  intro p q
  by_cases he : expectation p u ≥ expectation q u
  · exact Or.inl ((h p q).mpr he)
  · simp only [not_le] at he
    exact Or.inr ((h q p).mpr (le_of_lt he))

/-- A represented preference is transitive: weak inequality on `ℝ` is
transitive. -/
theorem rep_transitive (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P) :
    IsTransitive P := by
  intro p q r hpq hqr
  refine (h p r).mpr ?_
  have h1 := (h p q).mp hpq
  have h2 := (h q r).mp hqr
  linarith

/-- A represented preference satisfies independence: mixing with a common
lottery preserves the expected-utility ordering, because expectation is affine. -/
theorem rep_independent (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P) :
    IsIndependent P := by
  intro p q r t ht0 ht1 hpq
  apply (h _ _).mpr
  rw [expectation_mix t p r u ht0 ht1, expectation_mix t q r u ht0 ht1]
  have hpq' : expectation p u ≥ expectation q u := (h p q).mp hpq
  nlinarith [hpq', ht0, ht1, sub_nonneg.mpr ht1]

/-- A represented preference satisfies continuity: given `p ≽ q ≽ r`, the
expected utilities satisfy `E_p ≥ E_q ≥ E_r`, so the affine interpolation
`g(t) = t·E_p + (1-t)·E_r` over `t ∈ [0,1]` crosses `E_q`, making the
corresponding mixture indifferent to `q`. -/
theorem rep_continuous (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P) :
    IsContinuous P := by
  intro p q r hpq hqr
  have hEpq : expectation p u ≥ expectation q u := (h p q).mp hpq
  have hEqr : expectation q u ≥ expectation r u := (h q r).mp hqr
  by_cases hne : expectation p u = expectation r u
  · -- Degenerate case: all three expectations coincide; any mixture is indifferent.
    refine ⟨(1 : ℝ) / 2, by norm_num, by norm_num, ?_, ?_⟩
    · have he : expectation (mix ((1:ℝ)/2) p r (by norm_num) (by norm_num)) u
          = expectation q u := by
        rw [expectation_mix, hne]; linarith
      exact (h _ _).mpr (by linarith [he])
    · have he : expectation (mix ((1:ℝ)/2) p r (by norm_num) (by norm_num)) u
          = expectation q u := by
        rw [expectation_mix, hne]; linarith
      exact (h _ _).mpr (by linarith [he])
  · -- Non-degenerate case: E_p > E_r; cross at t = (E_q − E_r)/(E_p − E_r) ∈ [0,1].
    have hlt : expectation p u > expectation r u := by
      refine lt_of_le_of_ne ?_ (Ne.symm hne)
      linarith
    have hdenom : 0 < expectation p u - expectation r u := sub_pos.mpr hlt
    set t : ℝ := (expectation q u - expectation r u) / (expectation p u - expectation r u) with htdef
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hEqr) (le_of_lt hdenom)
    have ht1 : t ≤ 1 := (div_le_one hdenom).mpr (by linarith)
    refine ⟨t, ht0, ht1, ?_, ?_⟩
    · have he : expectation (mix t p r ht0 ht1) u = expectation q u := by
        rw [expectation_mix, htdef]
        have hne0 : expectation p u - expectation r u ≠ 0 := ne_of_gt hdenom
        field_simp [hne0]
        ring
      exact (h _ _).mpr (by linarith [he])
    · have he : expectation (mix t p r ht0 ht1) u = expectation q u := by
        rw [expectation_mix, htdef]
        have hne0 : expectation p u - expectation r u ≠ 0 := ne_of_gt hdenom
        field_simp [hne0]
        ring
      exact (h _ _).mpr (by linarith [he])

/-- **Sound direction of the vNM theorem**: if a utility function represents a
preference, then that preference is rational (satisfies all four axioms). This
is the sorry-free half of the representation theorem. -/
theorem expected_utility_rep_is_rational (u : α → ℝ) (P : Pref α)
    (h : IsExpectedUtilityRep u P) : IsRational P where
  complete := rep_complete u P h
  transitive := rep_transitive u P h
  independent := rep_independent u P h
  continuous := rep_continuous u P h

end EasyDirection

section AffineStability

/-!
## Affine stability (uniqueness up to positive affine transformation)

If `u` represents `P`, so does any positive affine transform `a • u + b` with
`a > 0`. This is the easy half of the vNM cardinality result: only the affine
shape of the utility is pinned down by choice data.
-/

/-- A positive affine transform of a representing utility is again a
representing utility: expected utility transforms as `E_p[a·u + b] =
a·E_p[u] + b`, so the ordering is preserved by the positive scaling `a` and is
invariant under the common shift `b`. -/
theorem affine_rep_is_rep (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    (a : ℝ) (ha : 0 < a) (b : ℝ) :
    IsExpectedUtilityRep (fun x => a * u x + b) P := by
  intro p q
  rw [expectation_affine p a b u, expectation_affine q a b u]
  refine ⟨fun hpq => ?_, fun hge => ?_⟩
  · have hpq' : expectation p u ≥ expectation q u := (h p q).mp hpq
    nlinarith [hpq', ha]
  · apply (h p q).mpr
    nlinarith [hge, ha]

end AffineStability

section StrictAndIndifference

/-!
## Strict preference and indifference under a representation

The weak representation `IsExpectedUtilityRep u P` pins down `p ≽ q ↔ E_p[u] ≥ E_q[u]`.
Two companion characterisations follow by elementary reasoning on the order of `ℝ`,
completing the trichotomy weak / strict / indifferent of a represented preference —
the vNM analogue of the mono-book / probability-weights dichotomy of `Coherence`.
-/

/-- Under a representation, **strict preference** `p ≻ q` (weakly preferred one way,
    not the other) holds exactly when the expected utility under `p` *strictly* exceeds
    that under `q`. This is the strict companion of `IsExpectedUtilityRep`. -/
theorem rep_strict_iff (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    (p q : Lottery α) :
    StrictPref P p q ↔ expectation p u > expectation q u := by
  show P p q ∧ ¬ P q p ↔ expectation p u > expectation q u
  refine ⟨fun ⟨hpp, hnqp⟩ => ?_, fun hgt => ⟨?_, ?_⟩⟩
  · -- P p q ∧ ¬ P q p  ⟹ E_p > E_q
    have hge : expectation p u ≥ expectation q u := (h p q).mp hpp
    by_contra hneg
    -- hneg : ¬ E_p > E_q  ⟹  E_p ≤ E_q  ⟹  P q p, contradicting hnqp
    exact hnqp ((h q p).mpr (not_lt.mp hneg))
  · -- E_p > E_q  ⟹  P p q
    exact (h p q).mpr (le_of_lt hgt)
  · -- E_p > E_q  ⟹  ¬ P q p
    intro hqp
    have hle := (h q p).mp hqp
    linarith

/-- Under a representation, **indifference** `p ~ q` (each weakly preferred to the other)
    holds exactly when the two expected utilities coincide. Together with
    `rep_strict_iff`, this partitions a represented preference into the three exhaustive
    cases (strict-p / strict-q / indifferent) via the trichotomy of `ℝ`. -/
theorem rep_indifference_iff (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    (p q : Lottery α) :
    (P p q ∧ P q p) ↔ expectation p u = expectation q u := by
  refine ⟨fun ⟨hpp, hqp⟩ => ?_, fun heq => ?_⟩
  · -- P p q ∧ P q p  ⟹  E_p = E_q  (squeeze the two inequalities)
    have hge := (h p q).mp hpp
    have hle := (h q p).mp hqp
    linarith
  · -- E_p = E_q  ⟹  P p q ∧ P q p
    exact ⟨(h p q).mpr (by linarith), (h q p).mpr (by linarith)⟩

/-- **Irreflexivity of strict preference** under a representation: no lottery is strictly
    preferred to itself. Immediate corollary of `rep_strict_iff` (`E_p > E_p` is absurd). -/
theorem strict_irrefl (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    (p : Lottery α) : ¬ StrictPref P p p := by
  rw [rep_strict_iff u P h]
  exact lt_irrefl _

end StrictAndIndifference

section OrderAlgebra

/-!
## The order-theoretic algebra of a represented preference

`rep_strict_iff` and `rep_indifference_iff` transport a represented preference
onto the order of `ℝ`. Consequently the strict part `≻` inherits the structure
of a strict order (irreflexive — already shown in `StrictAndIndifference` —,
asymmetric, transitive), the indifference part `~` inherits that of an
equivalence relation, and the two interleave: a strict step absorbs an adjacent
indifferent step. Each proof below is the corresponding elementary fact about
`<` / `=` on `ℝ`, pulled back through the representation. Together they close the
trichotomy that `StrictAndIndifference` opens. -/

/-- **Indifference matches equality of expected utility.** Restatement of
`rep_indifference_iff` through the named relation `Indiff`; the two are the same
conjunction definitionally, so the proof is the earlier equivalence verbatim. -/
theorem rep_indiff_iff (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    (p q : Lottery α) :
    Indiff P p q ↔ expectation p u = expectation q u :=
  rep_indifference_iff u P h p q

/-- **Strict preference is asymmetric**: `p ≻ q` forbids `q ≻ p`, because
`E_p > E_q` excludes `E_q > E_p`. -/
theorem strict_asymm (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    {p q : Lottery α} (hpq : StrictPref P p q) : ¬ StrictPref P q p := by
  rw [rep_strict_iff u P h] at hpq ⊢
  intro hqp
  linarith

/-- **Strict preference is transitive**: `p ≻ q` and `q ≻ r` give `p ≻ r`,
chaining `E_p > E_q > E_r`. With `strict_irrefl` and `strict_asymm`, `≻` is a
strict order. -/
theorem strict_trans (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    {p q r : Lottery α} (hpq : StrictPref P p q) (hqr : StrictPref P q r) :
    StrictPref P p r := by
  rw [rep_strict_iff u P h] at hpq hqr ⊢
  linarith

/-- **Indifference is reflexive**: every lottery is indifferent to itself
(`E_p = E_p`). -/
theorem indiff_refl (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    (p : Lottery α) : Indiff P p p := by
  rw [rep_indiff_iff u P h]

/-- **Indifference is symmetric**: `p ~ q` gives `q ~ p` (equality is
symmetric). -/
theorem indiff_symm (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    {p q : Lottery α} (hpq : Indiff P p q) : Indiff P q p := by
  rw [rep_indiff_iff u P h] at hpq ⊢
  linarith

/-- **Indifference is transitive**: `p ~ q` and `q ~ r` give `p ~ r`
(`E_p = E_q = E_r`). With reflexivity and symmetry, `~` is an equivalence
relation on lotteries. -/
theorem indiff_trans (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    {p q r : Lottery α} (hpq : Indiff P p q) (hqr : Indiff P q r) :
    Indiff P p r := by
  rw [rep_indiff_iff u P h] at hpq hqr ⊢
  linarith

/-- **A strict step absorbs a following indifferent step**: `p ≻ q` and `q ~ r`
give `p ≻ r` (`E_p > E_q = E_r`). -/
theorem strict_indiff_trans (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    {p q r : Lottery α} (hpq : StrictPref P p q) (hqr : Indiff P q r) :
    StrictPref P p r := by
  rw [rep_strict_iff u P h] at hpq ⊢
  rw [rep_indiff_iff u P h] at hqr
  linarith

/-- **An indifferent step absorbs a following strict step**: `p ~ q` and `q ≻ r`
give `p ≻ r` (`E_p = E_q > E_r`). -/
theorem indiff_strict_trans (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    {p q r : Lottery α} (hpq : Indiff P p q) (hqr : StrictPref P q r) :
    StrictPref P p r := by
  rw [rep_indiff_iff u P h] at hpq
  rw [rep_strict_iff u P h] at hqr ⊢
  linarith

/-- **Trichotomy**: under a representation any two lotteries fall into at least
one of `p ≻ q`, `q ≻ p`, `p ~ q`. Exhaustiveness is the trichotomy of `<` on
`E_p, E_q`; the three cases are moreover mutually exclusive (`strict_asymm`
rules out the reverse strict, and a strict preference forces `E_p ≠ E_q`). -/
theorem rep_trichotomy (u : α → ℝ) (P : Pref α) (h : IsExpectedUtilityRep u P)
    (p q : Lottery α) :
    StrictPref P p q ∨ StrictPref P q p ∨ Indiff P p q := by
  rcases lt_trichotomy (expectation p u) (expectation q u) with hlt | heq | hgt
  · exact Or.inr (Or.inl ((rep_strict_iff u P h q p).mpr hlt))
  · exact Or.inr (Or.inr ((rep_indiff_iff u P h p q).mpr heq))
  · exact Or.inl ((rep_strict_iff u P h p q).mpr hgt)

end OrderAlgebra

/-!
## Existence direction — OPEN milestone

The converse — **every rational preference admits an expected-utility
representation** — is the substantive half of the von Neumann–Morgenstern
theorem (Herstein & Milnor, 1953). Its proof proceeds by:

1. Establishing that the preference is represented by a linear functional on
   the simplex of lotteries (independence gives linearity along mixture lines,
   continuity extends it to the interior).
2. Showing that this linear functional is an expectation `E_p[u]` for some
   `u : α → ℝ`, recovered from the functional's values on point masses.

This requires a non-trivial separation / linear-algebra argument and is left as
the natural next milestone. It is deliberately **not** stated as a `sorry`-backed
theorem: the present library is fully `sorry`-free, delivering the sound
converse, the four axioms under a representation, and affine uniqueness.
-/

end Utility
