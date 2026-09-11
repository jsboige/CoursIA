import Mathlib.Tactic

import RepeatedGames.Stage
import RepeatedGames.Discounting_en
import RepeatedGames.GrimTrigger_en

/-!
  Folk Theorem (STRETCH) — EN sibling
  ===================================

  English mirror of `RepeatedGames/Folk.lean` (FR-first canonical).
  Convention i18n Lean ratifiée par ai-01 (2026-07-04, #4980 comment-4881909354) :
  distinct `.lean` files FR + EN siblings in the same lake, both compile.
  Drift-CI detectable: non-docstring content byte-identical between siblings.

  Note méthodologique : traduction manuelle du FR canonique (pas de source
  EN historique pré-Option A à recover, fichier FR-first depuis origin).

  Namespace sibling : `RepeatedGames_en` (the FR canonical stays
  `RepeatedGames`). Shared types `PrisonersDilemma`, `PDAction` (defined in
  `Stage.lean` under `namespace RepeatedGames`) are re-exposed via
  `open RepeatedGames` so the EN sibling resolves them as FR `GrimTrigger_en`
  does. Field projections `g.P`/`g.R`/`g.S`/`g.T` are structure-field access
  (not namespace dot-notation), hence safe under the open.

  See #4980. Part of #4208 (axe E).
-/

/-!
  Repeated Games - Folk Theorem (STRETCH)
  ========================================

  The Folk theorem (Folk 1950s, formally Fudenberg–Maskin 1986, see also
  Aumann–Shapley 1994 for the continuous-time analogue) states, in its
  discounted payoff version:

    Every feasible payoff profile that is strictly individually rational can
    be sustained as a subgame-perfect Nash equilibrium in the limit as the
  discount factor δ → 1.

  This is a STRETCH module, optional per Issue #4880 ("Folk.lean — minimal
  version of the Folk theorem... If scaffolded, declare it explicitly as
  stretch with its sorries counted — 0-sorry is required only on the
  flagship theorem").

  The proof requires:
  - The set of feasible payoffs is a polytope (geometric fact over n-stage
    games);
  - For each target feasible point strictly inside the individual-rational
    polytope, construct a strategy profile that alternates between the
    target joint action and a punishment phase;
  - As δ → 1, the weight on the punishment phase vanishes, so the discounted
    average converges to the target payoff.

  These proofs use polytope topology, extreme-point arguments, and
  minmax-constrained optimization — substantially harder than GrimTrigger.
  A single theorem carries a `sorry`, the genuine STRETCH
  `folk_theorem_discounted`; the prover BG harness will attempt it in later
  iterations but it is flagged as low-priority. Everything else in the module
  is fully proven, including the concrete counterexample refutation of the
  unnormalized statement (`folk_theorem_discounted_unnormalized_refuted`,
  #15655).

  Type-forced definitions (lesson Lidman L39, PR #4899): `IndividuallyRational`
  is bounded by `g.P` and `Feasible` is a convex constraint on the four joint
  actions, **so correctness is forced by the type system, not by any cited
  numerical data** (no KnotInfo-style tables, no source labels). The `sorry`
  on `folk_theorem_discounted` is the genuine hard direction (Fudenberg–Maskin
  polytope topology, OUT of scope of the GrimTrigger sprint).

  Normalized convention (#15655): the conclusion of `folk_theorem_discounted`
  carries the factor `(1 - δ)` on each payoff equation — the geometric series
  `Σ' δⁿ = 1/(1-δ)` gives `(1-δ)·V` unit mass, the stage-payoff weighted
  average. Without this factor the statement would be FALSE even inside the
  convergent window `0 ≤ δ < 1`: exactly what
  `folk_theorem_discounted_unnormalized_refuted` establishes on the canonical
  PD `(3, 2, 1, 0)` with target `(2, 2)`.
-/

namespace RepeatedGames_en

open RepeatedGames


/-- Individual rationality: a payoff vector `u` is individually rational if
    each coordinate exceeds the player's minmax payoff (the worst a player
    can be forced to by the others). For a 2-player PD this is just `g.P`
    (the row player can be made to earn `P` if the column always defects).
    Type-forced via `≥ g.P` (no cited constants). -/
def IndividuallyRational (g : PrisonersDilemma) (u_row u_col : ℝ) : Prop :=
  u_row ≥ g.P ∧ u_col ≥ g.P

/-- Feasibility: a payoff vector is achievable as the expected payoff of
    some distribution over joint actions. In a 2x2 PD the feasible set is the
    convex hull of the four payoff profiles `(R, R), (S, T), (T, S), (P, P)`,
    characterized by non-negative weights summing to one. Type-forced: the
    formulas `g.R`, `g.S`, `g.T`, `g.P` are projections of the `PrisonersDilemma`
    structure, not external numerical data. -/
def Feasible (g : PrisonersDilemma) (u_row u_col : ℝ) : Prop :=
  ∃ pCC pCD pDC pDD : ℝ,  -- probability weights summing to 1
    pCC + pCD + pDC + pDD = 1 ∧
    pCC ≥ 0 ∧ pCD ≥ 0 ∧ pDC ≥ 0 ∧ pDD ≥ 0 ∧
    u_row = pCC * g.R + pCD * g.S + pDC * g.T + pDD * g.P ∧
    u_col = pCC * g.R + pCD * g.T + pDC * g.S + pDD * g.P

/-- Convexity of the feasible set (#14990): any convex combination of two
    feasible payoff vectors is feasible. First brick of the Folk theorem —
    the Fudenberg–Maskin construction interpolates between the target joint
    action and a punishment phase, so it requires the set of realizable
    payoffs to be stable under barycentres. Direct proof on the `Feasible`
    existential (no Mathlib `convexHull`): the witness weights combine as
    `lam * p + (1 - lam) * q`, which stays non-negative (product of
    non-negatives) and sums to one (affine combination of the two unit
    sums). -/
theorem feasible_convex (g : PrisonersDilemma) (lam : ℝ)
    (u1_row u1_col u2_row u2_col : ℝ)
    (h1 : Feasible g u1_row u1_col) (h2 : Feasible g u2_row u2_col)
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    Feasible g (lam * u1_row + (1 - lam) * u2_row)
                (lam * u1_col + (1 - lam) * u2_col) := by
  obtain ⟨pCC1, pCD1, pDC1, pDD1, hs1, ha1, ha2, ha3, ha4, hr1, hc1⟩ := h1
  obtain ⟨pCC2, pCD2, pDC2, pDD2, hs2, hb1, hb2, hb3, hb4, hr2, hc2⟩ := h2
  have h1l : 0 ≤ 1 - lam := by nlinarith
  refine ⟨lam * pCC1 + (1 - lam) * pCC2, lam * pCD1 + (1 - lam) * pCD2,
    lam * pDC1 + (1 - lam) * pDC2, lam * pDD1 + (1 - lam) * pDD2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination lam * hs1 + (1 - lam) * hs2
  · exact add_nonneg (mul_nonneg hlam ha1) (mul_nonneg h1l hb1)
  · exact add_nonneg (mul_nonneg hlam ha2) (mul_nonneg h1l hb2)
  · exact add_nonneg (mul_nonneg hlam ha3) (mul_nonneg h1l hb3)
  · exact add_nonneg (mul_nonneg hlam ha4) (mul_nonneg h1l hb4)
  · linear_combination lam * hr1 + (1 - lam) * hr2
  · linear_combination lam * hc1 + (1 - lam) * hc2

/-- Discounted payoff of the reference (row) player under a trajectory of
    joint actions `a` and discount factor `δ`. Generalizes `coopValue` /
    `deviateValue` (stationary special cases) to an arbitrary trajectory:
    `Σ' n, δⁿ · stagePayoff g (a n).1 (a n).2`. The column player's payoff
    under the same trajectory is obtained by swapping the joint-action
    components (see `folk_theorem_discounted`). -/
noncomputable def discountedPayoff (g : PrisonersDilemma) (δ : ℝ)
    (a : ℕ → PDAction × PDAction) : ℝ :=
  ∑' n : ℕ, δ^n * stagePayoff g (a n).1 (a n).2

/-- The DISCOUNTED Folk theorem (Fudenberg–Maskin 1986, simplified for 2x2),
    in the NORMALIZED convention (#15655):

      For every strictly individually rational feasible payoff
      `u = (u_row, u_col)`, there exists δ* < 1 such that for all δ ∈ [δ*, 1) the
      vector `u` is realized as the discounted average of a trajectory of
      joint actions: `(1 - δ) · Σ' δⁿ · payoffₙ = u`.

    The factor `1 - δ` is not decorative: `Σ' δⁿ = 1/(1-δ)` (lemma
    `geom_sum`), so `(1 - δ) · V` is the stage-payoff weighted average — the
    only convention under which the statement is true. The UNNORMALIZED
    version (`V = u` without the factor) is FALSE even in `0 ≤ δ < 1`,
    refuted by the fully proven counterexample
    `folk_theorem_discounted_unnormalized_refuted` below (canonical PD
    `⟨3, 2, 1, 0⟩`, target `(2, 2)`).

    The conclusion is a **real equation** (`(1 - d) * discountedPayoff … =
    u_row ∧ … = u_col`), not `True`: the `sorry` thus carries the genuine
    debt (existence of a trajectory realizing the target vector — the
    Fudenberg–Maskin construction alternating target action / punishment
    phase, using convexity of the feasible-payoff polytope). Do NOT close on
    `True`: with a trivial conclusion the `sorry` would yield a "−1" with no
    mathematics (lesson #10188). The deeper layer — resistance to one-shot
    unilateral deviation (sustainment as SPNE) — is the full
    Fudenberg–Maskin wall, out of scope of this grain (see
    `grim_trigger_sustains_iff` for the grim-trigger special case, proven).

    Genuine STRETCH: BG priority LOW (cf Issue #4880 closing criteria 1). -/
theorem folk_theorem_discounted (g : PrisonersDilemma) :
    ∀ (u_row u_col : ℝ),
      IndividuallyRational g u_row u_col →
      Feasible g u_row u_col →
      u_row > g.P ∧ u_col > g.P →  -- strict IR
      ∃ (δ_star : ℝ), δ_star < 1 ∧
        ∀ (d : ℝ), d ≥ δ_star → d < 1 →
          ∃ (a : ℕ → PDAction × PDAction),
            (1 - d) * discountedPayoff g d a = u_row ∧
            (1 - d) * discountedPayoff g d (fun n => ((a n).2, (a n).1)) = u_col := by
  -- STRETCH (Fudenberg–Maskin 1986): existence of a joint-action trajectory
  -- realizing the target payoff vector (u_row, u_col) as a discounted
  -- average (factor 1 - d), for all δ close enough to 1. Requires convexity
  -- of the feasible-payoff polytope and an extreme-point argument; a
  -- multi-page proof, not one tactic.
  --
  -- Two statement repairs, each documented:
  -- (2026-08-15) the "d < 1" bound: the old quantifier "∀ d ≥ δ*"
  -- (no d < 1 bound) made the theorem FALSE — at d ≥ 1 the series
  -- ∑' d^n · payoff diverge and `tsum` is 0 (junk value). The prover picks
  -- δ* ≥ 0, hence d ∈ [δ*, 1) ⊆ [0, 1) and the series converge absolutely.
  -- (2026-09-12, #15655) the "1 - d" factor: the UNNORMALIZED conclusion
  -- was FALSE even inside [0, 1) — refuted by
  -- folk_theorem_discounted_unnormalized_refuted below.
  sorry

/-! ## Refutation of the unnormalized statement (#15655)

The `1 - d` factor correction is not a nicety: without it, the conclusion of
`folk_theorem_discounted` is outright FALSE, even restricted to the
convergent window `0 ≤ δ < 1` repaired on 2026-08-15. The block below proves
it by concrete counterexample on the canonical PD `(3, 2, 1, 0)`: for the
target `u = (2, 2)` — whose hypotheses all hold and are proven as conjuncts
of the refutation theorem (`pdCanonical_target_hypotheses`: feasible with
`pCC = 1`, strictly individually rational `2 > 1 = P`) — and for every
threshold `δ_star < 1`, there exists `d ∈ [δ_star, 1)` such that NO
trajectory yields `V_row = 2 ∧ V_col = 2`.
The argument (fully proven, zero `sorry`): every joint-action profile pays
`uₙ + vₙ ≥ 2` to the two players, hence `V_row + V_col ≥ 2 · Σ' dⁿ =
2/(1-d) > 4` as soon as `d > 1/2`. -/

/-- The canonical PD of grain #15655: `(T, R, P, S) = (3, 2, 1, 0)`. The four
    constraints `T > R > P > S` and `2R > T + S` (`4 > 3`) check by
    `norm_num`. This is the witness of
    `folk_theorem_discounted_unnormalized_refuted`: the target `u = (2, 2)`
    is feasible there (`pCC = 1`) and strictly individually rational
    (`2 > 1 = P`), so the refutation of the unnormalized statement hits a
    point where ALL the theorem's hypotheses hold — a fact proven by
    `pdCanonical_target_hypotheses`. -/
def pdCanonical : PrisonersDilemma where
  T := 3
  R := 2
  P := 1
  S := 0
  hTR := by norm_num
  hRP := by norm_num
  hPS := by norm_num
  hPD := by norm_num

/-- All the Folk theorem hypotheses hold for the witness
    `(g, u) = (pdCanonical, (2, 2))`: individual rationality (`2 ≥ 1`),
    feasibility (explicit weights `pCC = 1`, `pCD = pDC = pDD = 0` — the
    target is pure mutual cooperation) and strict individual rationality
    (`2 > 1 = P`). This fact, until now purely prosaic in docstrings, here
    becomes a proven lemma that
    `folk_theorem_discounted_unnormalized_refuted` exposes as conjuncts of
    its conclusion: the refutation hits a point where ALL the theorem's
    hypotheses are formally checked, not merely asserted. -/
lemma pdCanonical_target_hypotheses :
    IndividuallyRational pdCanonical 2 2 ∧
    Feasible pdCanonical 2 2 ∧
    2 > pdCanonical.P ∧ 2 > pdCanonical.P := by
  have hT : pdCanonical.T = 3 := rfl
  have hR : pdCanonical.R = 2 := rfl
  have hP : pdCanonical.P = 1 := rfl
  refine ⟨⟨by norm_num [hP], by norm_num [hP]⟩,
    ⟨1, 0, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num [hT, hR, hP], by norm_num [hT, hR, hP]⟩,
    by norm_num [hP], by norm_num [hP]⟩

/-- The canonical PD stage payoffs live in `[0, 3]`: minimum `S = 0`,
    maximum `T = 3`. This bound makes each term `dⁿ · payoff` dominated by
    `3 · dⁿ` — the summability lever of the discounted series
    (`summable_discounted_pdCanonical`). -/
lemma stagePayoff_pdCanonical_bounds (a b : PDAction) :
    0 ≤ stagePayoff pdCanonical a b ∧ stagePayoff pdCanonical a b ≤ 3 := by
  have hT : pdCanonical.T = 3 := rfl
  have hR : pdCanonical.R = 2 := rfl
  have hP : pdCanonical.P = 1 := rfl
  have hS : pdCanonical.S = 0 := rfl
  cases a <;> cases b <;> norm_num [stagePayoff, hT, hR, hP, hS]

/-- Key invariant of the refutation: on the canonical PD, the row + column
    payoff sum of a single joint-action profile is at least `2` — mutual
    cooperation `R + R = 4`, exploitation `T + S = 3` (both directions),
    mutual defection `P + P = 2`. -/
lemma stage_sum_ge_two (a b : PDAction) :
    2 ≤ stagePayoff pdCanonical a b + stagePayoff pdCanonical b a := by
  have hT : pdCanonical.T = 3 := rfl
  have hR : pdCanonical.R = 2 := rfl
  have hP : pdCanonical.P = 1 := rfl
  have hS : pdCanonical.S = 0 := rfl
  cases a <;> cases b <;> norm_num [stagePayoff, hT, hR, hP, hS]

/-- Summability of the discounted series on an arbitrary trajectory of the
    canonical PD: each term `dⁿ · payoff` is dominated in absolute value by
    the geometric series `3 · dⁿ`, summable for `d ∈ [0, 1)`
    (`Summable.of_norm_bounded`). -/
lemma summable_discounted_pdCanonical (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (a : ℕ → PDAction × PDAction) :
    Summable fun n : ℕ => d^n * stagePayoff pdCanonical (a n).1 (a n).2 := by
  have hgeom : Summable fun n : ℕ => 3 * d^n :=
    (summable_geometric_of_lt_one hd0 hd1).mul_left 3
  have hb : ∀ n : ℕ, ‖d^n * stagePayoff pdCanonical (a n).1 (a n).2‖ ≤ 3 * d^n := by
    intro n
    have hp : 0 ≤ d^n := pow_nonneg hd0 n
    have hbd := stagePayoff_pdCanonical_bounds (a n).1 (a n).2
    have habs : |stagePayoff pdCanonical (a n).1 (a n).2| ≤ 3 := by
      rw [abs_of_nonneg hbd.1]
      exact hbd.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
    calc d^n * |stagePayoff pdCanonical (a n).1 (a n).2|
        ≤ d^n * 3 := mul_le_mul_of_nonneg_left habs hp
      _ = 3 * d^n := by ring
  exact Summable.of_norm_bounded hgeom hb

/-- Pointwise inequality: for `d ≥ 0`, twice each geometric weight `2 · dⁿ`
    is dominated by the sum of the two discounted terms (row + column) of
    stage `n` — `stage_sum_ge_two` multiplied through by `dⁿ ≥ 0`. -/
lemma pair_terms_ge_two (d : ℝ) (hd0 : 0 ≤ d) (n : ℕ)
    (a : ℕ → PDAction × PDAction) :
    2 * d^n ≤ d^n * stagePayoff pdCanonical (a n).1 (a n).2
            + d^n * stagePayoff pdCanonical (a n).2 (a n).1 := by
  have h2 := stage_sum_ge_two (a n).1 (a n).2
  have hp : 0 ≤ d^n := pow_nonneg hd0 n
  have h := mul_le_mul_of_nonneg_right h2 hp
  calc 2 * d^n
      ≤ (stagePayoff pdCanonical (a n).1 (a n).2
          + stagePayoff pdCanonical (a n).2 (a n).1) * d^n := h
    _ = d^n * stagePayoff pdCanonical (a n).1 (a n).2
        + d^n * stagePayoff pdCanonical (a n).2 (a n).1 := by ring

/-- Mathematical core of the refutation: for every `d ∈ (1/2, 1)`, NO
    trajectory of the canonical PD realizes `V_row = 2 ∧ V_col = 2` in
    UNNORMALIZED discounted payoffs. If both equations held, summing the
    series would give `∑' dⁿ · (uₙ + vₙ) = 4` (tsum additivity, summability
    by geometric comparison) while `uₙ + vₙ ≥ 2` at every stage forces
    `∑' dⁿ · (uₙ + vₙ) ≥ 2 · ∑' dⁿ = 2/(1-d) > 4` as soon as `d > 1/2` —
    contradiction. -/
theorem unnormalized_pair_payoff_refuted (d : ℝ) (hd : 1/2 < d) (hd1 : d < 1)
    (a : ℕ → PDAction × PDAction) :
    ¬ (discountedPayoff pdCanonical d a = 2 ∧
       discountedPayoff pdCanonical d (fun n => ((a n).2, (a n).1)) = 2) := by
  have hd0 : 0 ≤ d := by linarith
  intro h
  obtain ⟨hrow, hcol⟩ := h
  simp only [discountedPayoff] at hrow hcol
  have hsu : Summable fun n : ℕ => d^n * stagePayoff pdCanonical (a n).1 (a n).2 :=
    summable_discounted_pdCanonical d hd0 hd1 a
  have hsv : Summable fun n : ℕ => d^n * stagePayoff pdCanonical (a n).2 (a n).1 :=
    summable_discounted_pdCanonical d hd0 hd1 fun n => ((a n).2, (a n).1)
  have hsum : ∑' n : ℕ, (d^n * stagePayoff pdCanonical (a n).1 (a n).2
      + d^n * stagePayoff pdCanonical (a n).2 (a n).1) = 4 := by
    rw [Summable.tsum_add hsu hsv, hrow, hcol]
    ring
  have hgeom : ∑' n : ℕ, d^n = (1 - d)⁻¹ := tsum_geometric_of_lt_one hd0 hd1
  have hsum2 : Summable fun n : ℕ => 2 * d^n := by
    have he : (fun n : ℕ => 2 * d^n) = fun n : ℕ => d^n + d^n :=
      funext fun n => by ring
    rw [he]
    exact Summable.add (summable_geometric_of_lt_one hd0 hd1)
      (summable_geometric_of_lt_one hd0 hd1)
  have hle : ∑' n : ℕ, 2 * d^n
      ≤ ∑' n : ℕ, (d^n * stagePayoff pdCanonical (a n).1 (a n).2
          + d^n * stagePayoff pdCanonical (a n).2 (a n).1) :=
    hsum2.tsum_le_tsum (fun n => pair_terms_ge_two d hd0 n a) (hsu.add hsv)
  have hval : ∑' n : ℕ, 2 * d^n = 2 * ∑' n : ℕ, d^n := by
    have he : (fun n : ℕ => 2 * d^n) = fun n : ℕ => d^n + d^n :=
      funext fun n => by ring
    rw [he, Summable.tsum_add (summable_geometric_of_lt_one hd0 hd1)
      (summable_geometric_of_lt_one hd0 hd1)]
    ring
  have hfinal : (2:ℝ) / (1 - d) ≤ 4 := by
    have heq : (2:ℝ) / (1 - d) = 2 * ∑' n : ℕ, d^n := by
      rw [hgeom]; ring
    rw [heq, ← hval]
    linarith
  have hpos : 0 < 1 - d := by linarith
  have hgt : 4 < 2 / (1 - d) := by
    apply (lt_div_iff₀ hpos).mpr
    have hlt : 1 - d < 1 / 2 := by linarith
    have h4 : 4 * (1 - d) < 4 * (1 / 2) := mul_lt_mul_of_pos_left hlt (by norm_num)
    have h2 : (4:ℝ) * (1 / 2) = 2 := by norm_num
    linarith
  linarith

/-- **Refutation of the unnormalized statement** (#15655): on the canonical
    PD `(T, R, P, S) = (3, 2, 1, 0)` for the target `u = (2, 2)` — ALL
    hypotheses of `folk_theorem_discounted` hold and are exposed as PROVEN
    conjuncts of the conclusion (individual rationality, feasibility with
    explicit weights `pCC = 1`, strict individual rationality — via
    `pdCanonical_target_hypotheses`) — for EVERY threshold `δ_star < 1`
    there exists a factor `d ∈ [δ_star, 1)` (namely
    `d = max δ_star (3/4) ∈ [3/4, 1) ⊂ (1/2, 1)`) such that NO joint-action
    trajectory realizes `V_row = 2 ∧ V_col = 2` in UNNORMALIZED discounted
    payoffs. The old conclusion of `folk_theorem_discounted` (equations
    without the `1 - d` factor) was therefore false; this is the
    non-regression of grain #15655: the fully proven theorem (zero `sorry`)
    prevents re-proposing the unnormalized statement. -/
theorem folk_theorem_discounted_unnormalized_refuted :
    ∀ (δ_star : ℝ), δ_star < 1 →
      ∃ (d : ℝ), δ_star ≤ d ∧ d < 1 ∧
        IndividuallyRational pdCanonical 2 2 ∧
        Feasible pdCanonical 2 2 ∧
        2 > pdCanonical.P ∧ 2 > pdCanonical.P ∧
        ∀ (a : ℕ → PDAction × PDAction),
          ¬ (discountedPayoff pdCanonical d a = 2 ∧
             discountedPayoff pdCanonical d (fun n => ((a n).2, (a n).1)) = 2) := by
  intro δ_star hδ
  obtain ⟨hir, hfeas, hgt1, hgt2⟩ := pdCanonical_target_hypotheses
  refine ⟨max δ_star (3 / 4), le_max_left _ _, max_lt hδ (by norm_num),
    hir, hfeas, hgt1, hgt2, ?_⟩
  intro a h
  have h34 : 1 / 2 < max δ_star (3 / 4) := by
    have hle34 := le_max_right δ_star (3 / 4)
    linarith
  exact unnormalized_pair_payoff_refuted _ h34 (max_lt hδ (by norm_num)) a h

/-- Boundary case δ = 0: with no weight on the future, the discounted values
    collapse to the stage payoffs — the repeated game reduces to the one-shot
    game. This is the Folk theorem's boundary case (the only one-shot Nash
    equilibrium is (Defect, Defect) with payoff (P, P)) and anchors the
    construction. Proven: closed forms of `coopValue` / `deviateValue` at
    δ = 0 (`coopValue R 0 = R / (1 − 0) = R`, `deviateValue T P 0 = T + 0 = T`). -/
theorem folk_theorem_boundary (g : PrisonersDilemma) :
    coopValue g.R 0 = g.R ∧ coopValue g.P 0 = g.P ∧ deviateValue g.T g.P 0 = g.T := by
  simp [coopValue, deviateValue]

end RepeatedGames_en
