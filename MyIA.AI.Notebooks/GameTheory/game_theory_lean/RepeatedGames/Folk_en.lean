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
  Several lemmas carry `sorry` as placeholders; the prover BG harness will
  attempt them in later iterations but they are flagged as low-priority.

  Type-forced definitions (lesson Lidman L39, PR #4899): `IndividuallyRational`
  is bounded by `g.P` and `Feasible` is a convex constraint on the four joint
  actions, **so correctness is forced by the type system, not by any cited
  numerical data** (no KnotInfo-style tables, no source labels). The `sorry`
  on `folk_theorem_discounted` is the genuine hard direction (Fudenberg–Maskin
  polytope topology, OUT of scope of the GrimTrigger sprint).
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

/-- Refutation witness (#15655): the PD `T = 3, R = 2, P = 1, S = 0` — the
positional reading of `(3, 2, 1, 0)` in field order `(T, R, P, S)`. The four
`PrisonersDilemma` axioms hold by `norm_num` (no numerical data cited
downstream: everything is carried by the structure). This game carries the
feasible strictly-IR target `u = (2, 2)` (the cooperative vertex `(R, R)`),
which refutes the unnormalized statement of the discounted Folk theorem —
see `folk_theorem_discounted_unnormalized_refuted`. -/
def folkCounterexample : PrisonersDilemma where
  T := 3
  R := 2
  P := 1
  S := 0
  hTR := by norm_num
  hRP := by norm_num
  hPS := by norm_num
  hPD := by norm_num

/-- The Folk-theorem hypotheses ARE satisfied by the witness: for
`folkCounterexample` (T3, R2, P1, S0), the target `u = (2, 2)` is
individually rational, feasible (the cooperative vertex `(R, R)`: weights
`pCC = 1`, others zero) and strictly individually rational (`2 > P`). The
refutation below thus hits the statement itself, not a hypothesis artefact. -/
theorem folkCounterexample_hypotheses :
    IndividuallyRational folkCounterexample 2 2 ∧
      Feasible folkCounterexample 2 2 ∧
      (2 > folkCounterexample.P ∧ 2 > folkCounterexample.P) := by
  refine ⟨⟨?_, ?_⟩, ⟨1, 0, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    norm_num [folkCounterexample]

/-- Symmetrized stage-payoff sum on the witness game: any pair of moves earns
at least `2` in total. The four possible cases give `R + R = 4` (cooperation),
`S + T = 3` and `T + S = 3` (exploitation), `P + P = 2` (mutual defection) —
the minimum is the defection level. -/
lemma stage_sum_ge_two (x y : PDAction) :
    2 ≤ stagePayoff folkCounterexample x y + stagePayoff folkCounterexample y x := by
  cases x <;> cases y <;> simp only [stagePayoff, folkCounterexample] <;> norm_num

/-- **Refutation of the UNNORMALIZED statement** (#15655). The old conclusion
of the discounted Folk theorem — `discountedPayoff g d a = u_row ∧ … = u_col`
on the RAW series — is FALSE, for any threshold `δ_star < 1`: on the witness
game `folkCounterexample` (T3, R2, P1, S0) with the feasible strictly-IR
target `u = (2, 2)`, no trajectory can realize the pair `(2, 2)` once
`d > 1/2`.

    Argument (by contradiction): every stage profile earns at least `2` in
    total (`stage_sum_ge_two`), so the sum of the two series equals
    `Σ' dⁿ · (p_row + p_col) ≥ 2 · Σ' dⁿ = 2 / (1 - d)`. If both discounted
    payoffs were `2` each, the sum would be `4` — yet `2 / (1 - d) > 4`
    whenever `d > 1/2`. For any `δ_star < 1` pick `d = max δ_star (3/4)`
    (which satisfies `δ_star ≤ d < 1` and `d > 1/2`) and the contradiction
    fires.

    Technical detail: each series is summable because its sum is `2 ≠ 0`
    (`tsum_eq_zero_of_not_summable`), enabling `Summable.tsum_add` then the
    `Summable.tsum_le_tsum` comparison with the geometric series (doubled as
    `dⁿ + dⁿ` to stay within the basic infinite-sum lemmas). The repaired
    statement `folk_theorem_discounted` normalizes both equations by
    `1 - d`: the target is the discounted MEAN payoff, whose sum is
    `u_row + u_col`, compatible with the lower bound `2`. -/
theorem folk_theorem_discounted_unnormalized_refuted :
    ¬ ∃ (δ_star : ℝ), δ_star < 1 ∧
      ∀ (d : ℝ), d ≥ δ_star → d < 1 →
        ∃ (a : ℕ → PDAction × PDAction),
          discountedPayoff folkCounterexample d a = 2 ∧
          discountedPayoff folkCounterexample d (fun n => ((a n).2, (a n).1)) = 2 := by
  rintro ⟨δ_star, hδs, hall⟩
  have hdl : max δ_star (3 / 4) < 1 := max_lt_iff.mpr ⟨hδs, by norm_num⟩
  obtain ⟨a, ha1, ha2⟩ := hall (max δ_star (3 / 4)) (le_max_left _ _) hdl
  set d := max δ_star (3 / 4)
  have hd0 : (1 / 2 : ℝ) < d := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hdnn : 0 ≤ d := by linarith
  have hs1 : Summable fun n : ℕ =>
      d ^ n * stagePayoff folkCounterexample (a n).1 (a n).2 := by
    by_contra hns
    simp only [discountedPayoff] at ha1
    rw [tsum_eq_zero_of_not_summable hns] at ha1
    norm_num at ha1
  have hs2 : Summable fun n : ℕ =>
      d ^ n * stagePayoff folkCounterexample (a n).2 (a n).1 := by
    by_contra hns
    simp only [discountedPayoff] at ha2
    rw [tsum_eq_zero_of_not_summable hns] at ha2
    norm_num at ha2
  have h4 : discountedPayoff folkCounterexample d a
      + discountedPayoff folkCounterexample d (fun n => ((a n).2, (a n).1)) = 4 := by
    rw [ha1, ha2]; norm_num
  have hgeo : Summable fun n : ℕ => d ^ n := summable_geometric_of_lt_one hdnn hdl
  have hlb : ∀ n : ℕ, d ^ n + d ^ n
      ≤ d ^ n * stagePayoff folkCounterexample (a n).1 (a n).2
        + d ^ n * stagePayoff folkCounterexample (a n).2 (a n).1 := by
    intro n
    have hp : 2 ≤ stagePayoff folkCounterexample (a n).1 (a n).2
        + stagePayoff folkCounterexample (a n).2 (a n).1 :=
      stage_sum_ge_two (a n).1 (a n).2
    have hdn : 0 ≤ d ^ n := pow_nonneg (by linarith) n
    calc d ^ n + d ^ n = d ^ n * 2 := by ring
      _ ≤ d ^ n * (stagePayoff folkCounterexample (a n).1 (a n).2
          + stagePayoff folkCounterexample (a n).2 (a n).1) :=
        mul_le_mul_of_nonneg_left hp hdn
      _ = d ^ n * stagePayoff folkCounterexample (a n).1 (a n).2
          + d ^ n * stagePayoff folkCounterexample (a n).2 (a n).1 := by ring
  have hbound : 2 / (1 - d) ≤ discountedPayoff folkCounterexample d a
      + discountedPayoff folkCounterexample d (fun n => ((a n).2, (a n).1)) := by
    have hgeo' : ∑' n : ℕ, (d ^ n + d ^ n) = 2 / (1 - d) := by
      rw [Summable.tsum_add hgeo hgeo, tsum_geometric_of_lt_one hdnn hdl]; ring
    rw [← hgeo']
    simp only [discountedPayoff]
    calc ∑' n : ℕ, (d ^ n + d ^ n)
        ≤ ∑' n : ℕ, (d ^ n * stagePayoff folkCounterexample (a n).1 (a n).2
          + d ^ n * stagePayoff folkCounterexample (a n).2 (a n).1) :=
        Summable.tsum_le_tsum hlb (hgeo.add hgeo) (hs1.add hs2)
      _ = ∑' n : ℕ, d ^ n * stagePayoff folkCounterexample (a n).1 (a n).2
          + ∑' n : ℕ, d ^ n * stagePayoff folkCounterexample (a n).2 (a n).1 :=
        Summable.tsum_add hs1 hs2
  rw [h4] at hbound
  have h1pos : 0 < 1 - d := by linarith
  rw [div_le_iff₀ h1pos] at hbound
  ring_nf at hbound
  have h4d : (2 : ℝ) < 4 * d := by
    have hmul := mul_lt_mul_of_pos_left hd0 (show (0 : ℝ) < 4 by norm_num)
    norm_num at hmul
    exact hmul
  linarith

/-- The DISCOUNTED Folk theorem (Fudenberg–Maskin 1986, simplified for 2x2),

    NORMALIZED form (#15655):

      For every strictly individually rational feasible payoff
      `u = (u_row, u_col)`, there exists δ* < 1 such that for all δ ∈ [δ*, 1) the
      vector `u` is realized as the discounted MEAN payoff of a trajectory of
      joint actions — each equation carries the `1 - d` factor:
      `(1 - d) · Σ' dⁿ · payoff = u`.

    The normalization is not cosmetic: the RAW statement
    (`discountedPayoff … = u` without the factor) is formally refuted by
    `folk_theorem_discounted_unnormalized_refuted` above — on the witness
    game (T3, R2, P1, S0) with the feasible strictly-IR target (2, 2), the
    sum of the two series is bounded below by `2 / (1 - d) > 4` whenever
    `d > 1/2`, so no trajectory can realize the raw pair near 1. The MEAN
    payoff escapes the refutation: its sum is `u_row + u_col`, within the
    range allowed by the lower bound.

    The conclusion is a **real equation** (`(1 - d) * discountedPayoff … =
    u_row ∧ … = u_col`), not `True`: the `sorry` thus carries the genuine debt
    (existence of a trajectory realizing the target vector — the
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
  -- Normalized statement (2026-09-13, #15655): the `1 - d` factor sits on
  -- BOTH equations — this is the discounted MEAN payoff, the standard
  -- Fudenberg–Maskin conclusion. The old unnormalized conclusion was FALSE:
  -- formally refuted by `folk_theorem_discounted_unnormalized_refuted`
  -- (witness T3/R2/P1/S0, u = (2, 2): every stage earns at least 2 in total,
  -- so the sum of the two series is ≥ 2 / (1 - d) > 4 = u_row + u_col once
  -- d > 1/2 — no trajectory realizes the raw pair near 1).
  --
  -- STRETCH (Fudenberg–Maskin 1986): existence of a joint-action trajectory
  -- realizing the target payoff vector (u_row, u_col) as a discounted mean
  -- payoff, for all δ close enough to 1. Requires convexity of the
  -- feasible-payoff polytope and an extreme-point argument; a multi-page
  -- proof, not one tactic.
  --
  -- Statement edge repaired (2026-08-15): the old quantifier "∀ d ≥ δ*"
  -- (no d < 1 bound) made the theorem FALSE — at d ≥ 1 the series
  -- ∑' d^n · payoff diverge and `tsum` is 0 (junk value), so no u ≠ 0 is
  -- realizable (witness: g = ⟨3, 2, 1, 0⟩, u = (2, 2), d = 2).
  -- The "d < 1" bound repairs without strengthening: the prover picks
  -- δ* ≥ 0, hence d ∈ [δ*, 1) ⊆ [0, 1) and the series converge absolutely.
  sorry

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
