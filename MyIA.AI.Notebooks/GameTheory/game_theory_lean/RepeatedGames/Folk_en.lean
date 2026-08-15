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

/-- Discounted payoff of the reference (row) player under a trajectory of
    joint actions `a` and discount factor `δ`. Generalizes `coopValue` /
    `deviateValue` (stationary special cases) to an arbitrary trajectory:
    `Σ' n, δⁿ · stagePayoff g (a n).1 (a n).2`. The column player's payoff
    under the same trajectory is obtained by swapping the joint-action
    components (see `folk_theorem_discounted`). -/
noncomputable def discountedPayoff (g : PrisonersDilemma) (δ : ℝ)
    (a : ℕ → PDAction × PDAction) : ℝ :=
  ∑' n : ℕ, δ^n * stagePayoff g (a n).1 (a n).2

/-- The DISCOUNTED Folk theorem (Fudenberg–Maskin 1986, simplified for 2x2):

      For every strictly individually rational feasible payoff
      `u = (u_row, u_col)`, there exists δ* < 1 such that for all δ ≥ δ* the
      vector `u` is realized as the discounted payoff of a trajectory of
      joint actions.

    The conclusion is a **real equation** (`discountedPayoff … = u_row ∧
    … = u_col`), not `True`: the `sorry` thus carries the genuine debt
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
        ∀ (d : ℝ), d ≥ δ_star →
          ∃ (a : ℕ → PDAction × PDAction),
            discountedPayoff g d a = u_row ∧
            discountedPayoff g d (fun n => ((a n).2, (a n).1)) = u_col := by
  -- STRETCH (Fudenberg–Maskin 1986): existence of a joint-action trajectory
  -- realizing the target payoff vector (u_row, u_col) as a discounted payoff,
  -- for all δ close enough to 1. Requires convexity of the feasible-payoff
  -- polytope and an extreme-point argument; a multi-page proof, not one tactic.
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
