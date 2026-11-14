import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.GeomSum
import RepeatedGames.Stage_en
import RepeatedGames.Discounting_en

/-!
  Repeated Games — Panel prover terrains (tranche 2, #1453) — EN sibling
  =====================================================================

  English mirror of `RepeatedGames/Panel.lean` (FR-first canonical).
  Convention i18n Lean ratified by ai-01 (2026-07-04, #4980): distinct
  `.lean` files FR + EN siblings in the same lake, both compile.
  Non-docstring content byte-identical between siblings (drift-CI
  detectable). Namespace sibling: `RepeatedGames_en`.

  Three prover-panel terrains on existing vocabulary, statements validated
  by ai-01 beforehand (arbitration 2026-11-05T00:31:43Z). Each carries one
  anchored `sorry` (`[LEAN-ANCHOR-DECLARED]`): the statement is complete,
  the `sorry` replaces only the proof.

  The reference proof routes are NOT written in this file. It is read by
  the prover: writing a route there would hand it the answer. They live in
  the PR #24730 thread (comment c.6648328912), which is the ledger's
  ground truth for the prover program.

  Measured classes: P1 (easy), P2 (medium), P3 (hard) — the gradient is
  described in the docstrings below.
-/

open RepeatedGames_en.PDAction Filter
open scoped BigOperators

namespace RepeatedGames_en

/-! ## The canonical Gibbons prisoners' dilemma -/

/-- The canonical Gibbons (2020) prisoners' dilemma: T = 5, R = 3, P = 1,
S = 0. The four `PrisonersDilemma` constraints are proved by `norm_num`. -/
noncomputable def panelPD : PrisonersDilemma :=
  ⟨5, 3, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## Terrain P1 — threshold of the canonical PD

The critical cooperation threshold of the canonical PD is exactly 1/2:
past δ = 1/2, the grim-trigger cooperative path dominates a one-shot
deviation. -/

/-- Terrain P1 (class P1, easy): the critical cooperation threshold of the
canonical Gibbons PD is 1/2. A reference proof exists; it is recorded in
the PR #24730 thread (c.6648328912) and is not written here, this file
being read by the prover. -/
theorem panel_pd_threshold_half :
    (panelPD.T - panelPD.R) / (panelPD.T - panelPD.P) = 1 / 2 := by
  sorry  -- [LEAN-ANCHOR-DECLARED]

/-! ## Terrain P2 — comparative statics of punishment

Hardening the punishment (lowering P) lowers the critical threshold:
cooperation becomes sustainable for a smaller δ. -/

/-- Terrain P2 (class P2, medium): a harsher punishment lowers the critical
cooperation threshold — `(T - R) / (T - P₂) ≤ (T - R) / (T - P₁)` when
`P₂ ≤ P₁`. A reference proof exists; it is recorded in the PR #24730
thread (c.6648328912) and is not written here, this file being read by the
prover. -/
theorem panel_harsher_punishment_lowers_threshold
    (T R P₁ P₂ : ℝ) (hTR : R < T) (hP : P₂ ≤ P₁) (hTP : P₁ < T) :
    (T - R) / (T - P₂) ≤ (T - R) / (T - P₁) := by
  sorry  -- [LEAN-ANCHOR-DECLARED]

/-! ## Terrain P3 — finite-horizon convergence to the perpetuity

The discounted payoff of the cooperative path at finite horizon n
converges to `coopValue R δ` as n → ∞: the analytic piece that links the
panel's finite horizon to the infinite stream. -/

/-- Terrain P3 (class P3, hard): the payoff of the cooperative path at
finite horizon converges to the perpetuity `coopValue R δ`. A reference
proof exists; it is recorded in the PR #24730 thread (c.6648328912) and is
not written here, this file being read by the prover. -/
theorem panel_partial_coop_tendsto
    (R δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ < 1) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, δ ^ k * R) atTop
      (nhds (coopValue R δ)) := by
  sorry  -- [LEAN-ANCHOR-DECLARED]

end RepeatedGames_en
