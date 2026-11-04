import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Gittins.Basic_en
import Gittins.Discount_en

/-!
# Prover program terrains (#1453) — documented `sorry`s

Fresh training terrains for the prover program (EPIC #1453, dispatch c2770,
2026-11-04): theorems we had refused to add, posed here as new targets with a
**documented** `sorry` in the proof — never in the statement (lesson #24705:
an honest statement first). Each was **verified absent from Mathlib at the
pin** (`db584cd6d46c`, measured by grepping the vendored Mathlib tree in
`.lake/packages/mathlib/`) before the `sorry` was placed, so the advertised
difficulty is real and not a disguise over an existing lemma.

Difficulty gradient (same P1/P2/P3 vocabulary as the CALIBRATION sub-track):

| Terrain | Class | Mathlib verification at pin |
|---|---|---|
| `panel_quarter_partial_sum` | P1 — concrete computation | statement about a lake definition (`geometricPartialSum`), hence out of Mathlib's reach by construction |
| `panel_constant_stream_monotone` | P2 — rewrite chain | `tsum_le_tsum` exists at the pin only over ℝ≥0/ℝ≥0∞ (`InfiniteSum/ENNReal.lean:115`) — **not over raw ℝ**; the pointwise shortcut is closed, the closed form (`present_value_constant`) is the route |
| `panel_partial_sums_tendsto` | P3 — List→tsum bridge | `HasSum.tendsto_sum_nat` exists at the pin (compiled usages in `InfiniteSum/Ring.lean:281`) and serves as the **final step**; the difficulty is the `List.foldl` → `∑ k ∈ Finset.range n` bridge, which is local to the lake |

The `sorry-baseline` of `scripts/lean/ci_lakes.json` goes from 2 to 5 in the
same PR (the gate requires exact equality, bidirectional failure).
i18n convention (#4980): French original in `Gittins/Panel.lean` (namespace
`Gittins`); only the docstrings differ between the two files.
-/

namespace Gittins_en

open Filter

/-- **P1 terrain — concrete computation** (prover program #1453, dispatch c2770).

Geometric partial sum in base 1/4 over three terms: `1 + 1/4 + 1/16 = 21/16`.
Easiest class of the gradient: unfold the definition (`geometricPartialSum`)
then compute exactly (`norm_num`). This is the decision-theory analogue of
the concrete targets of the CALIBRATION sub-track (`isWinningNim_345`,
`lookAndSay_4`).

Mathlib absence verification (pin `db584cd6d46c`): the statement talks about
`geometricPartialSum`, a lake definition — no Mathlib entity can state it;
`grep -r "geometricPartialSum"` over the vendored tree returns 0 hits. The P1
difficulty is therefore honest: unfold the local definition then compute,
with no external lemma short-circuiting the goal. -/
theorem panel_quarter_partial_sum : geometricPartialSum (1 / 4) 3 = 21 / 16 := by
  sorry

/-- **P2 terrain — rewrite chain** (prover program #1453, dispatch c2770).

Monotonicity of the discounted value of a constant stream: if `μ₁ ≤ μ₀` (with
`0 ≤ μ₁`, `0 < γ < 1`), then `∑' γⁿ·μ₁ ≤ ∑' γⁿ·μ₀`. This is the elementary
arbitrage move of a known-mean bandit: the value of the better arm's stream
dominates the dominated one's.

Mathlib absence verification (pin `db584cd6d46c`): the short pointwise route
`tsum_le_tsum` exists at the pin **only over ℝ≥0/ℝ≥0∞**
(`InfiniteSum/ENNReal.lean:115`, `protected`, namespace `ENNReal`) — measured
by `grep -rn "theorem tsum_le_tsum" Mathlib/`: 1 hit, none over ℝ. The route
therefore goes through the closed form: rewrite each side with
`present_value_constant` (`Gittins.Discount`), then compare `μ₁/(1-γ) ≤
μ₀/(1-γ)` using `one_minus_gamma_pos` as the sign condition. A few tactics,
several lemmas to find: P2. -/
theorem panel_constant_stream_monotone {γ μ₁ μ₀ : ℝ} (hγ₁ : 0 < γ) (hγ₂ : γ < 1)
    (hμ₁ : 0 ≤ μ₁) (h : μ₁ ≤ μ₀) :
    ∑' n : ℕ, γ ^ n * μ₁ ≤ ∑' n : ℕ, γ ^ n * μ₀ := by
  sorry

/-- **P3 terrain — List→tsum bridge** (prover program #1453, dispatch c2770).

Convergence of discounted partial sums to their total sum: the partial sums
`geometricPartialSum γ n · μ` (defined by a `List.foldl` over `List.range`)
tend to `∑' γᵏ·μ` as `n → ∞`, for `0 < γ < 1`. This is the analytic piece
connecting the lake's *finite* definition to the *infinite* theory of
`Gittins.Discount`.

Mathlib presence/absence verification (pin `db584cd6d46c`):
`HasSum.tendsto_sum_nat` **exists** at the pin (compiled usages in
`InfiniteSum/Ring.lean:281,286`) but only applies to sums `∑ k ∈
Finset.range n` — not to our `List.foldl`. The terrain's difficulty is the
**bridge** `geometricPartialSum γ n = ∑ k ∈ Finset.range n, γ ^ k` (induction
on `n`, `List.foldl` ↔ `Finset.sum`), then extracting a `HasSum` from
`geometric_series_converges` (`Summable.hasSum`), and multiplying by the
constant `μ` (`Tendsto.mul_const` / continuity). The Mathlib lemma is a final
step, not the proof: P3 by composition. -/
theorem panel_partial_sums_tendsto {γ μ : ℝ} (hγ₁ : 0 < γ) (hγ₂ : γ < 1) :
    Tendsto (fun n => geometricPartialSum γ n * μ) atTop (nhds (∑' k : ℕ, γ ^ k * μ)) := by
  sorry

end Gittins_en
