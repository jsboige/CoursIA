/-
  Signaling — Spence 1973 model, bounded formalization
  =====================================================

  Formalization of Spence's 1973 *QJE* 87(3):355-374 costly signaling
  model. The candidate of type `q ∈ {H, L}` (productivity `y_q`)
  chooses a signal `s ∈ ℕ` (cost `c(q, s) ∈ ℕ`), the employer observes
  `s` and proposes a wage `w(s)`. The candidate's utility is `w - c`.

  Four explicit constraints at the separating equilibrium:
  1. IC_H: `y_H - c(H, s_H) ≥ y_L - c(H, s_L)`
  2. IC_L: `y_L - c(L, s_L) ≥ y_H - c(L, s_H)`
  3. IR_H: `y_H - c(H, s_H) ≥ u_bar_H`
  4. IR_L: `y_L - c(L, s_L) ≥ u_bar_L`

  Competitive wage: `w_q = y_q` (the employer pays the productivity of
  the type that chose the signal). **NOT** a zero universal H rent.

  Strict bounds (audit c.475 category #1+#5):
  - NO `∃` statement for the interval without FINITE hypotheses listed;
  - algebraic bounds of the separator interval **derived** from
    IC_H/IC_L (`separator_icHigh_bound`, `separator_icLow_bound`) and
    Riley least-cost `sHigh = 3` proved **minimal** by the lower
    bound — on a finite explicit instance, no general uniqueness
    theorem;
  - No universal single-crossing — each lemma lists its hypotheses.

  English mirror of `Signaling.lean`. Byte-identical except docstrings.
-/

namespace AsymmetricInformation.Signaling

/-- Candidate type: high or low productivity. -/
inductive WorkerType where
  | low
  | high
  deriving DecidableEq, Repr

/-- Cost of signal `s` for type `q`, in natural numbers (consistent with
    upstream API). Single-crossing encoded: lower cost for H. -/
def signalCost (q : WorkerType) (s : Nat) : Nat :=
  match q with
  | .low  => 2 * s   -- higher cost for L (single-crossing encoded)
  | .high => s

/-- Candidate utility of type `q` receiving wage `w` and having chosen
    signal `s` (cost `signalCost q s`). `w - c(q, s)` directly. -/
def workerUtility (w : Int) (q : WorkerType) (s : Nat) : Int :=
  w - (signalCost q s : Int)

/-- Type productivity: `y_H > y_L`. -/
structure Productivity where
  yLow : Int
  yHigh : Int
  hOrder : yLow < yHigh

/-- Competitive wage: `w_q = y_q` (Spence 1973, signaling equation). -/
def competitiveWage (p : Productivity) (q : WorkerType) : Int :=
  match q with | .low => p.yLow | .high => p.yHigh

/-- The **four constraints** explicit on a separator. `s_L < s_H` is
    imposed by the statement (separation means the two types choose
    distinct signals). -/
structure Separator (p : Productivity) where
  sLow : Nat
  sHigh : Nat
  sOrder : sLow < sHigh
  reserveLow : Int
  reserveHigh : Int
  icHigh :
    p.yHigh - (signalCost .high sHigh : Int)
      ≥ p.yLow - (signalCost .high sLow : Int)
  icLow :
    p.yLow - (signalCost .low sLow : Int)
      ≥ p.yHigh - (signalCost .low sHigh : Int)
  irHigh :
    p.yHigh - (signalCost .high sHigh : Int) ≥ reserveHigh
  irLow :
    p.yLow - (signalCost .low sLow : Int) ≥ reserveLow

/-- Wage constructor from a separator: `w_q = y_q`
    (competitive, no universal H rent). -/
def separatorWage (p : Productivity) (sep : Separator p) (q : WorkerType) : Int :=
  competitiveWage p q

/- ## Algebraic bounds of the separator interval (repair #12848 c.503)

  IC_L and IC_H are not merely checked on witnesses: they **bound**
  the interval of possible separators. For the fixed cost encoding
  `c_H(s) = s`, `c_L(s) = 2s` (`signalCost` above), IC_H yields
  `sHigh ≤ (yHigh - yLow) + sLow` and IC_L yields
  `2 * sHigh ≥ (yHigh - yLow) + 2 * sLow`. On the instance
  `(yLow, yHigh) = (4, 10)` with `sLow = 0`, the interval is exactly
  `[3, 6]` — and the **least-cost** Riley separator is the lower
  endpoint `sHigh = 3`.
-/

/-- **Upper bound (IC_H)**: type H must not prefer L's signal. With
    `c_H(s) = s`, `yHigh - sHigh ≥ yLow - sLow` rearranges into
    `sHigh ≤ (yHigh - yLow) + sLow`. -/
theorem separator_icHigh_bound (p : Productivity) (sep : Separator p) :
    (sep.sHigh : Int) ≤ p.yHigh - p.yLow + (sep.sLow : Int) := by
  have hic := sep.icHigh
  simp only [signalCost] at hic
  omega

/-- **Lower bound (IC_L)**: type L must not want to imitate H. With
    `c_L(s) = 2s`, `yLow - 2*sLow ≥ yHigh - 2*sHigh` rearranges into
    `2*sHigh ≥ (yHigh - yLow) + 2*sLow`. -/
theorem separator_icLow_bound (p : Productivity) (sep : Separator p) :
    2 * (sep.sHigh : Int) ≥ p.yHigh - p.yLow + 2 * (sep.sLow : Int) := by
  have hic := sep.icLow
  simp only [signalCost] at hic
  omega

/-- **Derived separator interval on the instance** `(yLow, yHigh) =
    (4, 10)` with `sLow = 0`: every separator satisfies
    `3 ≤ sHigh ≤ 6`. Both bounds come from the general lemmas above —
    no witness is assumed. -/
theorem separator_interval_instance (p : Productivity)
    (hEq : p.yLow = 4 ∧ p.yHigh = 10)
    (sep : Separator p) (h : sep.sLow = 0) :
    3 ≤ sep.sHigh ∧ (sep.sHigh : Int) ≤ 6 := by
  obtain ⟨hyl, hyh⟩ := hEq
  have hUp := separator_icHigh_bound p sep
  have hLow := separator_icLow_bound p sep
  rw [h] at hLow
  constructor <;> omega

/-- **Riley minimality**: every separator of the instance with
    `sLow = 0` has `sHigh ≥ 3` — a direct consequence of the IC_L
    lower bound, not a case sampling. -/
theorem riley_sHigh_minimal (p : Productivity)
    (hEq : p.yLow = 4 ∧ p.yHigh = 10)
    (sep : Separator p) (h : sep.sLow = 0) : 3 ≤ sep.sHigh := by
  obtain ⟨hyl, hyh⟩ := hEq
  have hLow := separator_icLow_bound p sep
  rw [h] at hLow
  omega

/-- **Decided counter-witness**: `sHigh = 2` (with `sLow = 0`) violates
    IC_L — `4 ≥ 10 - 2*2 = 6` is arithmetically false. The refutation
    goes through the minimality above, not through re-sampling. -/
example : ¬ ∃ sep : Separator ⟨4, 10, by omega⟩, sep.sLow = 0 ∧ sep.sHigh = 2 := by
  intro h
  obtain ⟨sep, hsLow, hsHigh⟩ := h
  have hmin := riley_sHigh_minimal ⟨4, 10, by omega⟩ ⟨rfl, rfl⟩ sep hsLow
  rw [hsHigh] at hmin
  omega

/-- **Riley least-cost — decided witness**: `(s_L, s_H) = (0, 3)` is
    the LOWER endpoint of the interval `[3, 6]`, hence the
    **lowest-cost** separating signal on the instance:

    - IC_H: `10 - 3 ≥ 4 - 0` ⟹ `7 ≥ 4` ✓
    - IC_L: `4 - 0 ≥ 10 - 6` ⟹ `4 ≥ 4` ✓ (**equality** — exactly the
      frontier, hence minimality)
    - IR_H: `10 - 3 ≥ 0` ⟹ `7 ≥ 0` ✓ (u_bar_H = 0)
    - IR_L: `4 - 0 ≥ 0` ⟹ `4 ≥ 0` ✓ (u_bar_L = 0) -/
example : ∃ sep : Separator ⟨4, 10, by omega⟩,
    sep.sLow = 0 ∧ sep.sHigh = 3 ∧ sep.reserveLow ≤ 0 ∧ sep.reserveHigh ≤ 0 := by
  refine ⟨⟨0, 3, by omega, 0, 0, by decide, by decide, by decide, by decide⟩, rfl, rfl, by decide, by decide⟩

/-- **Decided example — HIGH endpoint of the interval**: on the
    instance `(y_H, y_L) = (10, 4)` and the specified cost,
    `(s_L, s_H) = (0, 6)` is a valid separator, but it is the
    HIGHEST-cost signal of `[3, 6]` — not Riley's least-cost (which is
    `sHigh = 3` above):

    - IC_H: `10 - 6 ≥ 4 - 0` ⟹ `4 ≥ 4` ✓
    - IC_L: `4 - 0 ≥ 10 - 12` ⟹ `4 ≥ -2` ✓
    - IR_H: `10 - 6 ≥ 0` ⟹ `4 ≥ 0` ✓ (u_bar_H = 0)
    - IR_L: `4 - 0 ≥ 0` ⟹ `4 ≥ 0` ✓ (u_bar_L = 0) -/
example : ∃ sep : Separator ⟨4, 10, by omega⟩,
    sep.sLow = 0 ∧ sep.sHigh = 6 ∧ sep.reserveLow ≤ 0 ∧ sep.reserveHigh ≤ 0 := by
  refine ⟨⟨0, 6, by omega, 0, 0, by decide, by decide, by decide, by decide⟩, rfl, rfl, by decide, by decide⟩

/-- **NO general uniqueness claim**: on the same instance, we exhibit a
    **second separator** `(s_L, s_H) = (1, 7)` that also satisfies the
    4 constraints. Calculation: `signalCost .high 7 = 7`,
    `signalCost .high 1 = 1`, `signalCost .low 1 = 2`, `signalCost .low 7 = 14`.
    - IC_H: `10 - 7 ≥ 4 - 1` ⟹ `3 ≥ 3` ✓
    - IC_L: `4 - 2 ≥ 10 - 14` ⟹ `2 ≥ -4` ✓
    - IR_H: `10 - 7 ≥ 0` ⟹ `3 ≥ 0` ✓
    - IR_L: `4 - 2 ≥ 0` ⟹ `2 ≥ 0` ✓ -/
example : ∃ sep : Separator ⟨4, 10, by omega⟩,
    sep.sLow = 1 ∧ sep.sHigh = 7 ∧ sep.reserveLow ≤ 0 ∧ sep.reserveHigh ≤ 0 := by
  refine ⟨⟨1, 7, by omega, 0, 0, by decide, by decide, by decide, by decide⟩, rfl, rfl, by decide, by decide⟩

end AsymmetricInformation.Signaling