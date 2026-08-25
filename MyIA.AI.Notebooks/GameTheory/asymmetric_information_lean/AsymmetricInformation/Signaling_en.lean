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
  - Riley least-cost separator illustrated on a **finite explicit instance**
    (not a general theorem);
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

/-- **Decided examples**: on the instance `(y_H, y_L) = (10, 4)` and the
    specified cost, `(s_L, s_H) = (0, 6)` is a valid separator:

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