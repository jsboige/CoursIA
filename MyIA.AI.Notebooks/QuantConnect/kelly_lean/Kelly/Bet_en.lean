import Mathlib

/-!
# Kelly.Bet — Bernoulli bet, wagered fraction, wealth multipliers

A **Bernoulli bet** (the canonical setting of the Kelly criterion): with
probability `p` one wins and receives `b` times the stake `f` (net odds `b`), with
probability `q = 1 − p` one loses the stake. The relative wealth after the bet is:
- **`1 + b·f`** in case of a win (capital + profit `b·f`),
- **`1 − f`** in case of a loss (capital − stake `f`).

The **wagered fraction** `f` lives in the open interval `(−1/b, 1)`: beyond it both
multipliers are no longer strictly positive (the log-growth is undefined). A negative
fraction = betting *against* the player (short), `f = 0` = bet nothing.

This module sets up the model. The optimal fraction `f*` and the flagship theorem live
in `Kelly.lean`. See issue #4052.
-/

namespace KellyLean_en

open Real

/-- A Bernoulli bet parameterized by its win probability `p` and its net odds `b`. -/
structure Bet where
  /-- Win probability, strictly between 0 and 1. -/
  p : ℝ
  hp_pos : 0 < p
  hp_lt_one : p < 1
  /-- Net odds: profit `b` per unit staked in case of a win, `b > 0`. -/
  b : ℝ
  hb_pos : 0 < b

/-- Loss probability, `q = 1 − p`. -/
def q (β : Bet) : ℝ := 1 - β.p

/-- The loss probability is strictly positive (since `p < 1`). -/
lemma q_pos (β : Bet) : 0 < q β := by unfold q; linarith [β.hp_lt_one]

/-- The loss probability is strictly less than 1 (since `p > 0`). -/
lemma q_lt_one (β : Bet) : q β < 1 := by unfold q; linarith [β.hp_pos]

/-- Probabilities sum to 1: `p + q = 1`. -/
lemma pq_add_eq_one (β : Bet) : β.p + q β = 1 := by unfold q; ring

/-- Wealth multiplier in case of a **win**: `1 + b·f` (capital + profit `b·f`). -/
def winWealth (β : Bet) (f : ℝ) : ℝ := 1 + β.b * f

-- Wealth multiplier in case of a **loss**: `1 − f` (capital − stake `f`).
-- Le corps ne dépend pas de la cote `β.b` (perdre sa mise est universel), mais `β`
-- est gardé en paramètre pour la symétrie d'API avec `winWealth`. L'option silences
-- le linter `unusedVariables` (intentionnel : API symétrique).
set_option linter.unusedVariables false in
def loseWealth (β : Bet) (f : ℝ) : ℝ := 1 - f

/-- The net odds satisfy `b + 1 > 0` (useful for domains). -/
lemma b_add_one_pos (β : Bet) : 0 < β.b + 1 := by linarith [β.hb_pos]

/-- `winWealth` is strictly positive on the admissible region `f > −1/b`. -/
lemma winWealth_pos (β : Bet) (f : ℝ) (hf : -1 / β.b < f) : 0 < winWealth β f := by
  unfold winWealth
  rw [div_lt_iff₀ β.hb_pos] at hf
  linarith [mul_comm β.b f]

/-- `loseWealth` is strictly positive on the admissible region `f < 1`. -/
lemma loseWealth_pos (β : Bet) (f : ℝ) (hf : f < 1) : 0 < loseWealth β f := by
  unfold loseWealth; linarith

/-- **Admissible region** of a fraction `f`: both multipliers are strictly
    positive, i.e. `f ∈ (−1/b, 1)`. The log-growth is defined there. -/
def Feasible (β : Bet) (f : ℝ) : Prop := -1 / β.b < f ∧ f < 1

/-- Any admissible fraction makes `winWealth` strictly positive. -/
lemma winWealth_pos_of_feasible (β : Bet) (f : ℝ) (hf : Feasible β f) :
    0 < winWealth β f :=
  winWealth_pos β f hf.1

/-- Any admissible fraction makes `loseWealth` strictly positive. -/
lemma loseWealth_pos_of_feasible (β : Bet) (f : ℝ) (hf : Feasible β f) :
    0 < loseWealth β f :=
  loseWealth_pos β f hf.2

end KellyLean_en
