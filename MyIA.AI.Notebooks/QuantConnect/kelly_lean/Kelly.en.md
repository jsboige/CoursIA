# Kelly — English documentation companion

> **Convention.** This file is the **English translation of docstrings** in the
> `kelly_lean` lake. It is a **non-compiled Markdown companion** to the Lean 4
> sources — the **French `.lean` source remains the single source of truth** and
> is unchanged. Tactical `--` comments inside proof bodies are **not** mirrored
> (they remain French-only, tactic-bound). Module docstrings (`/-! ... -/`) and
> per-declaration docstrings (`/-- ... -/`) are translated.
>
> Source lake: [`MyIA.AI.Notebooks/QuantConnect/kelly_lean/`](./).
> Companion convention: PR #4980 rollout, option B (user decision 2026-07-02),
> pilot = PR #4998 (sudoku_lean). See #1650 (multilingual documentation EPIC).

---

## `lakefile.lean` — package manifest

**Module docstring (translated).**

A pedagogical Lean 4 mini-project (with Mathlib) proving the **optimality of the Kelly criterion** for position sizing: for a Bernoulli bet (winning probability `p`, net odds `b`), the optimal fraction of capital to wager is

    f* = (b·p − q) / b        (q = 1 − p)

which **uniquely maximizes** the expected growth rate `g(f) = p·log(1+bf) + q·log(1−f)`. Over-bets (`f > f*`) and under-bets (`f < f*`) are strictly suboptimal. See issue #4052 (Lean roadmap #4038, Tier 2).

**Why here**: the Kelly criterion grounds **position sizing** (at the heart of trading taught in the QuantConnect series), and ties the trading series to a clean, provable mathematical result.

**Feasibility**: `Real.log` is strictly concave on `(0, ∞)` (`StrictConcaveOn` in Mathlib); `g(f)` is strictly concave as a convex combination of strictly-concave affine compositions. The first-order condition `g'(f*) = 0` plus strict concavity ⟹ `f*` is the **unique maximizer**. Standard real-calculus argument, attainable at **0 sorry** on the flagship theorem `kelly_optimal`.

Companion notebook (QuantConnect series): pedagogical presentation of position sizing / Kelly (Python, Lean + Python side by side). The notebook wiring belongs to the QuantConnect series owner (sibling-lake convention: the lake is the formal deliverable, the `lake build` is the proof of execution).

---

## `Kelly/Bet.lean` — Bernoulli bet, wagered fraction, wealth multipliers

**Module docstring (translated).**

A **Bernoulli bet** (the canonical framework of the Kelly criterion): with probability `p` one wins and receives `b` times the wager `f` (net odds `b`); with probability `q = 1 − p` one loses the wager. The relative wealth after the bet is:
- **`1 + b·f`** in the win case (capital + profit `b·f`),
- **`1 − f`** in the loss case (capital − wager `f`).

The **wagered fraction** `f` lives in the open interval `(−1/b, 1)`: below that threshold both multipliers are strictly positive (the log-growth is defined). A negative fraction = a bet *against* the player (short); `f = 0` = bet nothing.

This module sets up the model. The optimal fraction `f*` and the flagship theorem live in `Kelly.lean`. See issue #4052.

### `Bet` — structure

A Bernoulli bet parameterized by its win probability `p` and its net odds `b`.

- **`p : ℝ`** — win probability, strictly between 0 and 1.
- **`hp_pos : 0 < p`** — witness that `p > 0`.
- **`hp_lt_one : p < 1`** — witness that `p < 1`.
- **`b : ℝ`** — net odds: profit `b` per unit wagered in the win case, `b > 0`.
- **`hb_pos : 0 < b`** — witness that `b > 0`.

### `q` — definition

The loss probability `q = 1 − p`.

### `q_pos` — lemma

The loss probability is strictly positive (because `p < 1`).

### `q_lt_one` — lemma

The loss probability is strictly less than 1 (because `p > 0`).

### `pq_add_eq_one` — lemma

Probabilities sum to 1: `p + q = 1`.

### `winWealth` — definition

Wealth multiplier in the **win** case: `1 + b·f` (capital + profit `b·f`).

### `loseWealth` — definition

Wealth multiplier in the **loss** case: `1 − f` (capital − wager `f`).

### `b_add_one_pos` — lemma

The net odds satisfy `b + 1 > 0` (useful for domains).

### `winWealth_pos` — lemma

`winWealth` is strictly positive on the admissible zone `f > −1/b`.

### `loseWealth_pos` — lemma

`loseWealth` is strictly positive on the admissible zone `f < 1`.

### `Feasible` — definition

**Admissible zone** of a fraction `f`: both multipliers are strictly positive, i.e. `f ∈ (−1/b, 1)`. The log-growth is defined there.

### `winWealth_pos_of_feasible` — lemma

Any admissible fraction makes `winWealth` strictly positive.

### `loseWealth_pos_of_feasible` — lemma

Any admissible fraction makes `loseWealth` strictly positive.

---

## `Kelly/Growth.lean` — expected growth rate `g(f) = E[log(wealth)]`

**Module docstring (translated).**

The **expected growth rate** of a Bernoulli bet under the fraction `f` is

    g(f) = p · log(1 + b·f) + q · log(1 − f)

where `p` (resp. `q`) is the win (resp. loss) probability and `b` the net odds. Maximizing `g` amounts to maximizing the **asymptotic growth of compounded capital** over an infinity of independent bets — this is the Kelly optimality. See issue #4052.

This module defines `growth` and `growthGrad`, and establishes the **fundamental baseline facts** (zero growth without a bet, slope at the origin = the edge). The strict concavity of `g` on the admissible zone (seen by direct calculation `g''(f) < 0`) is the proof strategy **bypassed** by the flagship optimality theorem, which proves `g(f) ≤ g(f*)` directly via the tangent-line inequality `log t ≤ t − 1` rather than invoking abstract concavity — that flagship lives in `Kelly.lean`.

### `growth` — definition

The **expected growth rate** `g(f) = p·log(1 + b·f) + q·log(1 − f)`: expectation of the logarithm of the relative wealth.

### `growthGrad` — definition

The **slope** (derivative) of the growth rate: `g'(f) = p·b/(1+bf) − q/(1−f)`. This is the quantity whose vanishing characterizes the optimal fraction. It is exposed explicitly because it is at the heart of the optimality theorem (first-order condition `growthGrad β f* = 0`).

### `growth_zero` — lemma

**Zero growth without a bet**: `g(0) = 0`. Betting nothing (`f = 0`) leaves capital unchanged — both wealth multipliers equal `1`, and `log 1 = 0`. This is the **baseline** of the Kelly criterion: any fraction `f` with `g(f) > 0` beats the "do nothing" baseline, any fraction with `g(f) < 0` is below it (cf. `Kelly.kelly_optimal`, which guarantees `g(f) ≤ g(f*)`, and — the edge being positive — `g(f*) > 0 = g(0)`).

### `growthGrad_zero` — lemma

**Slope at the origin equals the edge**: `g'(0) = b·p − q`. Without a wager (`f = 0`), the slope of the log-growth equals exactly the **edge** `b·p − q` — which is the **numerator** of the Kelly fraction `f* = (b·p − q)/b`. Hence `g'(0) > 0` ⟺ `f* > 0` (favorable bet, bet on it); `g'(0) < 0` ⟺ `f* < 0` (unfavorable bet, short it). This is the bridge between the local geometry of `g` (its slope at `0`) and the sign of the optimal wager.

---

## `Kelly/Kelly.lean` — optimality of the Kelly fraction `f*` (flagship)

**Module docstring (translated).**

The **Kelly theorem**: the optimal fraction to wager on a Bernoulli bet (win probability `p`, net odds `b`) is

    f* = (b·p − q) / b        (q = 1 − p)

which **uniquely maximizes** the expected growth rate `g(f) = p·log(1+bf) + q·log(1−f)`. Any over-bet (`f > f*`) or under-bet (`f < f*`) is strictly suboptimal.

**Proof strategy.** Abstract concavity is avoided and `g(f) ≤ g(f*)` is proved **directly** via the tangent line of the logarithm at 1, `log t ≤ t − 1` (with equality iff `t = 1`). Writing

    g(f) − g(f*) = p · log((1+bf)/(1+bf*)) + q · log((1−f)/(1−f*))

and applying `log t ≤ t − 1` to each ratio, we get

    g(f) − g(f*) ≤ (f − f*) · [p·b/(1+bf*) − q/(1−f*)] = (f − f*) · g'(f*).

Now `g'(f*) = 0` (first-order condition, verified by calculation). So `g(f) ≤ g(f*)`. Uniqueness follows from the strict version `log t < t − 1` for `t ≠ 1`: if `f ≠ f*`, the ratios differ from `1`, hence the inequalities are strict, and `g(f) < g(f*)`.

Reference: J. L. Kelly Jr., *A New Interpretation of Information Rate*, BSTT (1956). See issue #4052.

### `kellyFrac` — definition

The **Kelly fraction** `f* = (b·p − q)/b` (the optimal wager per unit of capital).

### `kellyFrac_feasible` — lemma

The Kelly fraction lies in the admissible zone `(−1/b, 1)`: both wealth multipliers at `f*` are strictly positive.

### `winWealth_kelly` — lemma

Win wealth multiplier evaluated at `f*`: `winWealth β f* = p · (b + 1)`.

### `loseWealth_kelly` — lemma

Loss wealth multiplier evaluated at `f*`: `loseWealth β f* = q · (b + 1) / b`.

### `growthGrad_kelly_zero` — lemma

**First-order condition**: the slope of the log-growth vanishes at `f*`, `g'(f*) = growthGrad β f* = 0`.

### `growth_diff_le` — lemma

**Key upper bound**: for any admissible fraction `f`, `g(f) − g(f*) ≤ (f − f*) · g'(f*)`. Follows from `log t ≤ t − 1` applied to the two ratios.

### `kelly_optimal` — theorem

**Kelly theorem (maximizer)**: `f*` maximizes the expected growth rate. For any admissible fraction `f`, `g(f) ≤ g(f*)`.

### `kelly_unique` — theorem

**Over-bets and under-bets are strictly suboptimal**: if `f ≠ f*` is admissible, then `g(f) < g(f*)` (uniqueness of the maximizer). Follows from the strict version `log t < t − 1` for `t ≠ 1`.