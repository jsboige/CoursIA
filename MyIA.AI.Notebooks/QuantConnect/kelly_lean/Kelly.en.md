# `kelly_lean` — English documentation companion

> **Convention — issue #4980, user decision 2026-07-02 (option B).**
> The `.lean` source files (`lakefile.lean`, `Kelly/Bet.lean`,
> `Kelly/Growth.lean`, `Kelly/Kelly.lean`) are the **canonical French**
> documentation — the single source of truth, unchanged. This file is the
> **English companion**: a non-compiled Markdown mirror of the same docstrings,
> translated. It follows the `README.md` → `README.en.md` pattern of Epic #1650
> (pilot: sudoku_lean #4998; rollout tranche 1: finiteness_lean #5000).
>
> - **Zero build cost** (Markdown is not compiled by `lake`), **zero risk** to
>   compilation — the `.lean` files are untouched.
> - **Source of truth = the `.lean`**. If the two ever disagree, the French in
>   the `.lean` wins; this companion mirrors the source and is regenerated
>   against it. Section order below matches declaration order in each file so
>   drift is easy to spot.
> - Tactical `--` comments (inline, developer-facing, proof-tactic-bound) are
>   French-only in the source by convention and are **not** mirrored here — they
>   are tied to the Lean tactic language and add noise if duplicated.

---

## `lakefile.lean` — module

# Lean pedagogical mini-project: Kelly criterion (optimality of log-growth)

A Lean 4 project (with Mathlib) proving the **optimality of the Kelly criterion**
for position sizing: for a Bernoulli bet (probability `p` of winning, net odds
`b`), the optimal fraction of capital to risk is

    f* = (b·p − q) / b        (q = 1 − p)

which **uniquely maximizes** the expected growth rate `g(f) = p·log(1 + b·f)
+ q·log(1 − f)`. Over-betting (`f > f*`) and under-betting (`f < f*`) are
strictly suboptimal. See issue #4052 (Lean roadmap #4038, Tier 2).

**Why here**: the Kelly criterion grounds **position sizing** (central to the
trading taught in the QuantConnect series) and ties the trading series to a
clean, provable mathematical result.

**Feasibility**: `Real.log` is strictly concave on `(0, ∞)` (`StrictConcaveOn`
in Mathlib); `g(f)` is strictly concave as a convex combination of strictly
concave affine compositions. The first-order condition `g'(f*) = 0` + strict
concavity ⟹ `f*` is the **unique maximizer**. Standard real calculus,
achievable **0 sorry** on the flagship theorem `kelly_optimal`.

Companion notebook (QuantConnect series): pedagogical presentation of position
sizing / Kelly (Python, Lean + Python side by side). Wiring the notebook is the
responsibility of the QuantConnect series owner (convention of the sibling
lakes: the lake is the formal deliverable, `lake build` is the proof of
execution).

---

## `Kelly/Bet.lean`

### Module

# Kelly.Bet — Bernoulli bet, bet fraction, wealth multipliers

A **Bernoulli bet** (the canonical setting of the Kelly criterion): with
probability `p` one wins and receives `b` times the stake `f` (net odds `b`),
with probability `q = 1 − p` one loses the stake. The relative wealth after the
bet is:
- **`1 + b·f`** on a win (capital + profit `b·f`),
- **`1 − f`** on a loss (capital − stake `f`).

The **bet fraction** `f` lives in the open interval `(−1/b, 1)`: in this range
both multipliers are strictly positive (log-growth is defined). A negative
fraction = betting *against* the player (short), `f = 0` = bet nothing.

This module sets up the model. The optimal fraction `f*` and the flagship
theorem live in `Kelly.lean`. See issue #4052.

### `Bet`

A Bernoulli bet parameterized by its win probability `p` and its net odds `b`.

### `Bet.p`

Win probability, strictly between 0 and 1.

### `Bet.b`

Net odds: profit `b` per unit staked on a win, `b > 0`.

### `q`

Loss probability, `q = 1 − p`.

### `q_pos`

The loss probability is strictly positive (since `p < 1`).

### `q_lt_one`

The loss probability is strictly less than 1 (since `p > 0`).

### `pq_add_eq_one`

The probabilities sum to 1: `p + q = 1`.

### `winWealth`

Wealth multiplier on a **win**: `1 + b·f` (capital + profit `b·f`).

### `loseWealth`

Wealth multiplier on a **loss**: `1 − f` (capital − stake `f`). The body does
not depend on the odds `β.b` (losing one's stake is universal), but `β` is kept
as a parameter for API symmetry with `winWealth`. The option silences the
`unusedVariables` linter (intentional: symmetric API).

### `b_add_one_pos`

The net odds satisfy `b + 1 > 0` (useful for domains).

### `winWealth_pos`

`winWealth` is strictly positive on the admissible zone `f > −1/b`.

### `loseWealth_pos`

`loseWealth` is strictly positive on the admissible zone `f < 1`.

### `Feasible`

**Admissible zone** of a fraction `f`: both multipliers are strictly positive,
i.e. `f ∈ (−1/b, 1)`. Log-growth is defined there.

### `winWealth_pos_of_feasible`

Any admissible fraction makes `winWealth` strictly positive.

### `loseWealth_pos_of_feasible`

Any admissible fraction makes `loseWealth` strictly positive.

---

## `Kelly/Growth.lean`

### Module

# Kelly.Growth — the expected growth rate `g(f) = E[log(wealth)]`

The **expected growth rate** of a Bernoulli bet under fraction `f` is

    g(f) = p · log(1 + b·f) + q · log(1 − f)

where `p` (resp. `q`) is the win (resp. loss) probability and `b` the net odds.
Maximizing `g` amounts to maximizing the **asymptotic growth of compounded
capital** over infinitely many independent bets (this is the Kelly optimum). See
issue #4052.

This module defines `growth` and `growthGrad`, and establishes the baseline
**fundamental facts** (zero growth without betting, slope at the origin = the
edge). The strict concavity of `g` on the admissible zone (seen by computing
`g''(f) < 0`) is the proof strategy **bypassed** by the flagship optimality
theorem, which proves `g(f) ≤ g(f*)` directly via the tangent `log t ≤ t − 1`
rather than invoking abstract concavity — that flagship lives in `Kelly.lean`.

### `growth`

The **expected growth rate** `g(f) = p·log(1 + b·f) + q·log(1 − f)`:
expectation of the logarithm of relative wealth.

### `growthGrad`

The **slope** (derivative) of the growth rate: `g'(f) = p·b/(1+bf) − q/(1−f)`.
This is the quantity whose vanishing characterizes the optimal fraction. It is
exposed explicitly because it is at the heart of the optimality theorem
(first-order condition `growthGrad β f* = 0`).

### `growth_zero`

**Zero growth without betting**: `g(0) = 0`. Betting nothing (`f = 0`) leaves
capital unchanged — both wealth multipliers equal `1`, and `log 1 = 0`. This is
the **baseline** of the Kelly criterion: any fraction `f` with `g(f) > 0` beats
"doing nothing", any fraction with `g(f) < 0` is worse (cf `Kelly.kelly_optimal`,
which guarantees `g(f) ≤ g(f*)` and, the edge being positive, `g(f*) > 0 = g(0)`).

### `growthGrad_zero`

**Slope at the origin = the edge**: `g'(0) = b·p − q`. With no stake (`f = 0`),
the slope of log-growth is exactly the "edge" `b·p − q` — i.e. the **numerator**
of the Kelly fraction `f* = (b·p − q)/b`. Thus `g'(0) > 0` ⟺ `f* > 0` (favorable
bet, bet), `g'(0) < 0` ⟺ `f* < 0` (unfavorable bet, short). This is the bridge
between the local geometry of `g` (its slope at 0) and the direction of the
optimal bet.

---

## `Kelly/Kelly.lean`

### Module

# Kelly.Kelly — optimality of the fraction `f* (Kelly criterion)

The **Kelly theorem**: the optimal fraction to bet on a Bernoulli bet (win
probability `p`, net odds `b`) is

    f* = (b·p − q) / b        (q = 1 − p)

which **uniquely maximizes** the expected growth rate `g(f) = p·log(1+bf) +
q·log(1−f)`. Any over-bet (`f > f*`) or under-bet (`f < f*`) is strictly
suboptimal.

#### Proof strategy

We avoid abstract concavity and prove `g(f) ≤ g(f*)` **directly** via the
logarithm tangent at 1, `log t ≤ t − 1` (with equality iff `t = 1`). Writing

    g(f) − g(f*) = p · log((1+bf)/(1+bf*)) + q · log((1−f)/(1−f*))

and applying `log t ≤ t − 1` to each ratio, we get

    g(f) − g(f*) ≤ (f − f*) · [p·b/(1+bf*) − q/(1−f*)] = (f − f*) · g'(f*).

Now `g'(f*) = 0` (first-order condition, verified by computation). Hence
`g(f) ≤ g(f*)`. Uniqueness follows from the strict version `log t < t − 1` for
`t ≠ 1`: if `f ≠ f*`, the ratios differ from `1`, so the inequalities are
strict, and `g(f) < g(f*)`.

Reference: J. L. Kelly Jr., *A New Interpretation of Information Rate*, BSTT
(1956). See issue #4052.

### `kellyFrac`

The **Kelly fraction** `f* = (b·p − q)/b` (the optimal stake per unit of
capital).

### `kellyFrac_feasible`

The Kelly fraction lies in the admissible zone `(−1/b, 1)`: both wealth
multipliers at `f*` are strictly positive.

### `winWealth_kelly`

Win multiplier evaluated at `f*`: `winWealth β f* = p · (b + 1)`.

### `loseWealth_kelly`

Loss multiplier evaluated at `f*`: `loseWealth β f* = q · (b + 1) / b`.

### `growthGrad_kelly_zero`

**First-order condition**: the slope of log-growth vanishes at `f*`,
`g'(f*) = growthGrad β f* = 0`.

### `growth_diff_le`

**Key bound**: for any admissible fraction `f`,
`g(f) − g(f*) ≤ (f − f*) · g'(f*)`. Follows from `log t ≤ t − 1` applied to both
ratios.

### `kelly_optimal`

**Kelly theorem** (maximizer): `f*` maximizes the expected growth rate. For any
admissible fraction `f`, `g(f) ≤ g(f*)`.

### `kelly_unique`

**Over-bet and under-bet are strictly suboptimal**: if `f ≠ f*` is admissible,
then `g(f) < g(f*)` (uniqueness of the maximizer). Follows from `log t < t − 1`
for `t ≠ 1`.
