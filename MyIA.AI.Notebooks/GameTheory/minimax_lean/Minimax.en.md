# `minimax_lean` — English documentation companion

> **Convention — issue #4980, user decision 2026-07-02 (option B).**
> The `.lean` source files (`lakefile.lean`, `Minimax.lean`, `Minimax/ZeroSum.lean`,
> `Minimax/Concavity.lean`, `Minimax/SionApplication.lean`) are the **canonical French**
> documentation — the single source of truth, unchanged. This file is the **English
> companion**: a non-compiled Markdown mirror of the same docstrings, translated. It
> follows the `README.md` → `README.en.md` pattern of Epic #1650 (pilot: sudoku_lean
> #4998; rollout: finiteness #5000, kelly #5003, erc20 #5007).
>
> - **Zero build cost** (Markdown is not compiled by `lake`), **zero risk** to
>   compilation — the `.lean` files are untouched.
> - **Source of truth = the `.lean`**. If the two ever disagree, the French in the
>   `.lean` wins; this companion mirrors the source and is regenerated against it.
>   Section order below matches declaration order in each file so drift is easy to spot.
> - Tactical `--` comments (inline, developer-facing, proof-tactic-bound) are
>   French-only in the source by convention and are **not** mirrored here — they are
>   tied to the Lean tactic language and add noise if duplicated.

---

## `lakefile.lean` — module

# Lean pedagogical mini-project: von Neumann minimax theorem (zero-sum games)

A Lean 4 project (with Mathlib) proving **von Neumann's minimax theorem** for finite
zero-sum games: for any payoff matrix `A` (m × n), optimal mixed strategies exist and
the value of the game satisfies

    maxₓ minᵧ xᵀ A y = minᵧ maxₓ xᵀ A y

(`x` ranges over the simplex of the row player's mixed strategies, `y` over the
column player's). See issue #4054 (Lean roadmap #4038).

The theorem follows from **Sion's minimax** (Mathlib `Topology.Sion`), whose
bilinear case on compact convex simplexes yields exactly von Neumann: the payoff
`xᵀ A y` is **affine in each variable**, hence (i) continuous ⟹ upper and lower
semicontinuous, (ii) affine ⟹ quasiconvex and quasiconcave — the four hypotheses
of `Sion.exists_isSaddlePointOn'`.

**Reassessed feasibility**: issue #4054 classified this theorem "MEDIUM-HARD"
assuming one would have to prove Sion/Kakutani by hand. Mathlib `v4.31.0-rc1`
provides `Sion.exists_isSaddlePointOn'` + `stdSimplex` (compact convex): the full
theorem is thus achievable **0 sorry**, the work being to wire the
bilinearity/convexity of the payoff on the simplexes — honestly documented as the
core of the formalization.

Companion notebook (`GameTheory` series): pedagogical presentation of zero-sum
games. Wiring the notebook is the responsibility of the GameTheory series owner
(convention of the sibling lakes: the lake is the formal deliverable, `lake build`
is the execution proof).

---

## `Minimax.lean`

### Module

# minimax_lean — bilinearity of the payoff for von Neumann's minimax theorem

A Lean 4 lake (Mathlib) at the root of the **zero-sum** specialization of the
`GameTheory` series, formalizing the analytic foundation of **von Neumann's
minimax theorem** for finite zero-sum games:

    maxₓ minᵧ xᵀ A y = minᵧ maxₓ xᵀ A y

(`x` ranges over the simplex of the row player's mixed strategies, `y` over the
column player's). See issue #4054 (roadmap Lean #4038).

#### Formalization strategy (from Mathlib `Topology.Sion`)

The full theorem follows from **Sion's minimax** (`Sion.exists_isSaddlePointOn'`),
whose bilinear case on compact convex simplexes yields exactly von Neumann. Sion's
hypotheses for `f = payoff A` on `X = stdSimplex ℝ m`, `Y = stdSimplex ℝ n` are:
- `IsCompact`/`Convex`/`Nonempty` of the simplexes (Mathlib facts on `stdSimplex`);
- `UpperSemicontinuousOn`/`LowerSemicontinuousOn` — since `payoff` is **continuous**;
- `QuasiconcaveOn`/`QuasiconvexOn` — since `payoff` is **affine in each variable**.

This first deliverable establishes the **formal core**: the bilinearity of the
payoff, which carries these four hypotheses.

- `Minimax/ZeroSum.lean` — payoff matrix, bilinear payoff `xᵀ A y = Σᵢⱼ xᵢ Aᵢⱼ yⱼ`,
  additivity + homogeneity in each variable (`payoff_add_in_x`, `payoff_smul_in_x`,
  `payoff_add_in_y`, `payoff_smul_in_y`), joint and restricted continuity
  (`continuous_payoff`, `continuous_payoff_in_x`, `continuous_payoff_in_y`). **0 sorry.**
- `Minimax/Concavity.lean` — **Sion glue (iterations 1 & 2)**: concavity/convexity of
  the payoff on the simplexes (`payoff_concave_in_x`, `payoff_convex_in_x`, and in
  `y`), then quasiconcavity/quasiconvexity via the Mathlib bridges
  (`payoff_quasiconcave_in_y`, `payoff_quasiconvex_in_x`) — iteration 1: 2 of the 4
  analytic hypotheses of `Sion.exists_isSaddlePointOn'`. **Iteration 2**:
  semicontinuity derived from continuity (`payoff_lowerSemicontinuous_in_x`,
  `payoff_upperSemicontinuous_in_y`) — the **2 remaining hypotheses**.
  **All 4 analytic hypotheses are now proven. 0 sorry.**
- `Minimax/SionApplication.lean` — **iteration 3 of the Sion glue**: non-emptiness of
  the simplexes (`stdSimplex_nonempty_m/n` via `single_mem_stdSimplex`) then the
  **final application** `exists_saddle_point_payoff` — the von Neumann theorem
  (saddle-point form) proven in one application of `Sion.exists_isSaddlePointOn`
  gathering the 4 analytic hypotheses + compactness `isCompact_stdSimplex` +
  convexity `convex_stdSimplex` + non-emptiness. The topological `Pi`-over-`ℝ`
  instances (`TopologicalSpace`, `AddCommGroup`, `Module ℝ`,
  `IsTopologicalAddGroup`, `ContinuousSMul ℝ`) synthesize from Mathlib.
  **Milestone #4054 RESOLVED. 0 sorry.**

#### Milestone — RESOLVED (#4054)

von Neumann's minimax theorem (saddle-point form) is now **proven 0-sorry** via
`Minimax/SionApplication.lean` (`exists_saddle_point_payoff`): for any payoff matrix
`A` over non-empty finite types, there exist `a ∈ Δₘ`, `b ∈ Δₙ` such that
`payoff A a y ≤ payoff A x b` for all `x ∈ Δₘ`, `y ∈ Δₙ`. Proven in one application
of `Sion.exists_isSaddlePointOn` (real case, `Topology/Sion.lean`), gathering the 4
analytic hypotheses from `Concavity.lean` (quasiconvexity in `x`, quasiconcavity in
`y`, lower semicontinuity in `x`, upper in `y`) with the
compactness/convexity/non-emptiness of the simplexes (Mathlib facts
`isCompact_stdSimplex`/`convex_stdSimplex`/`single_mem_stdSimplex`).

### `Status`

Status marker: von Neumann's minimax theorem (saddle-point form) is **proven
0-sorry** via `Minimax/SionApplication.lean`. Milestone #4054 RESOLVED.

---

## `Minimax/ZeroSum.lean`

### Module

# Minimax.ZeroSum — finite zero-sum games: matrix, mixed strategies, payoff

A finite two-player zero-sum game: the row player picks a row `i`, the column
player a column `j`, and the row player receives payoff `A i j` (the column player
receives `-A i j`). In **mixed strategies**, each player draws from a probability
distribution; the row player's expected payoff is the **bilinear payoff**
`xᵀ A y = Σᵢⱼ xᵢ Aᵢⱼ yⱼ`, where `x` and `y` are points of the probability simplex
(`stdSimplex`).

This module sets up the definitions and proves the **bilinearity** of the payoff
(key to applying Sion): `payoff` is affine in each variable separately, hence both
continuous and quasiconvex/quasiconcave — exactly the hypotheses of
`Sion.exists_isSaddlePointOn'` (see `Minimax.lean`).

Cross-reference: the `GameTheory` series (Nash already exists via
`lean_game_defs/Nash.lean`, of which this lake is the zero-sum specialization).
See issue #4054.

### `PayoffMatrix`

The payoff matrix of a zero-sum game (rows = row player, columns = column
player). `A i j` = row player's payoff when `i` plays row `i`, `j` plays column
`j`.

### `payoff`

The **bilinear expected payoff**: `payoff A x y = Σᵢⱼ xᵢ · Aᵢⱼ · yⱼ` (sum over the
product `m × n`). This is the row player's expected payoff under the mixed
strategies `x` (rows) and `y` (columns). Representing it as a **single sum over the
product** makes bilinearity immediate (`sum_add_distrib` / `sum_mul` in one step).

### `payoff_add_in_x`

**Additivity in `x`**: the payoff is additive in the row player's strategy (first
half of linearity).

### `payoff_smul_in_x`

**Homogeneity in `x`**: the payoff is homogeneous in the row player's strategy
(second half of linearity).

### `payoff_add_in_y`

**Additivity in `y`**: the payoff is additive in the column player's strategy
(first half of linearity in `y`).

### `payoff_smul_in_y`

**Homogeneity in `y`**: the payoff is homogeneous in the column player's strategy
(second half of linearity in `y`).

### `continuous_payoff`

The payoff is **continuous** (jointly), as a finite sum of continuous monomials.
This is the key fact that yields, by restriction, the upper and lower
semicontinuity required by Sion.

### `continuous_payoff_in_x`

The payoff `payoff A · y` is **continuous** in the row player's strategy (special
case of `continuous_payoff`, by restricting `y` = constant).

### `continuous_payoff_in_y`

The payoff `payoff A x ·` is **continuous** in the column player's strategy
(special case of `continuous_payoff`, by restricting `x` = constant).

---

## `Minimax/Concavity.lean`

### Module

# Minimax.Concavity — concavity/convexity of the payoff (iteration 1 of the Sion glue)

**Sion's** minimax theorem (classical case) requires, for the payoff
`f = payoff A` on the simplexes `X = stdSimplex ℝ m`, `Y = stdSimplex ℝ n`:
- `f(x, ·)` **quasiconcave** in `y` for all `x`;
- `f(·, y)` **quasiconvex** in `x` for all `y`.

Now the payoff is **linear** (hence affine) in each variable separately — this is
the bilinearity proven in `ZeroSum.lean` (`payoff_add_in_x`, `payoff_smul_in_x`,
`payoff_add_in_y`, `payoff_smul_in_y`). A linear function is both **concave and
convex** (Jensen's inequality holds with **equality**). This module formalizes that
fact: `payoff A · y` is `ConcaveOn`/`ConvexOn` on the simplex, and likewise in `y`,
then (iteration 2) derives the exact `QuasiconcaveOn`/`QuasiconvexOn` required by
`Sion.exists_isSaddlePointOn'`.

This is **iteration 1 of the Sion glue** (milestone #4054): via the Mathlib bridges
`ConcaveOn.quasiconcaveOn` / `ConvexOn.quasiconvexOn`, we obtain 2 of Sion's 4
hypotheses. The final application (compactness `isCompact_stdSimplex` +
semicontinuity from `continuous_payoff` + this) remained the OPEN milestone.
Module **entirely 0-sorry**.

**Iteration 2**: derives Sion's 2 **semicontinuity** hypotheses
(`LowerSemicontinuousOn` in `x`, `UpperSemicontinuousOn` in `y`) from
`continuous_payoff_in_x` / `continuous_payoff_in_y` (`ZeroSum.lean`) via the bridges
`Continuous.lowerSemicontinuous` / `Continuous.upperSemicontinuous` then
`.lowerSemicontinuousOn` / `.upperSemicontinuousOn`. Sion's **4 analytic
hypotheses** are now proven (quasiconcave/quasiconvex + LSC/USC); the OPEN
milestone that remained: `Pi`-over-`ℝ` instances + non-empty `stdSimplex` + the
final application of `Sion.minimax'`.

### `payoff_concave_in_x`

The payoff is **concave in `x`** on the simplex (linearity ⟹ concavity, Jensen's
inequality holding with equality: `payoff_smul_in_x` gives the scalar
multiplication `a * payoff A x y`, and `smul_eq_mul` normalizes the `•` in the
`ConcaveOn` goal).

### `payoff_convex_in_x`

The payoff is **convex in `x`** on the simplex (a linear function is both concave
and convex).

### `payoff_concave_in_y`

The payoff is **concave in `y`** on the simplex.

### `payoff_convex_in_y`

The payoff is **convex in `y`** on the simplex.

### `payoff_quasiconcave_in_y`

**Quasiconcavity in `y`** (iteration 2 of the Sion glue): via the Mathlib bridge
`ConcaveOn.quasiconcaveOn`, required by `Sion.exists_isSaddlePointOn'` (hypothesis
`f(x, ·)` quasiconcave).

### `payoff_quasiconvex_in_x`

**Quasiconvexity in `x`** (iteration 2 of the Sion glue): via the Mathlib bridge
`ConvexOn.quasiconvexOn`, required by `Sion.exists_isSaddlePointOn'` (hypothesis
`f(·, y)` quasiconvex).

### Iteration 2 — semicontinuity (Sion's 2 remaining hypotheses)

The 4 analytic hypotheses of `Sion.minimax'` (`Mathlib/Topology/Sion.lean`):
- `hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X (f · y)` — **proven** (`payoff_quasiconvex_in_x`);
- `hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y (f x ·)` — **proven** (`payoff_quasiconcave_in_y`);
- `hfy : ∀ y ∈ Y, LowerSemicontinuousOn (f · y) X` — **proven below**;
- `hfx : ∀ x ∈ X, UpperSemicontinuousOn (f x ·) Y` — **proven below**.

A continuous function is both lower and upper semicontinuous
(`Continuous.lowerSemicontinuous` / `Continuous.upperSemicontinuous`), and
restriction to a subset goes through `.lowerSemicontinuousOn` /
`.upperSemicontinuousOn`. The payoff is continuous in each variable
(`continuous_payoff_in_x` / `continuous_payoff_in_y`), giving the two hypotheses.

### `payoff_lowerSemicontinuous_in_x`

**Lower semicontinuity in `x`** (iteration 2): `f(·, y)` is
`LowerSemicontinuousOn` on the simplex — continuity ⟹ LSC, required by
`Sion.minimax'` (hyp `hfy : ∀ y ∈ Y, LowerSemicontinuousOn (f · y) X`).

### `payoff_upperSemicontinuous_in_y`

**Upper semicontinuity in `y`** (iteration 2): `f(x, ·)` is
`UpperSemicontinuousOn` on the simplex — continuity ⟹ USC, required by
`Sion.minimax'` (hyp `hfx : ∀ x ∈ X, UpperSemicontinuousOn (f x ·) Y`).

---

## `Minimax/SionApplication.lean`

### Module

# Minimax.SionApplication — final application of Sion (iteration 3 of the Sion glue)

This module wires the **4 analytic hypotheses** proven in `Concavity.lean`
(quasiconvexity in `x`, quasiconcavity in `y`, lower semicontinuity in `x`, upper
in `y`) with Mathlib's topological facts on `stdSimplex` (compactness
`isCompact_stdSimplex`, convexity `convex_stdSimplex`, non-emptiness via
`single_mem_stdSimplex`) to prove the existence of a saddle point via
`Sion.exists_isSaddlePointOn` (real case) — the **final milestone** of #4054.

Sion's 5 topological prerequisites on `E = m → ℝ` (and `F = n → ℝ`) are
`TopologicalSpace`, `AddCommGroup`, `Module ℝ`, `IsTopologicalAddGroup`,
`ContinuousSMul ℝ`: they synthesize from Mathlib's `Pi` instances
(`Pi.topologicalSpace`, `Pi.instAddCommGroup`, `Pi.instModule`, etc.). This
**iteration 3** module delivers the auxiliary fact of **non-emptiness of the
simplex** then the **final application**.

`IsSaddlePointOn` lives at the top level (`Mathlib/Order/SaddlePoint.lean`), while
`exists_isSaddlePointOn` is in `namespace Sion`.

### `stdSimplex_nonempty_m`

The standard simplex `stdSimplex ℝ m` is non-empty as soon as `m` is non-empty: the
Dirac `Pi.single i 1` (mass 1 at index `i`, 0 elsewhere) is a point of the simplex,
via the Mathlib lemma `single_mem_stdSimplex`.

### `stdSimplex_nonempty_n`

Variant in `y`: `stdSimplex ℝ n` is non-empty as soon as `n` is non-empty.

### `exists_saddle_point_payoff`

**von Neumann minimax theorem (saddle-point form)** — the **final milestone** of
issue #4054: for any payoff matrix `A` over non-empty finite types, there exist
mixed strategies `a ∈ Δₘ`, `b ∈ Δₙ` such that `payoff A a y ≤ payoff A x b` for all
`x ∈ Δₘ`, `y ∈ Δₙ` (saddle point). Proven in one application of
`Sion.exists_isSaddlePointOn` (real case, `Topology/Sion.lean` section `Real`),
gathering:
- compactness: `isCompact_stdSimplex ℝ`;
- convexity: `convex_stdSimplex ℝ`;
- non-emptiness: `stdSimplex_nonempty_m` / `stdSimplex_nonempty_n` (lemmas above);
- the 4 analytic hypotheses of `Concavity.lean` (quasiconvexity in `x`,
  quasiconcavity in `y`, lower semicontinuity in `x`, upper in `y`).

Sion's 5 topological prerequisites on `E = m → ℝ` and `F = n → ℝ`
(`TopologicalSpace`, `AddCommGroup`, `Module ℝ`, `IsTopologicalAddGroup`,
`ContinuousSMul ℝ`) synthesize from Mathlib's `Pi` instances.
