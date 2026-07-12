import Mathlib
import Minimax.ZeroSum_en

/-!
  Minimax.Concavity — concavity/convexity of the payoff (Sion glue iteration 1)
  =============================================================================

  English mirror of `Minimax/Concavity.lean` (FR-first canonical).
  Convention i18n Lean ratifiée par ai-01 (2026-07-04, #4980 comment-4881909354) :
  fichiers `.lean` distincts FR + EN siblings dans le même lake, les deux compilent.
  Drift-CI detectable : contenu non-docstring byte-identique entre siblings.

  Note méthodologique : traduction manuelle du FR canonique (pas de source
  EN historique pré-Option A à recover, fichier FR-first depuis origin).

  Sion's **minimax theorem** (classical case) requires, for the payoff
  `f = payoff A` on the simplices `X = stdSimplex ℝ m`,
  `Y = stdSimplex ℝ n`:
  - `f(x, ·)` **quasi-concave** in `y` for all `x`;
  - `f(·, y)` **quasi-convex** in `x` for all `y`.

  But the payoff is **linear** (hence affine) in each variable
  separately — this is the bilinearity proved in `ZeroSum.lean`
  (`payoff_add_in_x`, `payoff_smul_in_x`, `payoff_add_in_y`,
  `payoff_smul_in_y`). A linear function is both **concave and convex**
  (Jensen's inequality holds with **equality**). This module formalizes
  that fact: `payoff A · y` is `ConcaveOn` / `ConvexOn` on the simplex,
  and likewise in `y`, then (iteration 2) derives the exact
  `QuasiconcaveOn` / `QuasiconvexOn` required by
  `Sion.exists_isSaddlePointOn'`.

  This is **Sion glue iteration 1** (milestone #4054): via the Mathlib
  bridges `ConcaveOn.quasiconcaveOn` / `ConvexOn.quasiconvexOn`, we
  obtain 2 of the 4 hypotheses of Sion. The final application
  (compactness `isCompact_stdSimplex` + semicontinuity from
  `continuous_payoff` + this) remains the OPEN milestone that is
  documented. The module is **entirely 0-sorry**.

  **Iteration 2** derives the **semicontinuity** hypotheses of Sion
  (`LowerSemicontinuousOn` in `x`, `UpperSemicontinuousOn` in `y`) from
  `continuous_payoff_in_x` / `continuous_payoff_in_y` (`ZeroSum.lean`)
  via the bridges `Continuous.lowerSemicontinuous` /
  `Continuous.upperSemicontinuous` then `.lowerSemicontinuousOn` /
  `.upperSemicontinuousOn`. The **4 analytic hypotheses** of Sion are
  now proved (quasi-concave/quasi-convex + LSC/USC); what remains is the
  OPEN milestone: `Pi`-over-`ℝ` instances + non-empty `stdSimplex` +
  the final application `Sion.minimax'`.
-/

namespace MinimaxLean_en

open Finset Set

variable {m n : Type*} [Fintype m] [Fintype n]
variable (A : PayoffMatrix m n)

/-- The payoff is **concave in `x`** on the simplex (linearity ⟹
concavity, Jensen's inequality holding with equality: `payoff_smul_in_x`
gives the scalar multiplication `a * payoff A x y`, and `smul_eq_mul`
normalizes the `•` of the goal `ConcaveOn`). -/
theorem payoff_concave_in_x (y : n → ℝ) :
    ConcaveOn ℝ (stdSimplex ℝ m) fun x => payoff A x y := by
  refine ⟨convex_stdSimplex ℝ m, ?_⟩
  intro x _hx x' _hx' a b _ha _hb _hab
  dsimp only
  rw [payoff_add_in_x, payoff_smul_in_x, payoff_smul_in_x, smul_eq_mul, smul_eq_mul]

/-- The payoff is **convex in `x`** on the simplex (a linear function is
both concave and convex). -/
theorem payoff_convex_in_x (y : n → ℝ) :
    ConvexOn ℝ (stdSimplex ℝ m) fun x => payoff A x y := by
  refine ⟨convex_stdSimplex ℝ m, ?_⟩
  intro x _hx x' _hx' a b _ha _hb _hab
  dsimp only
  rw [payoff_add_in_x, payoff_smul_in_x, payoff_smul_in_x, smul_eq_mul, smul_eq_mul]

/-- The payoff is **concave in `y`** on the simplex. -/
theorem payoff_concave_in_y (x : m → ℝ) :
    ConcaveOn ℝ (stdSimplex ℝ n) fun y => payoff A x y := by
  refine ⟨convex_stdSimplex ℝ n, ?_⟩
  intro y _hy y' _hy' a b _ha _hb _hab
  dsimp only
  rw [payoff_add_in_y, payoff_smul_in_y, payoff_smul_in_y, smul_eq_mul, smul_eq_mul]

/-- The payoff is **convex in `y`** on the simplex. -/
theorem payoff_convex_in_y (x : m → ℝ) :
    ConvexOn ℝ (stdSimplex ℝ n) fun y => payoff A x y := by
  refine ⟨convex_stdSimplex ℝ n, ?_⟩
  intro y _hy y' _hy' a b _ha _hb _hab
  dsimp only
  rw [payoff_add_in_y, payoff_smul_in_y, payoff_smul_in_y, smul_eq_mul, smul_eq_mul]

/-- **Quasi-concavity in `y`** (Sion glue iteration 2): via the Mathlib
bridge `ConcaveOn.quasiconcaveOn`, required by
`Sion.exists_isSaddlePointOn'` (assumption `f(x, ·)` quasi-concave). -/
theorem payoff_quasiconcave_in_y (x : m → ℝ) :
    QuasiconcaveOn ℝ (stdSimplex ℝ n) fun y => payoff A x y :=
  (payoff_concave_in_y A x).quasiconcaveOn

/-- **Quasi-convexity in `x`** (Sion glue iteration 2): via the Mathlib
bridge `ConvexOn.quasiconvexOn`, required by
`Sion.exists_isSaddlePointOn'` (assumption `f(·, y)` quasi-convex). -/
theorem payoff_quasiconvex_in_x (y : n → ℝ) :
    QuasiconvexOn ℝ (stdSimplex ℝ m) fun x => payoff A x y :=
  (payoff_convex_in_x A y).quasiconvexOn

/-! ## Iteration 2 — semicontinuity (2 remaining Sion hypotheses)

The 4 analytic hypotheses of `Sion.minimax'` (`Mathlib/Topology/Sion.lean`):
- `hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X (f · y)` — **proved**
  (`payoff_quasiconvex_in_x`);
- `hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y (f x ·)` — **proved**
  (`payoff_quasiconcave_in_y`);
- `hfy : ∀ y ∈ Y, LowerSemicontinuousOn (f · y) X` — **proved below**;
- `hfx : ∀ x ∈ X, UpperSemicontinuousOn (f x ·) Y` — **proved below**.

A continuous function is both lower and upper semicontinuous
(`Continuous.lowerSemicontinuous` /
`Continuous.upperSemicontinuous`), and restriction to a subset passes
through `.lowerSemicontinuousOn` / `.upperSemicontinuousOn`. The payoff
is continuous in each variable (`continuous_payoff_in_x` /
`continuous_payoff_in_y`), whence the two hypotheses. -/

/-- **Lower semicontinuity in `x`** (iteration 2): `f(·, y)` is
`LowerSemicontinuousOn` on the simplex — continuity ⟹ LSC, required by
`Sion.minimax'` (hyp `hfy : ∀ y ∈ Y, LowerSemicontinuousOn (f · y) X`). -/
theorem payoff_lowerSemicontinuous_in_x (y : n → ℝ) :
    LowerSemicontinuousOn (fun x => payoff A x y) (stdSimplex ℝ m) :=
  (continuous_payoff_in_x A y).lowerSemicontinuous.lowerSemicontinuousOn (stdSimplex ℝ m)

/-- **Upper semicontinuity in `y`** (iteration 2): `f(x, ·)` is
`UpperSemicontinuousOn` on the simplex — continuity ⟹ USC, required by
`Sion.minimax'` (hyp `hfx : ∀ x ∈ X, UpperSemicontinuousOn (f x ·) Y`). -/
theorem payoff_upperSemicontinuous_in_y (x : m → ℝ) :
    UpperSemicontinuousOn (fun y => payoff A x y) (stdSimplex ℝ n) :=
  (continuous_payoff_in_y A x).upperSemicontinuous.upperSemicontinuousOn (stdSimplex ℝ n)

end MinimaxLean_en
