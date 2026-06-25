import Mathlib
import Minimax.ZeroSum

/-!
# Minimax.Concavity — concavité/cvxicité du payoff (itération 1 du glue Sion)

Le théorème minimax de **Sion** (cas classique) requiert, pour le payoff
`f = payoff A` sur les simplexes `X = stdSimplex ℝ m`, `Y = stdSimplex ℝ n` :
- `f(x, ·)` **quasi-concave** en `y` pour tout `x` ;
- `f(·, y)` **quasi-convexe** en `x` pour tout `y`.

Or le payoff est **linéaire** (donc affine) en chaque variable séparément — c'est
la bilinéarité prouvée dans `ZeroSum.lean` (`payoff_add_in_x`, `payoff_smul_in_x`,
`payoff_add_in_y`, `payoff_smul_in_y`). Une fonction linéaire est à la fois
**concave et convexe** (l'inégalité de Jensen tient avec **égalité**). Ce module
formalise ce fait : `payoff A · y` est `ConcaveOn`/`ConvexOn` sur le simplexe, et
idem en `y`, puis (itération 2) dérive les `QuasiconcaveOn`/`QuasiconvexOn` exacts
requis par `Sion.exists_isSaddlePointOn'`.

C'est l'**itération 1 du glue Sion** (milestone #4054) : via les ponts Mathlib
`ConcaveOn.quasiconcaveOn` / `ConvexOn.quasiconvexOn`, on obtient 2 des 4 hyps de
Sion. L'application finale (compacité `isCompact_stdSimplex` + semi-continuité
depuis `continuous_payoff` + ceci) reste le milestone OPEN documenté. Module
**entièrement 0-sorry**.

**Itération 2** : dérive les 2 hyps de **semi-continuité** de Sion
(`LowerSemicontinuousOn` en `x`, `UpperSemicontinuousOn` en `y`) depuis
`continuous_payoff_in_x` / `continuous_payoff_in_y` (`ZeroSum.lean`) via les ponts
`Continuous.lowerSemicontinuous` / `Continuous.upperSemicontinuous` puis
`.lowerSemicontinuousOn` / `.upperSemicontinuousOn`. Les **4 hyps analytiques** de
Sion sont désormais prouvées (quasi-concave/quasi-convexe + LSC/USC) ; reste le
milestone OPEN : instances `Pi`-sur-`ℝ` + `stdSimplex` non-vide + application
finale `Sion.minimax'`.
-/

namespace MinimaxLean

open Finset Set

variable {m n : Type*} [Fintype m] [Fintype n]
variable (A : PayoffMatrix m n)

/-- Le payoff est **concave en `x`** sur le simplexe (linéarité ⟹ concavité,
l'inégalité de Jensen tenant avec égalité : `payoff_smul_in_x` donne la multiplication
scalaire `a * payoff A x y`, et `smul_eq_mul` normalise le `•` du but `ConcaveOn`). -/
theorem payoff_concave_in_x (y : n → ℝ) :
    ConcaveOn ℝ (stdSimplex ℝ m) fun x => payoff A x y := by
  refine ⟨convex_stdSimplex ℝ m, ?_⟩
  intro x _hx x' _hx' a b _ha _hb _hab
  dsimp only
  rw [payoff_add_in_x, payoff_smul_in_x, payoff_smul_in_x, smul_eq_mul, smul_eq_mul]

/-- Le payoff est **convexe en `x`** sur le simplexe (une fonction linéaire est à
la fois concave et convexe). -/
theorem payoff_convex_in_x (y : n → ℝ) :
    ConvexOn ℝ (stdSimplex ℝ m) fun x => payoff A x y := by
  refine ⟨convex_stdSimplex ℝ m, ?_⟩
  intro x _hx x' _hx' a b _ha _hb _hab
  dsimp only
  rw [payoff_add_in_x, payoff_smul_in_x, payoff_smul_in_x, smul_eq_mul, smul_eq_mul]

/-- Le payoff est **concave en `y`** sur le simplexe. -/
theorem payoff_concave_in_y (x : m → ℝ) :
    ConcaveOn ℝ (stdSimplex ℝ n) fun y => payoff A x y := by
  refine ⟨convex_stdSimplex ℝ n, ?_⟩
  intro y _hy y' _hy' a b _ha _hb _hab
  dsimp only
  rw [payoff_add_in_y, payoff_smul_in_y, payoff_smul_in_y, smul_eq_mul, smul_eq_mul]

/-- Le payoff est **convexe en `y`** sur le simplexe. -/
theorem payoff_convex_in_y (x : m → ℝ) :
    ConvexOn ℝ (stdSimplex ℝ n) fun y => payoff A x y := by
  refine ⟨convex_stdSimplex ℝ n, ?_⟩
  intro y _hy y' _hy' a b _ha _hb _hab
  dsimp only
  rw [payoff_add_in_y, payoff_smul_in_y, payoff_smul_in_y, smul_eq_mul, smul_eq_mul]

/-- **Quasi-concavité en `y`** (itération 2 du glue Sion) : via le pont Mathlib
`ConcaveOn.quasiconcaveOn`, requis par `Sion.exists_isSaddlePointOn'`
(hypothèse `f(x, ·)` quasi-concave). -/
theorem payoff_quasiconcave_in_y (x : m → ℝ) :
    QuasiconcaveOn ℝ (stdSimplex ℝ n) fun y => payoff A x y :=
  (payoff_concave_in_y A x).quasiconcaveOn

/-- **Quasi-convexité en `x`** (itération 2 du glue Sion) : via le pont Mathlib
`ConvexOn.quasiconvexOn`, requis par `Sion.exists_isSaddlePointOn'`
(hypothèse `f(·, y)` quasi-convexe). -/
theorem payoff_quasiconvex_in_x (y : n → ℝ) :
    QuasiconvexOn ℝ (stdSimplex ℝ m) fun x => payoff A x y :=
  (payoff_convex_in_x A y).quasiconvexOn

/-! ## Itération 2 — semi-continuité (2 hyps Sion restantes)

Les 4 hyps analytiques de `Sion.minimax'` (`Mathlib/Topology/Sion.lean`) :
- `hfy' : ∀ y ∈ Y, QuasiconvexOn ℝ X (f · y)` — **prouvée** (`payoff_quasiconvex_in_x`) ;
- `hfx' : ∀ x ∈ X, QuasiconcaveOn ℝ Y (f x ·)` — **prouvée** (`payoff_quasiconcave_in_y`) ;
- `hfy : ∀ y ∈ Y, LowerSemicontinuousOn (f · y) X` — **prouvée ci-dessous** ;
- `hfx : ∀ x ∈ X, UpperSemicontinuousOn (f x ·) Y` — **prouvée ci-dessous**.

Une fonction continue est à la fois semi-continue inférieurement et
supérieurement (`Continuous.lowerSemicontinuous` / `Continuous.upperSemicontinuous`),
et la restriction à une partie passe via `.lowerSemicontinuousOn` /
`.upperSemicontinuousOn`. Le payoff est continu en chaque variable
(`continuous_payoff_in_x` / `continuous_payoff_in_y`), d'où les deux hyps. -/

/-- **Semi-continuité inférieure en `x`** (itération 2) : `f(·, y)` est
`LowerSemicontinuousOn` sur le simplexe — continuité ⟹ LSC, requis par
`Sion.minimax'` (hyp `hfy : ∀ y ∈ Y, LowerSemicontinuousOn (f · y) X`). -/
theorem payoff_lowerSemicontinuous_in_x (y : n → ℝ) :
    LowerSemicontinuousOn (fun x => payoff A x y) (stdSimplex ℝ m) :=
  (continuous_payoff_in_x A y).lowerSemicontinuous.lowerSemicontinuousOn (stdSimplex ℝ m)

/-- **Semi-continuité supérieure en `y`** (itération 2) : `f(x, ·)` est
`UpperSemicontinuousOn` sur le simplexe — continuité ⟹ USC, requis par
`Sion.minimax'` (hyp `hfx : ∀ x ∈ X, UpperSemicontinuousOn (f x ·) Y`). -/
theorem payoff_upperSemicontinuous_in_y (x : m → ℝ) :
    UpperSemicontinuousOn (fun y => payoff A x y) (stdSimplex ℝ n) :=
  (continuous_payoff_in_y A x).upperSemicontinuous.upperSemicontinuousOn (stdSimplex ℝ n)

end MinimaxLean
