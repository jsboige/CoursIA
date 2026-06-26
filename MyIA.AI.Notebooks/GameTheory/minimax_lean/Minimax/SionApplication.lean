import Mathlib
import Minimax.ZeroSum
import Minimax.Concavity

/-!
# Minimax.SionApplication — application finale de Sion (itération 3 du glue Sion)

Ce module câble les **4 hyps analytiques** prouvées dans `Concavity.lean` (quasi-convexité
en `x`, quasi-concavité en `y`, semi-continuité inf. en `x`, sup. en `y`) avec les faits
topologiques de Mathlib sur `stdSimplex` (compacité `isCompact_stdSimplex`, convexité
`convex_stdSimplex`, non-vacuité via `single_mem_stdSimplex`) pour prouver l'existence
d'un point-selle via `Sion.exists_isSaddlePointOn` (cas réel) — le **milestone final** de #4054.

Les 5 prérequis topologiques de Sion sur `E = m → ℝ` (et `F = n → ℝ`) sont
`TopologicalSpace`, `AddCommGroup`, `Module ℝ`, `IsTopologicalAddGroup`, `ContinuousSMul ℝ` :
ils se synthétisent depuis les instances `Pi` de Mathlib (`Pi.topologicalSpace`,
`Pi.instAddCommGroup`, `Pi.instModule`, etc.). Ce module **itération 3** livre le fait
auxiliaire de **non-vacuité du simplexe** puis l'**application finale**.

`IsSaddlePointOn` vit au top-level (`Mathlib/Order/SaddlePoint.lean`), tandis que
`exists_isSaddlePointOn` est dans `namespace Sion`.
-/

namespace MinimaxLean

open Set

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable [Nonempty m] [Nonempty n]
variable (A : PayoffMatrix m n)

/-- Le simplexe standard `stdSimplex ℝ m` est non vide dès que `m` est non vide :
le Dirac `Pi.single i 1` (masse 1 sur l'indice `i`, 0 ailleurs) est un point du
simplexe, via le lemme Mathlib `single_mem_stdSimplex`. -/
lemma stdSimplex_nonempty_m : (stdSimplex ℝ m).Nonempty := by
  obtain ⟨i⟩ := ‹Nonempty m›
  exact ⟨Pi.single i 1, single_mem_stdSimplex (𝕜 := ℝ) i⟩

/-- Variante en `y` : `stdSimplex ℝ n` est non vide dès que `n` est non vide. -/
lemma stdSimplex_nonempty_n : (stdSimplex ℝ n).Nonempty := by
  obtain ⟨i⟩ := ‹Nonempty n›
  exact ⟨Pi.single i 1, single_mem_stdSimplex (𝕜 := ℝ) i⟩

/-- **Théorème minimax de von Neumann (forme point-selle)** — le **milestone final** de
l'issue #4054 : pour toute matrice de gains `A` sur des types finis non vides, il existe
des stratégies mixtes `a ∈ Δₘ`, `b ∈ Δₙ` telles que `payoff A a y ≤ payoff A x b` pour
tout `x ∈ Δₘ`, `y ∈ Δₙ` (point-selle). Démontré en une application de
`Sion.exists_isSaddlePointOn` (cas réel, `Topology/Sion.lean` section `Real`), en réunissant :
- compacité : `isCompact_stdSimplex ℝ` ;
- convexité : `convex_stdSimplex ℝ` ;
- non-vacuité : `stdSimplex_nonempty_m` / `stdSimplex_nonempty_n` (lemmes ci-dessus) ;
- les 4 hyps analytiques de `Concavity.lean` (quasi-convexité en `x`, quasi-concavité
  en `y`, semi-continuité inf. en `x`, sup. en `y`).

Les 5 prérequis topologiques de Sion sur `E = m → ℝ` et `F = n → ℝ`
(`TopologicalSpace`, `AddCommGroup`, `Module ℝ`, `IsTopologicalAddGroup`,
`ContinuousSMul ℝ`) se synthétisent depuis les instances `Pi` de Mathlib. -/
theorem exists_saddle_point_payoff :
    ∃ a ∈ stdSimplex ℝ m, ∃ b ∈ stdSimplex ℝ n,
      IsSaddlePointOn (stdSimplex ℝ m) (stdSimplex ℝ n) (payoff A) a b :=
  Sion.exists_isSaddlePointOn
    (ne_X := stdSimplex_nonempty_m)
    (cX := convex_stdSimplex ℝ m)
    (kX := isCompact_stdSimplex (𝕜 := ℝ) (ι := m))
    (hfy := fun y _hy => payoff_lowerSemicontinuous_in_x A y)
    (hfy' := fun y _hy => payoff_quasiconvex_in_x A y)
    (cY := convex_stdSimplex ℝ n)
    (ne_Y := stdSimplex_nonempty_n)
    (kY := isCompact_stdSimplex (𝕜 := ℝ) (ι := n))
    (hfx := fun x _hx => payoff_upperSemicontinuous_in_y A x)
    (hfx' := fun x _hx => payoff_quasiconcave_in_y A x)

end MinimaxLean
