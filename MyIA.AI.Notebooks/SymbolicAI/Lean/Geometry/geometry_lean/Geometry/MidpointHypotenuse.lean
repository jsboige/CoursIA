/-
  MidpointHypotenuse — le milieu de l'hypoténuse
  =============================================

  Premier théorème du lac `geometry_lean` (EPIC #18601 volet B, position 05 du
  programme gradué #17544). C'est le fil rouge de la série Geometry Python :
  le notebook `Geometry-01-From-Figure-To-Equation.ipynb` part de la figure
  du milieu de l'hypoténuse ; ce module en donne la preuve formelle.

  Formulation : un triangle `ABC` rectangle en `A`, vu depuis `A` prise pour
  origine, a ses deux côtés portés par des vecteurs orthogonaux `u` (vers `B`)
  et `v` (vers `C`). Le milieu `M` de l'hypoténuse `[BC]` est alors
  équidistant des trois sommets : `MA = MB = MC`. Autrement dit, `M` est le
  centre du cercle circonscrit et le rayon vaut la moitié de l'hypoténuse —
  c'est la réciproque du théorème de Pythagore qui « voit » le cercle.

  Les notebooks Python de la série calculent (sympy) ; ce lac prouve (Lean).
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Module

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Égalité des diagonales d'un parallélogramme « rectangle » : si `u` et `v`
sont orthogonaux, la somme `u + v` et la différence `u - v` ont même norme.
Chaque carré vaut `‖u‖² + ‖v‖²` — le terme croisé `±2⟪u, v⟫` de l'identité
de polarisation est nul — donc les deux normes valent la même racine
`√(‖u‖² + ‖v‖²)`, par les deux formes du théorème de Pythagore (additive et
soustractive) de Mathlib. -/
theorem norm_add_eq_norm_sub_of_inner_eq_zero {u v : E} (huv : ⟪u, v⟫_ℝ = 0) :
    ‖u + v‖ = ‖u - v‖ := by
  rw [norm_add_eq_sqrt_iff_real_inner_eq_zero.2 huv,
      norm_sub_eq_sqrt_iff_real_inner_eq_zero.2 huv]

/-- Composante « sommet `B` » : la distance de l'origine `A` au milieu `M`
égale la distance de `B = u` à `M`. Les deux se réduisent à `2⁻¹ • ‖u - v‖`
par l'identité de Pythagore (lemme ci-dessus) : `M - B` vaut la moitié de
`u - v` (une demi-diagonale du rectangle construit sur `u` et `v`). -/
private theorem dist_origin_eq_dist_apex_of_inner_eq_zero {u v : E}
    (huv : ⟪u, v⟫_ℝ = 0) :
    ‖(2 : ℝ)⁻¹ • (u + v)‖ = ‖u - (2 : ℝ)⁻¹ • (u + v)‖ := by
  have hsplit : u - (2 : ℝ)⁻¹ • (u + v) = (2 : ℝ)⁻¹ • (u - v) := by
    module
  rw [hsplit, norm_smul, norm_smul, norm_add_eq_norm_sub_of_inner_eq_zero huv]

/-- **Théorème du milieu de l'hypoténuse.** Dans un triangle rectangle en `A`
(l'origine), de côtés `B = u` et `C = v` avec `u ⊥ v`, le milieu
`M = (u + v) / 2` de l'hypoténuse `[BC]` est équidistant des trois sommets :
`MA = MB = MC`. La composante `MC` s'obtient par symétrie : échanger les rôles
de `u` et `v` échange `B` et `C` sans toucher au milieu ni à l'orthogonalité. -/
theorem midpoint_hypotenuse_equidistant {u v : E} (huv : ⟪u, v⟫_ℝ = 0) :
    ‖(2 : ℝ)⁻¹ • (u + v)‖ = ‖u - (2 : ℝ)⁻¹ • (u + v)‖ ∧
      ‖(2 : ℝ)⁻¹ • (u + v)‖ = ‖v - (2 : ℝ)⁻¹ • (u + v)‖ :=
  ⟨dist_origin_eq_dist_apex_of_inner_eq_zero huv, by
    have hvu : ⟪v, u⟫_ℝ = 0 := by
      rw [real_inner_comm, huv]
    have h := dist_origin_eq_dist_apex_of_inner_eq_zero hvu
    rwa [add_comm v u] at h⟩

/-- Le rayon commun vaut la moitié de l'hypoténuse : la distance de `A`
(origine) au milieu `M` est `‖u - v‖ / 2`, soit `BC / 2`. C'est la lecture
« cercle circonscrit » du théorème : le rayon est l'hypoténuse coupée en deux,
d'où la construction du cercle circonscrit au compas par le seul milieu de
l'hypoténuse. -/
theorem midpoint_hypotenuse_radius {u v : E} (huv : ⟪u, v⟫_ℝ = 0) :
    ‖(2 : ℝ)⁻¹ • (u + v)‖ = (2 : ℝ)⁻¹ * ‖u - v‖ := by
  rw [norm_smul, norm_add_eq_norm_sub_of_inner_eq_zero huv, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
