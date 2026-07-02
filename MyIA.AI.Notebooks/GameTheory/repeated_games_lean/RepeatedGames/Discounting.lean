import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import RepeatedGames.Stage

/-!
# Actualisation et sommes géométriques

On établit les formes closes des flux de paiements actualisés par le
facteur d'escompte `δ ∈ [0, 1)` :

  - Coopération perpétuelle :  `V_C(δ) = R + δ·R + δ²·R + … = R / (1 − δ)`
  - Dévier puis être puni :     `V_D(δ) = T + δ·P + δ²·P + … = T + δ·P / (1 − δ)`

La clé est la somme géométrique `Σ' δⁿ = (1 − δ)⁻¹` (Mathlib
`tsum_geometric_of_lt_one`). On en déduit le seuil critique du grim trigger :

  `V_C ≥ V_D  ⟺  δ ≥ (T − R) / (T − P)`
-/

namespace RepeatedGames

open Real

/-- Somme géométrique : pour `δ ∈ [0, 1)`, `Σ' n, δⁿ = (1 − δ)⁻¹`. -/
lemma geom_sum {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) :
    ∑' n : ℕ, δ^n = (1 - δ)⁻¹ :=
  tsum_geometric_of_lt_one h0 h1

/-- Valeur actualisée de la coopération perpétuelle (forme close). -/
noncomputable def coopValue (R δ : ℝ) : ℝ := R / (1 - δ)

/-- Valeur actualisée de la trajectoire « dévier une fois puis punition
perpétuelle » (forme close). -/
noncomputable def deviateValue (T P δ : ℝ) : ℝ := T + δ * P / (1 - δ)

/-! ## Réduction au seuil critique -/

/-! ## Réduction au seuil critique -/

/-- Lemme clé du seuil : pour `δ ∈ [0, 1)` et un PD `g`, la coopération
perpétuelle est au moins aussi bonne que dévier-puis-punir **ssi**
`δ ≥ (T − R) / (T − P)`.

Démonstration : algèbre réelle pure. On multiplie l'inégalité `R / (1 − δ) ≥
T + δ·P / (1 − δ)` par `1 − δ > 0`, ce qui donne `R ≥ T·(1 − δ) + δ·P`, i.e.
`δ·(T − P) ≥ T − R`, puis on divise par `T − P > 0`.

TODO tranche 2 : tactiques `field_simp` + `linarith` (les hypothèses de
positivité `1 − δ > 0`, `T − P > 0` découlent de `h1` et de `hTR`, `hRP`). -/
lemma coop_ge_deviate_iff {δ : ℝ} (g : PrisonersDilemma)
    (h0 : 0 ≤ δ) (h1 : δ < 1) :
    coopValue g.R δ ≥ deviateValue g.T g.P δ ↔
      δ ≥ (g.T - g.R) / (g.T - g.P) := by
  sorry

end RepeatedGames
