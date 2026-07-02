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

/-- Lemme clé du seuil : pour `δ ∈ [0, 1)` et un PD `g`, la coopération
perpétuelle est au moins aussi bonne que dévier-puis-punir **ssi**
`δ ≥ (T − R) / (T − P)`.

Démonstration (algèbre réelle pure) : `R/(1−δ) ≥ T + δ·P/(1−δ)` ⟺ (multiplier
par `1−δ > 0`) `R ≥ T·(1−δ) + δ·P` ⟺ `δ·(T−P) ≥ T−R` ⟺ (diviser par `T−P > 0`)
`δ ≥ (T−R)/(T−P)`. Les lemmes de division Mathlib `le_div_iff₀` / `div_le_iff₀`
font la multiplication par les dénominateurs positifs ; `field_simp` normalise la
fraction imbriquée `δ·P/(1−δ)` en `δ·P` (forme additive) ; `linarith` ferme le
résidu. -/
lemma coop_ge_deviate_iff {δ : ℝ} (g : PrisonersDilemma)
    (h0 : 0 ≤ δ) (h1 : δ < 1) :
    coopValue g.R δ ≥ deviateValue g.T g.P δ ↔
      δ ≥ (g.T - g.R) / (g.T - g.P) := by
  have hδp : 0 < 1 - δ := by linarith
  have hTP : 0 < g.T - g.P := by linarith [g.hTR, g.hRP]
  show g.R / (1 - δ) ≥ g.T + δ * g.P / (1 - δ) ↔
       δ ≥ (g.T - g.R) / (g.T - g.P)
  constructor
  · -- → : coopération l'emporte  ⟹  δ au-dessus du seuil
    intro h
    -- h : g.R/(1−δ) ≥ g.T + δ·g.P/(1−δ)
    -- Extraire (via le_div_iff₀) puis normaliser : la division imbriquée
    -- δ·g.P/(1−δ) simplifie en δ·g.P, donnant une forme purement additive.
    have h3raw : (g.T + δ * g.P / (1 - δ)) * (1 - δ) ≤ g.R :=
      (le_div_iff₀ hδp).mp h
    have h3 : g.T * (1 - δ) + δ * g.P ≤ g.R := by
      have heq : (g.T + δ * g.P / (1 - δ)) * (1 - δ) = g.T * (1 - δ) + δ * g.P := by
        field_simp [hδp.ne']
      rw [heq] at h3raw; exact h3raw
    -- But δ ≥ (g.T−g.R)/(g.T−g.P)  ⟺  g.T−g.R ≤ δ·(g.T−g.P)  (div_le_iff₀)
    exact (div_le_iff₀ hTP).mpr (by linarith [h3])
  · -- ← : δ au-dessus du seuil  ⟹  coopération l'emporte
    intro h
    -- h : δ ≥ (g.T−g.R)/(g.T−g.P)  ⟺  g.T−g.R ≤ δ·(g.T−g.P)  (div_le_iff₀)
    have h3 : g.T - g.R ≤ δ * (g.T - g.P) := (div_le_iff₀ hTP).mp h
    -- But g.R/(1−δ) ≥ g.T+δ·g.P/(1−δ)  ⟺  (g.T+δ·g.P/(1−δ))·(1−δ) ≤ g.R  (le_div_iff₀)
    -- Ramener à la forme additive g.T·(1−δ)+δ·g.P ≤ g.R puis linarith.
    apply (le_div_iff₀ hδp).mpr
    have heq : (g.T + δ * g.P / (1 - δ)) * (1 - δ) = g.T * (1 - δ) + δ * g.P := by
      field_simp [hδp.ne']
    rw [heq]
    linarith [h3]

end RepeatedGames
