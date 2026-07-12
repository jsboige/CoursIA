import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

import RepeatedGames.Stage

/-!
  Discounting and geometric series (EN sibling)
  =============================================

  English mirror of `RepeatedGames/Discounting.lean` (FR-first canonical).
  Convention i18n Lean ratifiée par ai-01 (2026-07-04, #4980 comment-4881909354) :
  fichiers `.lean` distincts FR + EN siblings dans le même lake, les deux compilent.
  Drift-CI detectable : contenu non-docstring byte-identique entre siblings.

  Note méthodologique : traduction manuelle du FR canonique (pas de source
  EN historique pré-Option A à recover, fichier FR-first depuis origin).

  We establish closed forms for the discounted payoff streams by the
  discount factor `δ ∈ [0, 1)`:

    - Perpetual cooperation:    V_C(δ) = R + δ·R + δ²·R + … = R / (1 − δ)
    - Deviate then be punished: V_D(δ) = T + δ·P + δ²·P + … = T + δ·P / (1 − δ)

  The key is the geometric series `Σ' δⁿ = (1 − δ)⁻¹` (Mathlib
  `tsum_geometric_of_lt_one`). We derive the grim trigger critical
  threshold:

    V_C ≥ V_D  ⟺  δ ≥ (T − R) / (T − P)
-/

namespace RepeatedGames_en

open Real
open RepeatedGames

/-- Geometric series: for `δ ∈ [0, 1)`, `Σ' n, δⁿ = (1 − δ)⁻¹`. -/
lemma geom_sum {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) :
    ∑' n : ℕ, δ^n = (1 - δ)⁻¹ :=
  tsum_geometric_of_lt_one h0 h1

/-- Discounted value of perpetual cooperation (closed form). -/
noncomputable def coopValue (R δ : ℝ) : ℝ := R / (1 - δ)

/-- Discounted value of the "deviate once then perpetual punishment"
trajectory (closed form). -/
noncomputable def deviateValue (T P δ : ℝ) : ℝ := T + δ * P / (1 - δ)

/-! ## Reduction to the critical threshold -/

/-- Key lemma of the threshold: for `δ ∈ [0, 1)` and a PD `g`,
perpetual cooperation is at least as good as deviate-then-punish
**iff** `δ ≥ (T − R) / (T − P)`.

Proof (pure real algebra): `R/(1−δ) ≥ T + δ·P/(1−δ)` ⟺ (multiply
by `1−δ > 0`) `R ≥ T·(1−δ) + δ·P` ⟺ `δ·(T−P) ≥ T−R` ⟺ (divide by `T−P > 0`)
`δ ≥ (T−R)/(T−P)`. The Mathlib division lemmas `le_div_iff₀` / `div_le_iff₀`
do the multiplication by positive denominators; `field_simp` normalizes the
nested fraction `δ·P/(1−δ)` into `δ·P` (additive form); `linarith` closes
the residue. -/
lemma coop_ge_deviate_iff {δ : ℝ} (g : PrisonersDilemma)
    (h0 : 0 ≤ δ) (h1 : δ < 1) :
    coopValue g.R δ ≥ deviateValue g.T g.P δ ↔
      δ ≥ (g.T - g.R) / (g.T - g.P) := by
  have hδp : 0 < 1 - δ := by linarith
  have hTP : 0 < g.T - g.P := by linarith [g.hTR, g.hRP]
  show g.R / (1 - δ) ≥ g.T + δ * g.P / (1 - δ) ↔
       δ ≥ (g.T - g.R) / (g.T - g.P)
  constructor
  · -- → : cooperation wins  ⟹  δ above threshold
    intro h
    -- h : g.R/(1−δ) ≥ g.T + δ·g.P/(1−δ)
    -- Extract (via le_div_iff₀) then normalize: the nested division
    -- δ·g.P/(1−δ) simplifies into δ·g.P, yielding a purely additive form.
    have h3raw : (g.T + δ * g.P / (1 - δ)) * (1 - δ) ≤ g.R :=
      (le_div_iff₀ hδp).mp h
    have h3 : g.T * (1 - δ) + δ * g.P ≤ g.R := by
      have heq : (g.T + δ * g.P / (1 - δ)) * (1 - δ) = g.T * (1 - δ) + δ * g.P := by
        field_simp [hδp.ne']
      rw [heq] at h3raw; exact h3raw
    -- But δ ≥ (g.T−g.R)/(g.T−g.P)  ⟺  g.T−g.R ≤ δ·(g.T−g.P)  (div_le_iff₀)
    exact (div_le_iff₀ hTP).mpr (by linarith [h3])
  · -- ← : δ above threshold  ⟹  cooperation wins
    intro h
    -- h : δ ≥ (g.T−g.R)/(g.T−g.P)  ⟺  g.T−g.R ≤ δ·(g.T−g.P)  (div_le_iff₀)
    have h3 : g.T - g.R ≤ δ * (g.T - g.P) := (div_le_iff₀ hTP).mp h
    -- But g.R/(1−δ) ≥ g.T+δ·g.P/(1−δ)  ⟺  (g.T+δ·g.P/(1−δ))·(1−δ) ≤ g.R  (le_div_iff₀)
    -- Reduce to additive form g.T·(1−δ)+δ·g.P ≤ g.R then linarith.
    apply (le_div_iff₀ hδp).mpr
    have heq : (g.T + δ * g.P / (1 - δ)) * (1 - δ) = g.T * (1 - δ) + δ * g.P := by
      field_simp [hδp.ne']
    rw [heq]
    linarith [h3]

end RepeatedGames_en