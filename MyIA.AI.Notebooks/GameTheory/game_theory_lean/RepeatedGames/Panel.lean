import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.GeomSum
import RepeatedGames.Stage
import RepeatedGames.Discounting

/-!
  Jeux répétés — Terrains du panel prover (tranche 2, #1453)
  ==========================================================

  Trois terrains Lean pour le programme panel prover, sur le vocabulaire
  existant de la série (`PrisonersDilemma`, `coopValue`, seuil critique).
  Énoncés validés par ai-01 au préalable (arbitrage 2026-11-05T00:31:43Z).

  Chaque terrain porte un `sorry` ancré `[LEAN-ANCHOR-DECLARED]` : l'énoncé
  est complet, le `sorry` ne remplace que la preuve.

  Les routes de preuve de référence ne figurent pas dans ce fichier. Il est
  lu par le prover : y écrire une route reviendrait à lui fournir la
  réponse. Elles vivent dans le fil de la PR #24730 (commentaire
  c.6648328912), qui sert de vérité terrain au ledger du programme prover.

  Classes mesurées : P1 (facile), P2 (moyen), P3 (difficile) — le gradient
  est décrit dans les docstrings ci-dessous.
-/

open RepeatedGames.PDAction Filter
open scoped BigOperators

namespace RepeatedGames

/-! ## Le PD canonique de Gibbons -/

/-- Le dilemme du prisonnier canonique de Gibbons (2020) : T = 5, R = 3,
P = 1, S = 0. Les quatre contraintes de `PrisonersDilemma` sont prouvées
par `norm_num`. -/
noncomputable def panelPD : PrisonersDilemma :=
  ⟨5, 3, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## Terrain P1 — seuil du PD canonique

Le seuil critique de coopération du PD canonique vaut exactement 1/2 :
au-delà de δ = 1/2, la trajectoire coopérative du grim trigger domine la
déviation unique. -/

/-- Terrain P1 (classe P1, facile) : le seuil critique de coopération du PD
canonique de Gibbons vaut 1/2. Une preuve de référence existe ; elle est
consignée dans le fil de la PR #24730 (c.6648328912) et n'est pas écrite
ici, ce fichier étant lu par le prover. -/
theorem panel_pd_threshold_half :
    (panelPD.T - panelPD.R) / (panelPD.T - panelPD.P) = 1 / 2 := by
  sorry  -- [LEAN-ANCHOR-DECLARED]

/-! ## Terrain P2 — statique comparative de la punition

Durcir la punition (baisser P) abaisse le seuil critique : la coopération
devient soutenable pour un δ plus faible. -/

/-- Terrain P2 (classe P2, moyen) : une punition plus dure abaisse le seuil
critique de coopération — `(T - R) / (T - P₂) ≤ (T - R) / (T - P₁)` quand
`P₂ ≤ P₁`. Une preuve de référence existe ; elle est consignée dans le fil
de la PR #24730 (c.6648328912) et n'est pas écrite ici, ce fichier étant lu
par le prover. -/
theorem panel_harsher_punishment_lowers_threshold
    (T R P₁ P₂ : ℝ) (hTR : R < T) (hP : P₂ ≤ P₁) (hTP : P₁ < T) :
    (T - R) / (T - P₂) ≤ (T - R) / (T - P₁) := by
  sorry  -- [LEAN-ANCHOR-DECLARED]

/-! ## Terrain P3 — convergence horizon fini vers la perpétuité

Le paiement actualisé de la trajectoire coopérative à horizon fini n
converge vers `coopValue R δ` quand n → ∞ : la pièce analytique qui relie
l'horizon fini du panel au flux infini. -/

/-- Terrain P3 (classe P3, difficile) : le paiement de la trajectoire
coopérative à horizon fini converge vers la perpétuité `coopValue R δ`.
Une preuve de référence existe ; elle est consignée dans le fil de la PR
#24730 (c.6648328912) et n'est pas écrite ici, ce fichier étant lu par le
prover. -/
theorem panel_partial_coop_tendsto
    (R δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ < 1) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, δ ^ k * R) atTop
      (nhds (coopValue R δ)) := by
  sorry  -- [LEAN-ANCHOR-DECLARED]

end RepeatedGames
