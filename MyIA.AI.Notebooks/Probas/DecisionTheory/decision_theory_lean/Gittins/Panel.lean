import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Gittins.Basic
import Gittins.Discount

/-!
# Panel de terrains du programme prover (#1453) — `sorry` documentés

Terrains d'entraînement du programme prover (EPIC #1453, dispatch c2770 du
2026-11-04) : des théorèmes qu'on s'était interdit d'ajouter, posés ici comme
cibles fraîches avec un `sorry` **documenté** dans la preuve — jamais dans
l'énoncé (leçon #24705 : un énoncé honnête d'abord). Chacun a été **vérifié
absent de Mathlib au pin** (`db584cd6d46c`, mesuré par grep de l'arbre Mathlib
vendored dans `.lake/packages/mathlib/`) avant la pose du `sorry`, afin que la
difficulté affichée soit réelle et non un déguisement de lemme existant.

Gradient de difficulté (le même vocabulaire P1/P2/P3 que le sous-track
CALIBRATION) :

| Terrain | Classe | Vérification Mathlib au pin |
|---|---|---|
| `panel_quarter_partial_sum` | P1 — calcul concret | énoncé sur une définition du lake (`geometricPartialSum`), donc hors d'atteinte de Mathlib par construction |
| `panel_constant_stream_monotone` | P2 — chaîne de réécriture | `tsum_le_tsum` n'existe au pin que sur ℝ≥0/ℝ≥0∞ (`InfiniteSum/ENNReal.lean:115`) — **pas sur ℝ brut** ; la voie directe point-à-point est fermée, la forme fermée (`present_value_constant`) est la route |
| `panel_partial_sums_tendsto` | P3 — pont List→tsum | `HasSum.tendsto_sum_nat` existe au pin (usages compilés dans `InfiniteSum/Ring.lean:281`) et sert d'**étape finale** ; la difficulté est le pont `List.foldl` → `∑ k ∈ Finset.range n`, qui est local au lake |

La baseline `sorry-baseline` de `scripts/lean/ci_lakes.json` passe de 2 à 5
dans la même PR (le gate exige l'égalité exacte, échec bidirectionnel).
Convention i18n (#4980) : miroir anglais dans `Gittins/Panel_en.lean`
(namespace `Gittins_en`), docstrings seules divergentes.
-/

namespace Gittins

open Filter

/-- **Terrain P1 — calcul concret** (programme prover #1453, dispatch c2770).

Somme partielle géométrique en base 1/4 sur trois termes :
`1 + 1/4 + 1/16 = 21/16`. Terrain de la classe la plus facile du gradient :
une exécution de la définition (`geometricPartialSum`) suivie d'un calcul
numérique exact (`norm_num`). C'est l'analogue décision-théorie des cibles
concrètes du sous-track CALIBRATION (`isWinningNim_345`, `lookAndSay_4`).

Vérification d'absence Mathlib (pin `db584cd6d46c`) : l'énoncé parle de
`geometricPartialSum`, une définition du lake — aucune entité Mathlib ne peut
l'énoncer ; le `grep -r "geometricPartialSum"` sur l'arbre vendored rend 0
hit. La difficulté P1 est donc honnête : déplier la définition locale puis
calculer, sans lemme externe qui court-circuite. -/
theorem panel_quarter_partial_sum : geometricPartialSum (1 / 4) 3 = 21 / 16 := by
  sorry

/-- **Terrain P2 — chaîne de réécriture** (programme prover #1453, dispatch c2770).

Monotonie de la valeur actualisée d'un flux constant : si `μ₁ ≤ μ₀` (avec
`0 ≤ μ₁`, `0 < γ < 1`), alors `∑' γⁿ·μ₁ ≤ ∑' γⁿ·μ₀`. C'est le geste
d'arbitrage élémentaire d'un bandit à moyennes connues : la valeur du flux du
meilleur bras domine celle du flux dominé.

Vérification d'absence Mathlib (pin `db584cd6d46c`) : la voie courte
point-à-point `tsum_le_tsum` n'existe au pin **que sur ℝ≥0/ℝ≥0∞**
(`InfiniteSum/ENNReal.lean:115`, `protected`, namespace `ENNReal`) — mesuré
par `grep -rn "theorem tsum_le_tsum" Mathlib/` : 1 hit, aucun sur ℝ. La route
passe donc par la forme fermée : réécrire chaque membre par
`present_value_constant` (`Gittins.Discount`), puis comparer `μ₁/(1-γ) ≤
μ₀/(1-γ)` avec `one_minus_gamma_pos` comme condition de signe. Quelques
tactiques, plusieurs lemmes à trouver : P2. -/
theorem panel_constant_stream_monotone {γ μ₁ μ₀ : ℝ} (hγ₁ : 0 < γ) (hγ₂ : γ < 1)
    (hμ₁ : 0 ≤ μ₁) (h : μ₁ ≤ μ₀) :
    ∑' n : ℕ, γ ^ n * μ₁ ≤ ∑' n : ℕ, γ ^ n * μ₀ := by
  sorry

/-- **Terrain P3 — pont List→tsum** (programme prover #1453, dispatch c2770).

Convergence des sommes partielles actualisées vers leur somme totale : les
sommes partielles `geometricPartialSum γ n · μ` (définies par un `List.foldl`
sur `List.range`) tendent vers `∑' γᵏ·μ` quand `n → ∞`, pour `0 < γ < 1`.
C'est la pièce analytique qui relie la définition *finie* du lake à la
théorie *infinie* de `Gittins.Discount`.

Vérification de présence/absence Mathlib (pin `db584cd6d46c`) :
`HasSum.tendsto_sum_nat` **existe** au pin (usages compilés dans
`InfiniteSum/Ring.lean:281,286`) mais ne s'applique qu'aux sommes
`∑ k ∈ Finset.range n` — pas à notre `List.foldl`. La difficulté du terrain
est le **pont** `geometricPartialSum γ n = ∑ k ∈ Finset.range n, γ ^ k`
(induction sur `n`, `List.foldl` ↔ `Finset.sum`), puis l'extraction d'un
`HasSum` depuis `geometric_series_converges` (`Summable.hasSum`), et la
multiplication par la constante `μ` (`Tendsto.mul_const` / continuité). Le
lemme Mathlib sert d'étape finale, pas de preuve : P3 par composition. -/
theorem panel_partial_sums_tendsto {γ μ : ℝ} (hγ₁ : 0 < γ) (hγ₂ : γ < 1) :
    Tendsto (fun n => geometricPartialSum γ n * μ) atTop (nhds (∑' k : ℕ, γ ^ k * μ)) := by
  sorry

end Gittins
