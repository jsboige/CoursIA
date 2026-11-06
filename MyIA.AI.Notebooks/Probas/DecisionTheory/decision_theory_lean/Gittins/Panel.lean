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
l'énoncé (leçon #24705 : un énoncé honnête d'abord). Chacun a été **sondé dans
Lean au pin** (`db584cd6d46c` : `#check` des candidats, `exact?`/`apply?` sur
l'énoncé — jamais par grep : un nom généré par `to_additive`, un `alias` ou un
`@[simps]` est invisible au grep) avant la pose du `sorry`. Leçon fondatrice de
la review c.5778073186 : un premier passage par grep avait affirmé à tort que
`tsum_le_tsum` n'existait pas sur ℝ — l'additif `Summable.tsum_le_tsum` de
`Multipliable.tprod_le_tprod` (`InfiniteSum/Order.lean:131`) y existe et porte
`gcongr`.

Gradient de difficulté (le même vocabulaire P1/P2/P3 que le sous-track
CALIBRATION), **reclassé honnêtement après sondage Lean** :

| Terrain | Classe (mesurée) | Sondage Lean au pin |
|---|---|---|
| `panel_quarter_partial_sum` | P1 — calcul concret | `exact?` échoue (définition locale du lake) ; la forme fermée `geometricPartialSum_closed` + `norm_num` clôt — vérifié en sondage |
| `panel_constant_stream_monotone` | P2 — **bas de classe : la voie directe existe** | `Summable.tsum_le_tsum` existe au pin sur ℝ (nom généré par `to_additive`, invisible au grep) ; `exact?` ne clôt pas d'un coup, mais la preuve complète fait 3 lignes (`summable_geometric_of_lt_one` + point-à-point `mul_le_mul_of_nonneg_left`) — établie en sondage |
| `panel_partial_sums_tendsto` | P3 — composition de limites | le lake a déjà la forme fermée `geometricPartialSum_closed` et `geometric_series_converges` ; Mathlib a `tendsto_pow_atTop_nhds_zero_of_lt_one` (sondé au pin) ; `exact?` échoue sur l'énoncé (déf locale) — la difficulté est la **composition** (réécriture par forme fermée puis algèbre des limites), pas un lemme manquant |

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

Sondage Lean au pin (`db584cd6d46c`) : l'énoncé parle de `geometricPartialSum`,
une définition du lake — hors d'atteinte de Mathlib par construction. `exact?`
échoue sur l'énoncé (déf locale) ; la route vérifiée en sondage est la forme
fermée du lake `geometricPartialSum_closed` puis `norm_num`. -/
theorem panel_quarter_partial_sum : geometricPartialSum (1 / 4) 3 = 21 / 16 := by
  sorry

/-- **Terrain P2 — monotonie d'un flux constant, reclassée bas de classe**
(programme prover #1453, dispatch c2770 ; reclassement après review
c.5778073186).

Monotonie de la valeur actualisée d'un flux constant : si `μ₁ ≤ μ₀` (avec
`0 ≤ μ₁`, `0 < γ < 1`), alors `∑' γⁿ·μ₁ ≤ ∑' γⁿ·μ₀`. C'est le geste
d'arbitrage élémentaire d'un bandit à moyennes connues : la valeur du flux du
meilleur bras domine celle du flux dominé.

Sondage Lean au pin (`db584cd6d46c`) — corrige l'ancien docstring, dont
l'affirmation d'absence était un **artefact de grep** : la voie directe
point-à-point **existe**. `Summable.tsum_le_tsum` (l'additif `to_additive` de
`Multipliable.tprod_le_tprod`, `InfiniteSum/Order.lean:131` — le nom n'apparaît
jamais tel quel dans la source, d'où l'invisibilité au grep) s'applique à tout
monoïde additif topologique ordonné à topologie fermée, ℝ compris. `exact?`
ne clôt pas l'énoncé d'un coup (il faut fournir les deux sommabilités), mais
la preuve complète fait trois lignes, établie en sondage :
`Summable.tsum_le_tsum` + `summable_geometric_of_lt_one hγ₁.le hγ₂` (sondé :
`0 ≤ r → r < 1 → Summable fun n => r ^ n`) composé par `Summable.mul_right`,
plus le point-à-point `mul_le_mul_of_nonneg_left h (pow_nonneg hγ₁.le n)`.
Classe réelle : P2 bas — le terrain garde sa valeur d'étalon « preuve
triviale à atteindre », il n'est plus un objectif de difficulté.

Sondage complémentaire (2026-11-06), à la tête de la PR : la preuve directe
compile telle quelle, et elle compile **aussi sans** l'hypothèse `0 ≤ μ₁` —
Lean signale alors `hμ₁` comme variable inutilisée. L'hypothèse est donc
superflue pour la monotonie ; elle est conservée parce qu'elle porte le sens
économique du terrain (une moyenne de récompense est positive), pas parce que
la preuve en a besoin. Un prover qui la voit comme du bruit a raison sur le
plan logique. -/
theorem panel_constant_stream_monotone {γ μ₁ μ₀ : ℝ} (hγ₁ : 0 < γ) (hγ₂ : γ < 1)
    (hμ₁ : 0 ≤ μ₁) (h : μ₁ ≤ μ₀) :
    ∑' n : ℕ, γ ^ n * μ₁ ≤ ∑' n : ℕ, γ ^ n * μ₀ := by
  sorry

/-- **Terrain P3 — composition de limites** (programme prover #1453, dispatch
c2770 ; description réalignée après review c.5778073186).

Convergence des sommes partielles actualisées vers leur somme totale : les
sommes partielles `geometricPartialSum γ n · μ` (définies par un `List.foldl`
sur `List.range`) tendent vers `∑' γᵏ·μ` quand `n → ∞`, pour `0 < γ < 1`.
C'est la pièce analytique qui relie la définition *finie* du lake à la
théorie *infinie* de `Gittins.Discount`.

Sondage Lean au pin (`db584cd6d46c`) : `exact?` échoue sur l'énoncé
(définition locale du lake dans le but) — honnête à citer. La route naturelle
ne passe **pas** par le pont `List.foldl ↔ Finset.sum` que l'ancien docstring
presentait comme le cœur : le lake possède déjà la forme fermée
`geometricPartialSum_closed` (`γ ≠ 1 → geometricPartialSum γ n = (1 − γⁿ)/(1 −
γ)`, `Gittins/Discount.lean`) et `geometric_series_converges` (`∑' γⁿ =
1/(1−γ)`), et Mathlib possède `tendsto_pow_atTop_nhds_zero_of_lt_one`
(`0 ≤ r → r < 1 → Tendsto (r ^ n) atTop (nhds 0)`, sondé au pin). La
difficulté réelle est la **composition** : réécrire chaque somme partielle par
la forme fermée, faire tendre `γⁿ → 0` par le lemme sondé, pousser la limite à
travers la division et la multiplication par `μ` (algèbre des limites), puis
identifier la limite à `∑' γᵏ·μ` via `geometric_series_converges`. -/
theorem panel_partial_sums_tendsto {γ μ : ℝ} (hγ₁ : 0 < γ) (hγ₂ : γ < 1) :
    Tendsto (fun n => geometricPartialSum γ n * μ) atTop (nhds (∑' k : ℕ, γ ^ k * μ)) := by
  sorry

end Gittins
