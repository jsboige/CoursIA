import Mathlib
import PacLearning.Data

/-!
# PacLearning.ERM — argument ERM (Empirical Risk Minimization), brique 6/6-agnostic étape b

Sous-module de `PacLearning` : l'argument déterministe au cœur de la **généralisation agnostic**.
Étant donné un échantillon `S`, une hypothèse ERM `ĥ` (qui minimise l'erreur empirique sur `S`) et
une hypothèse de référence `h* ∈ Hs`, l'erreur vraie de `ĥ` est contrôlée par celle de `h*` à
`2ε` près, **à condition que la concentration uniforme tienne** sur la classe `Hs` :

    trueError D f ĥ ≤ trueError D f h* + 2·ε.

C'est un résultat **purement arithmétique** (4 inégalités élémentaires enchaînées) — il ne fait
appel à aucune structure probabiliste. Le rôle des probabilités est joué par l'hypothèse
`hconc : ∀ h ∈ Hs, |empError f h S − trueError D f h| ≤ ε`, qui est exactement l'événement
« la concentration uniforme tient » — dont `uniform_concentration` (UniformConcentration.lean,
brique 6a) borne la probabilité de violation par `2·|Hs|·exp(−2nε²)`.

En spécialisant `h*` à l'argmin de `trueError` sur `Hs` (la meilleure hypothèse de la classe),
on obtient la borne de généralisation agnostic : l'ERM ne fait pas pire que `2ε` au-delà de
l'optimum de la classe. Combiné à `uniform_concentration`, cela donne la complexité d'échantillon
PAC **agnostique** `m ≥ (1/ε²)(ln|H|+ln(1/δ))` — à comparer au réalisable `m ≥ (1/ε)(ln|H|+ln(1/δ))`
(livré dans `pac_finite_class_bound`, PR #4580), où le facteur `1/ε` (vs `1/ε²`) traduit la
concentration géométrique `(1−μ)^n ≤ e^{−εn}` plutôt que la concentration quadratique de Hoeffding.

Chaîne d'inégalités (l'essence de l'ERM) :
1. **Concentration de `ĥ`** : `|empError(ĥ) − trueError(ĥ)| ≤ ε` ⟹ `trueError(ĥ) ≤ empError(ĥ) + ε`.
2. **ERM** : `empError(ĥ) ≤ empError(h*)` (car `ĥ` minimise `empError` sur `Hs`, et `h* ∈ Hs`).
3. **Concentration de `h*`** : `|empError(h*) − trueError(h*)| ≤ ε` ⟹ `empError(h*) ≤ trueError(h*) + ε`.
4. **Combinaison** : `trueError(ĥ) ≤ empError(ĥ) + ε ≤ empError(h*) + ε ≤ trueError(h*) + 2ε`.

On reste dans le style **ℝ-weight pédagogique** : aucune machine `ℝ≥0∞`/`Measure`/`iIndepFun`.
-/

namespace PacLearning

open scoped Classical

variable {X : Type*} [Fintype X]
variable (D : Distribution X)
variable {D}

/-- **Borne d'erreur ERM** (brique 6/6-agnostic, étape b) : sur l'événement où la concentration
uniforme tient sur `Hs` (`∀ h ∈ Hs, |empError − trueError| ≤ ε`), une hypothèse ERM `ĥ`
(minimisant l'erreur empirique sur `S`) a une erreur vraie contrôlée par celle de n'importe quelle
hypothèse de référence `h* ∈ Hs`, à `2ε` près.

    trueError D f ĥ ≤ trueError D f h* + 2·ε.

Preuve (arithmétique, 4 inégalités enchaînées, close par `linarith`) :
1. `|empError(ĥ) − trueError(ĥ)| ≤ ε` ⟹ `trueError(ĥ) ≤ empError(ĥ) + ε` (concentration de `ĥ`).
2. `empError(ĥ) ≤ empError(h*)` (ERM : `ĥ` minimise `empError`, et `h* ∈ Hs`).
3. `|empError(h*) − trueError(h*)| ≤ ε` ⟹ `empError(h*) ≤ trueError(h*) + ε` (concentration de `h*`).
4. `trueError(ĥ) ≤ empError(ĥ) + ε ≤ empError(h*) + ε ≤ trueError(h*) + 2ε`.

L'extraction des bornes depuis `|a − b| ≤ ε` se fait via `abs_le : |x| ≤ u ↔ -u ≤ x ∧ x ≤ u`.
`linarith` enchaîne alors les 4 inégalités sans aide.

**Spécialisation agnostic** : en prenant `h* = argmin_{h∈Hs} trueError D f h` (la meilleure
hypothèse de la classe), la borne dit que l'ERM ne fait pas plus de `2ε` de pire que l'optimum de
la classe — la borne de généralisation agnostic. Combinée à `uniform_concentration` (qui borne la
probabilité que l'hypothèse `hconc` échoue), cela donne la complexité d'échantillon PAC agnostic
`m ≥ (1/ε²)(ln|H|+ln(1/δ))`. -/
theorem erm_error_bound (f : Hypothesis X) (Hs : Finset (Hypothesis X)) {n : ℕ} (hn : 0 < n)
    (S : Fin n → X) {ε : ℝ} (hε : 0 < ε)
    (ĥ hOpt : Hypothesis X) (hĥ_mem : ĥ ∈ Hs) (hOpt_mem : hOpt ∈ Hs)
    (hconc : ∀ h ∈ Hs, |empError f h S - trueError D f h| ≤ ε)
    (hĥ_erm : ∀ h ∈ Hs, empError f ĥ S ≤ empError f h S) :
    trueError D f ĥ ≤ trueError D f hOpt + 2 * ε := by
  -- Concentration ponctuelle de `ĥ` et de `hOpt` (instances de l'hypothèse uniforme `hconc`).
  have hĥ := hconc ĥ hĥ_mem
  have hhOpt := hconc hOpt hOpt_mem
  -- Déplie les valeurs absolues : `|a − b| ≤ ε ⟺ -ε ≤ a−b ∧ a−b ≤ ε`.
  rw [abs_le] at hĥ hhOpt
  -- ERM appliqué à `hOpt ∈ Hs` : `empError(ĥ) ≤ empError(hOpt)`.
  have heĥ : empError f ĥ S ≤ empError f hOpt S := hĥ_erm hOpt hOpt_mem
  -- Chaîne des 4 inégalités (essence de l'ERM), close par `linarith` :
  --   trueError(ĥ) ≤ empError(ĥ) + ε ≤ empError(hOpt) + ε ≤ trueError(hOpt) + 2ε.
  linarith [hĥ.1, hhOpt.2, heĥ]

end PacLearning
