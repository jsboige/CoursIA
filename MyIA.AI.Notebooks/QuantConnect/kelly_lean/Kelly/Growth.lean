import Mathlib
import Kelly.Bet

/-!
# Kelly.Growth — le taux de croissance espéré `g(f) = E[log(richesse)]`

Le **taux de croissance espéré** d'un pari de Bernoulli sous la fraction `f` est

    g(f) = p · log(1 + b·f) + q · log(1 − f)

où `p` (resp. `q`) est la probabilité de gain (resp. perte) et `b` la cote nette.
Maximiser `g` revient à maximiser la **croissance asymptotique du capital** composé
sur une infinité de paris indépendants (c'est l'optimalité de Kelly). Voir l'issue
#4052.

Ce module définit `growth` et `growthGrad`, et pose les **faits fondamentaux** de
ligne de base (croissance nulle sans pari, pente à l'origine = l'avantage). La
concavité stricte de `g` sur la zone admissible (vue calcul `g''(f) < 0`) est la
stratégie de preuve **contournée** par le théorème phare d'optimalité, qui démontre
directement `g(f) ≤ g(f*)` via la tangente `log t ≤ t − 1` plutôt que d'invoquer la
concavité abstraite — ce phare vit dans `Kelly.lean`.
-/

namespace KellyLean

open Real

/-- Le **taux de croissance espéré** `g(f) = p·log(1 + b·f) + q·log(1 − f)` :
    espérance du logarithme de la richesse relative. -/
noncomputable def growth (β : Bet) (f : ℝ) : ℝ :=
  β.p * log (winWealth β f) + q β * log (loseWealth β f)

/-- La **pente** (dérivée) du taux de croissance : `g'(f) = p·b/(1+bf) − q/(1−f)`.
    C'est la quantité dont l'annulation caractérise la fraction optimale. On l'expose
    explicitement car elle est au cœur du théorème d'optimalité (condition du premier
    ordre `growthGrad β f* = 0`). -/
noncomputable def growthGrad (β : Bet) (f : ℝ) : ℝ :=
  β.p * β.b / winWealth β f - q β / loseWealth β f

/-- **Croissance nulle sans pari** : `g(0) = 0`. Ne rien miser (`f = 0`) laisse le
    capital inchangé — les deux multiplicateurs de richesse valent `1`, et `log 1 = 0`.
    C'est la **ligne de base** du critère de Kelly : toute fraction `f` avec `g(f) > 0`
    bat le « ne rien faire », toute fraction avec `g(f) < 0` lui est inférieure
    (cf `Kelly.kelly_optimal`, qui garantit `g(f) ≤ g(f*)` et, l'edge étant positif,
    `g(f*) > 0 = g(0)`). -/
lemma growth_zero (β : Bet) : growth β 0 = 0 := by
  unfold growth winWealth loseWealth
  simp [Real.log_one]

/-- **Pente à l'origine = l'avantage** : `g'(0) = b·p − q`. Sans mise (`f = 0`), la
    pente du log-croissance vaut exactement l'« edge » `b·p − q` — soit le **numérateur**
    de la fraction de Kelly `f* = (b·p − q)/b`. Ainsi `g'(0) > 0` ⟺ `f* > 0` (pari
    favorable, miser), `g'(0) < 0` ⟺ `f* < 0` (pari défavorable, shorter). C'est le
    pont entre la géométrie locale de `g` (sa pente en `0`) et le sens de la mise
    optimale. -/
lemma growthGrad_zero (β : Bet) : growthGrad β 0 = β.p * β.b - q β := by
  unfold growthGrad winWealth loseWealth
  simp [div_one]

end KellyLean
