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

Ce module définit `growth` et établit la **concavité stricte** de `g` sur la zone
admissible (vue calcul : `g''(f) < 0`). Le théorème phare d'optimalité — qui prouve
directement `g(f) ≤ g(f*)` via la tangente `log t ≤ t − 1`, sans recourir à la
concavité abstraite — vit dans `Kelly.lean`.
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

end KellyLean
