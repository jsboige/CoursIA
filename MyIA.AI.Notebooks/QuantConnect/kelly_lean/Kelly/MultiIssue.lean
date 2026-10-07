import Mathlib
import Kelly.Bet
import Kelly.Growth
import Kelly.Kelly

/-!
# Kelly.MultiIssue — extension multi-pari du critère de Kelly (cas indépendant, N = 2)

Le théorème de Kelly (cf. `Kelly.Kelly`) maximise la log-croissance `g(f)` pour
**un seul** pari de Bernoulli. Cette généralisation traite le cas **multi-pari
indépendant à deux paris** (le cas général `N` s'en déduit par induction, voir
note en bas) : étant donné deux paris indépendants `β_1, β_2` (chacun avec sa
probabilité et sa cote nette), l'allocation optimale `(f_1, f_2)` maximise la
**somme** des log-croissances individuelles :

    growth(β_1, f_1) + growth(β_2, f_2)

## Stratégie de preuve

On évite l'optimisation jointe abstraite et on exploite la **séparabilité** du
problème : la somme est un opérateur linéaire, et la log-croissance de chaque
pari ne dépend que de son propre `f_i`. On fixe `f_2` et on optimise en `f_1`
(`kelly_optimal` donne `f_1* = kellyFrac β_1` indépendamment de `f_2`), puis
on fixe `f_1 = kellyFrac β_1` et on optimise en `f_2` (même argument, `f_2* =
kellyFrac β_2`). Le couple `(kellyFrac β_1, kellyFrac β_2)` est donc le
**maximiseur joint**.

L'**unicité** suit de `kelly_unique` : si un des `f_i` diffère de `kellyFrac`,
la log-croissance jointe est strictement inférieure, peu importe l'autre
composante.

## Cas général (N paris)

L'extension à N paris indépendants suit par induction : ajouter un pari à une
famille optimale préserve l'optimalité parce que le nouveau pari est
indépendant des autres et maximise sa propre log-croissance par `kelly_optimal`
(cas unaire `N = 1` = `kelly_optimal` lui-même).

## Lemmes du module

| Nom | Type | Role |
|---|---|---|
| `jointGrowth2` | `def` | Somme des log-croissances de deux paris |
| `multiKelly_optimal_2` | `theorem` | Toute allocation admissible ≤ (kellyFrac β_1, kellyFrac β_2) |
| `multiKelly_unique_2` | `theorem` | Si un `f_i` diffère, la log-croissance est strictement < |

Voir l'issue #19516, carnet 3 du plan #16231.
-/

namespace KellyLean

open Real

/-- La **log-croissance jointe** de deux paris : somme des log-croissances
    individuelles. Pour des paris indépendants, le log-capital espéré après un
    pas est bien la somme des contributions (le capital total est le produit
    des multiplicateurs, dont le log est la somme des logs). -/
noncomputable def jointGrowth2 (β₁ β₂ : Bet) (f₁ f₂ : ℝ) : ℝ :=
  growth β₁ f₁ + growth β₂ f₂

/-- **Théorème de Kelly multi-pari à 2 paris (maximiseur)** : pour deux paris
    indépendants `β₁, β₂`, l'allocation Kelly `(kellyFrac β₁, kellyFrac β₂)`
    maximise la log-croissance jointe. Pour toute allocation admissible
    `(f₁, f₂)`, on a

        jointGrowth2 β₁ β₂ f₁ f₂ ≤ jointGrowth2 β₁ β₂ (kellyFrac β₁) (kellyFrac β₂)

    **Stratégie de preuve** : par `kelly_optimal` appliqué à chaque composante
    (les paris sont indépendants, donc les inégalités s'additionnent). -/
theorem multiKelly_optimal_2 (β₁ β₂ : Bet) (f₁ f₂ : ℝ)
    (hf₁ : Feasible β₁ f₁) (hf₂ : Feasible β₂ f₂) :
    jointGrowth2 β₁ β₂ f₁ f₂ ≤
      jointGrowth2 β₁ β₂ (kellyFrac β₁) (kellyFrac β₂) := by
  unfold jointGrowth2
  have h₁ := kelly_optimal β₁ f₁ hf₁
  have h₂ := kelly_optimal β₂ f₂ hf₂
  linarith

/-- **Théorème de Kelly multi-pari à 2 paris (unicité)** : si un des `f_i`
    diffère de `kellyFrac β_i`, la log-croissance jointe est strictement
    inférieure. Suit de `kelly_unique` appliqué à la composante qui diffère
    (l'autre étant dominée par `kelly_optimal` qui donne une inégalité ≤,
    l'addition préserve la stricte inégalité sur la composante différenciante). -/
theorem multiKelly_unique_2 (β₁ β₂ : Bet) (f₁ f₂ : ℝ)
    (hf₁ : Feasible β₁ f₁) (hf₂ : Feasible β₂ f₂)
    (hf₁ne : f₁ ≠ kellyFrac β₁) :
    jointGrowth2 β₁ β₂ f₁ f₂ <
      jointGrowth2 β₁ β₂ (kellyFrac β₁) (kellyFrac β₂) := by
  unfold jointGrowth2
  have h₁ := kelly_unique β₁ f₁ hf₁ hf₁ne
  have h₂ := kelly_optimal β₂ f₂ hf₂
  linarith

/-- **Symétrique** : si `f₂ ≠ kellyFrac β₂`, la log-croissance jointe est
    strictement inférieure. Variante de `multiKelly_unique_2` par symétrie. -/
theorem multiKelly_unique_2' (β₁ β₂ : Bet) (f₁ f₂ : ℝ)
    (hf₁ : Feasible β₁ f₁) (hf₂ : Feasible β₂ f₂)
    (hf₂ne : f₂ ≠ kellyFrac β₂) :
    jointGrowth2 β₁ β₂ f₁ f₂ <
      jointGrowth2 β₁ β₂ (kellyFrac β₁) (kellyFrac β₂) := by
  unfold jointGrowth2
  have h₁ := kelly_optimal β₁ f₁ hf₁
  have h₂ := kelly_unique β₂ f₂ hf₂ hf₂ne
  linarith

end KellyLean
