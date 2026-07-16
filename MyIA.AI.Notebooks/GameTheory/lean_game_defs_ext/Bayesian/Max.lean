/-
  Maxima finis sur `Fin (n + 1)` (Lean 4 core seul, sans Mathlib)
  ===============================================================

  Maximum d'une fonction à valeurs dans `Int` sur un domaine fini non
  vide, miroir de l'infrastructure `sumFin` de `Sum.lean`. Le résultat
  clé pour le développement valeur-de-l'information (`Information.lean`)
  est `maxFin_sumFin_le` : le max d'une somme est au plus la somme des
  max par groupe — adapter une décision à chaque groupe séparément ne
  peut qu'améliorer le choix d'une seule action pour tous les groupes.

  Voir #2610 (formalisation GT-Lean, phase bayésienne 4).

  ---
  English:
  Finite maxima over `Fin (n + 1)` (core Lean 4 only, no Mathlib)
  ===============================================================

  Maximum of an `Int`-valued function over a nonempty finite domain,
  mirroring the `sumFin` infrastructure of `Sum.lean`. The key result
  for the value-of-information development (`Information.lean`) is
  `maxFin_sumFin_le`: the max of a sum is at most the sum of the
  groupwise maxima — adapting a decision to each group separately can
  only improve on choosing one action for all groups at once.

  See #2610 (GT-Lean formalization, Bayesian phase 4).
-/

import Bayesian.Sum

/-- Maximum de `f` sur tout `Fin (n + 1)` (domaine non vide), par
    English: Maximum of `f` over all of `Fin (n + 1)` (nonempty domain), by
    structural recursion on `n`. -/
def maxFin : (n : Nat) → (Fin (n + 1) → Int) → Int
  | 0, f => f 0
  | n + 1, f => max (f 0) (maxFin n (fun i => f i.succ))

@[simp] theorem maxFin_zero (f : Fin 1 → Int) : maxFin 0 f = f 0 := rfl

@[simp] theorem maxFin_succ (n : Nat) (f : Fin (n + 2) → Int) :
    maxFin (n + 1) f = max (f 0) (maxFin n (fun i => f i.succ)) := rfl

/-- Toute valeur de `f` est au plus égale à son maximum.
    English: Every value of `f` is at most its maximum. -/
theorem le_maxFin : ∀ {n : Nat} (f : Fin (n + 1) → Int) (i : Fin (n + 1)),
    f i ≤ maxFin n f
  | 0, f, i => by
    cases i using Fin.cases with
    | zero => exact Int.le_refl _
    | succ j => exact j.elim0
  | n + 1, f, i => by
    cases i using Fin.cases with
    | zero =>
      simp only [maxFin_succ]
      omega
    | succ j =>
      have h := le_maxFin (fun i => f i.succ) j
      simp only [maxFin_succ]
      omega

/-- Le maximum est au plus n'importe quelle borne supérieure ponctuelle.
    English: The maximum is at most any pointwise upper bound. -/
theorem maxFin_le : ∀ {n : Nat} {f : Fin (n + 1) → Int} {b : Int},
    (∀ i, f i ≤ b) → maxFin n f ≤ b
  | 0, _, _, h => h 0
  | n + 1, f, b, h => by
    have h1 := h 0
    have h2 := maxFin_le (f := fun i => f i.succ) (fun i => h i.succ)
    simp only [maxFin_succ]
    omega

/-- Le maximum de la fonction nulle s'annule.
    English: The maximum of the zero function vanishes. -/
@[simp] theorem maxFin_zero_fun (n : Nat) :
    maxFin n (fun _ => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

/-- Lemme maître : le max d'une somme est au plus la somme des max par
    groupe. Choisir une seule action `a` pour tous les groupes `j` d'un coup
    ne bat pas le choix de la meilleure action séparément dans chaque groupe.
    English: Master lemma: the max of a sum is at most the sum of the groupwise
    maxima. Choosing one action `a` for every group `j` at once cannot
    beat choosing the best action separately inside each group. -/
theorem maxFin_sumFin_le {nA m : Nat} (F : Fin m → Fin (nA + 1) → Int) :
    maxFin nA (fun a => sumFin m (fun j => F j a)) ≤
    sumFin m (fun j => maxFin nA (fun a => F j a)) :=
  maxFin_le (fun a => sumFin_mono (fun j => le_maxFin (F j) a))

/-- Un `if` dont la condition ne dépend pas de l'indice se factorise hors
    du maximum (la branche `else 0` correspond à la fonction nulle).
    English: An `if` whose condition does not depend on the index pulls out of
    the maximum (the `else 0` branch matches the zero function). -/
theorem maxFin_if_distrib {n : Nat} (c : Prop) [Decidable c]
    (f : Fin (n + 1) → Int) :
    maxFin n (fun a => if c then f a else 0) = if c then maxFin n f else 0 := by
  by_cases h : c <;> simp [h]

/-! ## Argmax fini — l'indice atteignant le maximum

`maxFin` donne la *valeur* du maximum ; `argmaxFin` donne son *témoin* (un indice
qui l'atteint). Ce témoin manquait jusqu'ici : le module de fictitious play
(`FictitiousPlay.lean`, phase 7) calcule le paiement de la meilleure réponse via
`maxFin` mais défère l'extraction de l'indice argmax. `argmaxFin` comble ce gap
de manière *born-correct* : sur un domaine non vide `Fin (n + 1)`, il renvoie
toujours un indice (jamais d'échec), avec une garantie d'optimalité. En cas
d'égalité, le plus petit indice l'emporte.

English:
Finite argmax — the index achieving the maximum

`maxFin` gives the *value* of the maximum; `argmaxFin` gives its *witness* (an
index that attains it). This witness was missing until now: the fictitious play
module (`FictitiousPlay.lean`, phase 7) computes the best-response payoff via
`maxFin` but defers extracting the argmax index. `argmaxFin` fills this gap in a
*born-correct* way: over a nonempty domain `Fin (n + 1)` it always returns an
index (never fails), with an optimality guarantee. Ties break to the smaller
index. -/

/-- Indice atteignant le maximum de `f` sur `Fin (n + 1)` (domaine non vide),
    miroir argmax de `maxFin`. En cas d'égalité, le plus petit indice l'emporte.
    English: Index achieving the maximum of `f` over `Fin (n + 1)` (nonempty
    domain), the argmax mirror of `maxFin`. Ties break to the smaller index. -/
def argmaxFin : (n : Nat) → (Fin (n + 1) → Int) → Fin (n + 1)
  | 0, _ => 0
  | n + 1, f =>
    if f 0 ≥ f (argmaxFin n (fun i => f i.succ)).succ
    then 0
    else (argmaxFin n (fun i => f i.succ)).succ

/-- L'argmax atteint bien le maximum : `f (argmaxFin n f) = maxFin n f`.
    English: The argmax does achieve the maximum: `f (argmaxFin n f) = maxFin n f`. -/
theorem argmaxFin_spec : ∀ {n : Nat} (f : Fin (n + 1) → Int),
    f (argmaxFin n f) = maxFin n f
  | 0, _ => rfl
  | n + 1, f => by
    have ih : f (argmaxFin n (fun i => f i.succ)).succ
        = maxFin n (fun i => f i.succ) := argmaxFin_spec (fun i => f i.succ)
    simp only [argmaxFin, maxFin_succ]
    split <;> rename_i h <;> omega

/-- Garantie d'optimalité de l'argmax : aucune valeur ne dépasse celle de
    l'indice choisi.
    English: Optimality guarantee of the argmax: no value exceeds that of the
    chosen index. -/
theorem le_argmaxFin {n : Nat} (f : Fin (n + 1) → Int) (i : Fin (n + 1)) :
    f i ≤ f (argmaxFin n f) := by
  rw [argmaxFin_spec f]
  exact le_maxFin f i
