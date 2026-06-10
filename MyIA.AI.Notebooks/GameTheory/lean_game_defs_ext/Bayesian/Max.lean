/-
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

/-- Maximum of `f` over all of `Fin (n + 1)` (nonempty domain), by
    structural recursion on `n`. -/
def maxFin : (n : Nat) → (Fin (n + 1) → Int) → Int
  | 0, f => f 0
  | n + 1, f => max (f 0) (maxFin n (fun i => f i.succ))

@[simp] theorem maxFin_zero (f : Fin 1 → Int) : maxFin 0 f = f 0 := rfl

@[simp] theorem maxFin_succ (n : Nat) (f : Fin (n + 2) → Int) :
    maxFin (n + 1) f = max (f 0) (maxFin n (fun i => f i.succ)) := rfl

/-- Every value of `f` is at most its maximum. -/
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

/-- The maximum is at most any pointwise upper bound. -/
theorem maxFin_le : ∀ {n : Nat} {f : Fin (n + 1) → Int} {b : Int},
    (∀ i, f i ≤ b) → maxFin n f ≤ b
  | 0, _, _, h => h 0
  | n + 1, f, b, h => by
    have h1 := h 0
    have h2 := maxFin_le (f := fun i => f i.succ) (fun i => h i.succ)
    simp only [maxFin_succ]
    omega

/-- The maximum of the zero function vanishes. -/
@[simp] theorem maxFin_zero_fun (n : Nat) :
    maxFin n (fun _ => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih]

/-- Master lemma: the max of a sum is at most the sum of the groupwise
    maxima. Choosing one action `a` for every group `j` at once cannot
    beat choosing the best action separately inside each group. -/
theorem maxFin_sumFin_le {nA m : Nat} (F : Fin m → Fin (nA + 1) → Int) :
    maxFin nA (fun a => sumFin m (fun j => F j a)) ≤
    sumFin m (fun j => maxFin nA (fun a => F j a)) :=
  maxFin_le (fun a => sumFin_mono (fun j => le_maxFin (F j) a))

/-- An `if` whose condition does not depend on the index pulls out of
    the maximum (the `else 0` branch matches the zero function). -/
theorem maxFin_if_distrib {n : Nat} (c : Prop) [Decidable c]
    (f : Fin (n + 1) → Int) :
    maxFin n (fun a => if c then f a else 0) = if c then maxFin n f else 0 := by
  by_cases h : c <;> simp [h]
