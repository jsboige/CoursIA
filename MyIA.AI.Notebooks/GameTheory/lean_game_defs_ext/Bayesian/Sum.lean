/-
  Finite sums over `Fin n` (core Lean 4 only, no Mathlib)
  =======================================================

  Minimal summation infrastructure for Bayesian game expected utilities.
  Mathlib's `Finset.sum` is not available (core-only project), so we
  define a structural recursion and prove the three lemmas the game
  theory development needs: monotonicity, scalar multiplication, and
  congruence.

  See #2610 (GT-Lean formalization, Bayesian phase 1).
-/

/-- Sum of `f` over all of `Fin n`, by structural recursion on `n`. -/
def sumFin : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => f 0 + sumFin n (fun i => f i.succ)

@[simp] theorem sumFin_zero (f : Fin 0 → Int) : sumFin 0 f = 0 := rfl

@[simp] theorem sumFin_succ (n : Nat) (f : Fin (n + 1) → Int) :
    sumFin (n + 1) f = f 0 + sumFin n (fun i => f i.succ) := rfl

/-- The sum of the zero function vanishes. -/
@[simp] theorem sumFin_zero_fun (n : Nat) :
    sumFin n (fun _ => (0 : Int)) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

/-- Pointwise dominance transfers to the sums. -/
theorem sumFin_mono {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i ≤ g i) :
    sumFin n f ≤ sumFin n g := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sumFin_succ]
    exact Int.add_le_add (h 0) (ih (fun i => h i.succ))

/-- Pointwise equal functions have equal sums. -/
theorem sumFin_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    sumFin n f = sumFin n g := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sumFin_succ]
    rw [h 0, ih (fun i => h i.succ)]

/-- A constant factor distributes out of the sum. -/
theorem sumFin_mul_left {n : Nat} (c : Int) (f : Fin n → Int) :
    sumFin n (fun i => c * f i) = c * sumFin n f := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sumFin_succ]
    rw [ih, Int.mul_add]
