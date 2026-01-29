/-
  Sen's Liberal Paradox
  =====================

  Port of asouther4/lean-social-choice to Lean 4

  Sen's impossibility theorem shows that no social decision procedure
  can simultaneously satisfy:
  1. Weak Pareto criterion
  2. Minimal liberalism (some individuals are decisive over some pairs)
  3. Unrestricted domain

  This is a fundamental result showing tension between efficiency and liberty.
-/

import SocialChoice.Basic
import SocialChoice.Arrow
import Mathlib.Tactic

variable {ι : Type*} {σ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq σ]

/-! ## Minimal Liberalism -/

/-- Individual i is decisive over the pair (x, y):
    If i strictly prefers x to y, society does too -/
def is_decisive_over (f : SWF ι σ) (i : ι) (x y : σ) : Prop :=
  ∀ P : Profile ι σ, P (P i).rel x y → P (f P).rel x y

/-- Minimal liberalism: At least two individuals each have at least one
    pair over which they are decisive -/
def minimal_liberal (f : SWF ι σ) (X : Finset σ) : Prop :=
  ∃ i j : ι, i ≠ j ∧
    (∃ x y : σ, x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ is_decisive_over f i x y) ∧
    (∃ x y : σ, x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ is_decisive_over f j x y)

/-- Unrestricted domain: The SWF accepts any profile -/
-- (This is implicit in our definition of SWF)

/-! ## Sen's Paradox Construction -/

/-- A preference profile that demonstrates the paradox -/
-- Consider: Prude prefers (not-read, not-read) > (read-by-other, not-read) > (read, read-by-other)
--           Lewd prefers (read-by-other, read) > (read, not-read) > (not-read, not-read)

/-! ## Sen's Impossibility Theorem -/

/--
Sen's Liberal Paradox:
There exists no social welfare function that satisfies both
Weak Pareto and Minimal Liberalism for all preference profiles.
-/
theorem sen_impossibility (f : SWF ι σ) (X : Finset σ)
    (hne : (2 : ℕ) ≤ Fintype.card ι)
    (hX : 3 ≤ X.card)
    (hwp : weak_pareto f X)
    (hml : minimal_liberal f X) :
    ∃ P : Profile ι σ, ¬∃ best : σ, is_best_element best X (f P).rel := by
  -- The proof constructs a preference cycle using liberal rights
  -- and Pareto to show that no element can be best
  sorry

/-! ## Example: The Book Reading Paradox -/

/-- Classic example with Prude (p) and Lewd (l) choosing who reads a book
    Alternatives: np (no one reads), pr (prude reads), lr (lewd reads) -/

-- The paradox arises because:
-- 1. Prude is decisive over (pr, lr): prefers not to read if Lewd reads
-- 2. Lewd is decisive over (np, lr): prefers to read rather than no one
-- 3. Both agree (Pareto): (np, pr) - better if Prude reads than no one
--
-- This creates a cycle: np > pr (Pareto), pr > lr (Prude), lr > np (Lewd)
-- No social choice function can break this cycle

theorem book_paradox_demonstrates_sen
    (prude lewd : ι) (hne : prude ≠ lewd)
    (np pr lr : σ) (hdist : np ≠ pr ∧ pr ≠ lr ∧ np ≠ lr)
    (f : SWF ι σ) (X : Finset σ)
    (hX : X = {np, pr, lr})
    (hwp : weak_pareto f X)
    (hprude : is_decisive_over f prude pr lr)
    (hlewd : is_decisive_over f lewd np lr) :
    ∃ P : Profile ι σ,
      -- Prude prefers pr > lr (exercises right)
      -- Lewd prefers lr > np (exercises right)
      -- Both prefer np > pr (Pareto condition)
      -- Result: Society has cycle np > pr > lr > np
      (P (f P).rel np pr) ∧ (P (f P).rel pr lr) ∧ (P (f P).rel lr np) := by
  sorry

/-! ## Resolution Approaches -/

-- Sen's paradox has led to various resolution approaches:
-- 1. Restricting the domain (not all profiles allowed)
-- 2. Weakening Pareto (conditional Pareto)
-- 3. Weakening liberalism (conditional liberalism)
-- 4. Procedural approaches (rights as game forms)

-- The paradox remains philosophically important as it shows
-- a fundamental tension between efficiency and individual rights.

end
