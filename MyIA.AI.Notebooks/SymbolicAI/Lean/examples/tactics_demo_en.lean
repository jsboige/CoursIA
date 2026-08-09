/-
  Lean Examples - Tactics Mode (EN sibling)

  This file demonstrates Lean's tactic mode
  corresponding to the Lean-5 notebook.

  English sibling of tactics_demo.lean (i18n #4980): docstrings and
  comments translated to English; theorems, definitions, tactics, and
  variables are byte-identical to the French original.
-/

-- ============================================================
-- Basic tactics
-- ============================================================

-- exact : provide the exact term
theorem exact_demo (p : Prop) (hp : p) : p := by
  exact hp

-- intro : introduce hypotheses
theorem intro_demo (p q : Prop) : p -> q -> p := by
  intro hp hq
  exact hp

-- apply : apply a lemma
theorem apply_demo (p q r : Prop) (hpq : p -> q) (hqr : q -> r) (hp : p) : r := by
  apply hqr
  apply hpq
  exact hp

-- assumption : search the context
theorem assumption_demo (p q : Prop) (hp : p) (hq : q) : p := by
  assumption

-- ============================================================
-- Context management
-- ============================================================

-- have : intermediate lemma
theorem have_demo (p q r : Prop) (hpq : p -> q) (hqr : q -> r) (hp : p) : r := by
  have hq : q := hpq hp
  have hr : r := hqr hq
  exact hr

-- show : annotate the goal
theorem show_demo (p q : Prop) (hp : p) (hq : q) : q /\ p := by
  constructor
  show q
  exact hq
  show p
  exact hp

-- ============================================================
-- Tactics for logic
-- ============================================================

-- constructor for And
theorem and_tactic (p q : Prop) (hp : p) (hq : q) : p /\ q := by
  constructor
  . exact hp
  . exact hq

-- cases for Or
theorem or_tactic (p q r : Prop) (hpq : p \/ q) (hpr : p -> r) (hqr : q -> r) : r := by
  cases hpq with
  | inl hp => exact hpr hp
  | inr hq => exact hqr hq

-- left and right for Or
theorem left_right_demo (p q : Prop) (hp : p) : p \/ q := by
  left
  exact hp

-- contradiction
theorem contradiction_demo (p q : Prop) (hp : p) (hnp : Not p) : q := by
  contradiction

-- ============================================================
-- Rewriting and simplification
-- ============================================================

-- rw : rewriting
theorem rw_demo (a b c : Nat) (h : a = b) : a + c = b + c := by
  rw [h]

-- rw with multiple lemmas
theorem rw_chain (a b c d : Nat) (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by
  rw [h1, h2, h3]

-- simp : automatic simplification
theorem simp_demo (n : Nat) : n + 0 = n := by
  simp

-- simp with additional lemmas
theorem simp_with (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  simp [h]

-- ============================================================
-- Automatic tactics
-- ============================================================

-- omega : Presburger arithmetic
theorem omega_demo (n m : Nat) (h : n < m) : n + 1 <= m := by
  omega

-- decide : decidable propositions
theorem decide_demo : 3 < 5 := by
  decide

-- ============================================================
-- Structuring proofs
-- ============================================================

-- Bullets for focusing
theorem bullets_demo (p q r : Prop) (hp : p) (hq : q) (hr : r) : p /\ q /\ r := by
  constructor
  . exact hp
  . constructor
    . exact hq
    . exact hr

-- <;> to apply to all goals
theorem all_goals_demo (p : Prop) (hp : p) : p /\ p := by
  constructor <;> exact hp

-- ============================================================
-- Induction
-- ============================================================

-- Recurrence over Nat
theorem induction_demo (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [Nat.add_succ, ih]
