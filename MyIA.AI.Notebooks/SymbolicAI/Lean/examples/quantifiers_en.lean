/-
  Lean Examples - Quantifiers (EN sibling)

  This file contains first-order logic examples
  corresponding to the Lean-4 notebook.

  English sibling of quantifiers.lean (i18n #4980): docstrings and
  comments translated to English; theorems, definitions, tactics, and
  variables are byte-identical to the French original.
-/

-- ============================================================
-- Universal quantifier (forall)
-- ============================================================

-- Adding zero on the right
theorem add_zero_right (n : Nat) : n + 0 = n := rfl

-- Commutativity of addition
theorem add_comm_nat (a b : Nat) : a + b = b + a :=
  Nat.add_comm a b

-- Associativity of addition
theorem add_assoc_nat (a b c : Nat) : (a + b) + c = a + (b + c) :=
  Nat.add_assoc a b c

-- ============================================================
-- Existential quantifier (exists)
-- ============================================================

-- There exists an even number
theorem exists_even : exists n : Nat, 2 * n = n + n :=
  Exists.intro 1 rfl

-- There exists a number > 5
theorem exists_gt_5 : exists n : Nat, n > 5 :=
  Exists.intro 6 (Nat.lt_succ_self 5)

-- There exists a number whose square is 4
theorem exists_square_4 : exists n : Nat, n * n = 4 :=
  Exists.intro 2 rfl

-- ============================================================
-- forall/exists interaction
-- ============================================================

variable (A : Type) (P Q : A -> Prop)

-- forall distributes over And
theorem forall_and_distrib :
  (forall x : A, P x /\ Q x) <-> (forall x : A, P x) /\ (forall x : A, Q x) :=
  Iff.intro
    (fun h => And.intro (fun x => (h x).left) (fun x => (h x).right))
    (fun h x => And.intro (h.left x) (h.right x))

-- exists distributes over Or
theorem exists_or_distrib :
  (exists x : A, P x \/ Q x) <-> (exists x : A, P x) \/ (exists x : A, Q x) :=
  Iff.intro
    (fun h => match h with
      | Exists.intro x (Or.inl hp) => Or.inl (Exists.intro x hp)
      | Exists.intro x (Or.inr hq) => Or.inr (Exists.intro x hq))
    (fun h => match h with
      | Or.inl (Exists.intro x hp) => Exists.intro x (Or.inl hp)
      | Or.inr (Exists.intro x hq) => Exists.intro x (Or.inr hq))

-- Negation of exists = forall not
theorem not_exists_iff :
  (Not (exists x : A, P x)) <-> (forall x : A, Not (P x)) :=
  Iff.intro
    (fun h x hp => h (Exists.intro x hp))
    (fun h he => match he with | Exists.intro x hp => h x hp)

-- ============================================================
-- Divisibility
-- ============================================================

-- Definition of divisibility
def divides (a b : Nat) : Prop := exists k : Nat, b = a * k

notation:50 a " | " b => divides a b

-- Every number divides 0
theorem divides_zero (a : Nat) : a | 0 :=
  Exists.intro 0 (Nat.mul_zero a).symm

-- 1 divides every number
theorem one_divides (a : Nat) : 1 | a :=
  Exists.intro a (Nat.one_mul a).symm

-- Reflexivity of divisibility
theorem divides_refl (a : Nat) : a | a :=
  Exists.intro 1 (Nat.mul_one a).symm

-- Transitivity of divisibility
theorem divides_trans (a b c : Nat) (hab : a | b) (hbc : b | c) : a | c :=
  match hab, hbc with
  | Exists.intro k1 hk1, Exists.intro k2 hk2 =>
    Exists.intro (k1 * k2) (calc
      c = b * k2 := hk2
      _ = (a * k1) * k2 := congrArg (. * k2) hk1
      _ = a * (k1 * k2) := Nat.mul_assoc a k1 k2)
